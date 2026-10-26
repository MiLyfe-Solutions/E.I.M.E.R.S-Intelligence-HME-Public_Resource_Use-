import V185TrunkScan22Chunk072

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_655221 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_655221 : Nat := 118140960795 + 655221 * 2 ^ 59
def prefixEnd_655221 : Nat := 4983230072969 + 3 ^ 40 * 655221 * 2
def baseEnd_655221 : Nat := 224295538613124119016133

theorem tailTrace_655221 : CollatzResearch.WordTrace tailWord_655221 prefixEnd_655221 224295538613124119016133 := by
  unfold tailWord_655221
  simp only [CollatzResearch.WordTrace]
  refine ⟨23897873159253694682869517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15931915439502463121913011 23897873159253694682869517)
  ·
    refine ⟨8961702434720135506076069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23897873159253694682869517 8961702434720135506076069)
    ·
      refine ⟨1680319206510025407389263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8961702434720135506076069 1680319206510025407389263)
      ·
        refine ⟨2520478809765038111083895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680319206510025407389263 2520478809765038111083895)
        ·
          refine ⟨3780718214647557166625843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520478809765038111083895 3780718214647557166625843)
          ·
            refine ⟨5671077321971335749938765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780718214647557166625843 5671077321971335749938765)
            ·
              refine ⟨2126653995739250906227037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5671077321971335749938765 2126653995739250906227037)
              ·
                refine ⟨797495248402219089835139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2126653995739250906227037 797495248402219089835139)
                ·
                  refine ⟨1196242872603328634752709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797495248402219089835139 1196242872603328634752709)
                  ·
                    refine ⟨224295538613124119016133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1196242872603328634752709 224295538613124119016133)
                    ·
                      rfl

theorem cell22_655221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_655221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655221 prefixEnd_655221 := by exact prefixLift 655221
  have htrace : WordTrace (prefixWord ++ tailWord_655221) baseStart_655221 baseEnd_655221 := by
    simpa [prefixWord, tailWord_655221, baseEnd_655221] using wordTrace_append hprefix tailTrace_655221
  have hstable : (prefixWord ++ tailWord_655221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655221).length < 2 ^ (prefixWord ++ tailWord_655221).sum := by decide
  have hdescent : baseEnd_655221 < baseStart_655221 := by decide
  rcases family_descends (prefixWord ++ tailWord_655221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655236 : List Nat := [2, 3, 2, 1, 1, 1, 4, 4, 4]
def baseStart_655236 : Nat := 118140960795 + 655236 * 2 ^ 59
def prefixEnd_655236 : Nat := 4983230072969 + 3 ^ 40 * 655236 * 2
def baseEnd_655236 : Nat := 74766891139889693297029

theorem tailTrace_655236 : CollatzResearch.WordTrace tailWord_655236 prefixEnd_655236 74766891139889693297029 := by
  unfold tailWord_655236
  simp only [CollatzResearch.WordTrace]
  refine ⟨11949210127099676122332781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15932280169466234829777041 11949210127099676122332781)
  ·
    refine ⟨4480953797662378545874793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11949210127099676122332781 4480953797662378545874793)
    ·
      refine ⟨3360715348246783909406095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4480953797662378545874793 3360715348246783909406095)
      ·
        refine ⟨5041073022370175864109143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360715348246783909406095 5041073022370175864109143)
        ·
          refine ⟨7561609533555263796163715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5041073022370175864109143 7561609533555263796163715)
          ·
            refine ⟨11342414300332895694245573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7561609533555263796163715 11342414300332895694245573)
            ·
              refine ⟨2126702681312417942671045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11342414300332895694245573 2126702681312417942671045)
              ·
                refine ⟨398756752746078364250821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2126702681312417942671045 398756752746078364250821)
                ·
                  refine ⟨74766891139889693297029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 398756752746078364250821 74766891139889693297029)
                  ·
                    rfl

theorem cell22_655236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_655236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655236 prefixEnd_655236 := by exact prefixLift 655236
  have htrace : WordTrace (prefixWord ++ tailWord_655236) baseStart_655236 baseEnd_655236 := by
    simpa [prefixWord, tailWord_655236, baseEnd_655236] using wordTrace_append hprefix tailTrace_655236
  have hstable : (prefixWord ++ tailWord_655236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655236).length < 2 ^ (prefixWord ++ tailWord_655236).sum := by decide
  have hdescent : baseEnd_655236 < baseStart_655236 := by decide
  rcases family_descends (prefixWord ++ tailWord_655236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655358 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_655358 : Nat := 118140960795 + 655358 * 2 ^ 59
def prefixEnd_655358 : Nat := 4983230072969 + 3 ^ 40 * 655358 * 2
def baseEnd_655358 : Nat := 224342436512901428340713

theorem tailTrace_655358 : CollatzResearch.WordTrace tailWord_655358 prefixEnd_655358 224342436512901428340713 := by
  unfold tailWord_655358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2987858744969670885075841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15935246639838244720404485 2987858744969670885075841)
  ·
    refine ⟨2240894058727253163806881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2987858744969670885075841 2240894058727253163806881)
    ·
      refine ⟨1680670544045439872855161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2240894058727253163806881 1680670544045439872855161)
      ·
        refine ⟨1260502908034079904641371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1680670544045439872855161 1260502908034079904641371)
        ·
          refine ⟨1890754362051119856962057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1260502908034079904641371 1890754362051119856962057)
          ·
            refine ⟨1418065771538339892721543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1890754362051119856962057 1418065771538339892721543)
            ·
              refine ⟨2127098657307509839082315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418065771538339892721543 2127098657307509839082315)
              ·
                refine ⟨3190647985961264758623473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127098657307509839082315 3190647985961264758623473)
                ·
                  refine ⟨2392985989470948568967605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3190647985961264758623473 2392985989470948568967605)
                  ·
                    refine ⟨224342436512901428340713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2392985989470948568967605 224342436512901428340713)
                    ·
                      rfl

theorem cell22_655358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_655358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655358 prefixEnd_655358 := by exact prefixLift 655358
  have htrace : WordTrace (prefixWord ++ tailWord_655358) baseStart_655358 baseEnd_655358 := by
    simpa [prefixWord, tailWord_655358, baseEnd_655358] using wordTrace_append hprefix tailTrace_655358
  have hstable : (prefixWord ++ tailWord_655358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655358).length < 2 ^ (prefixWord ++ tailWord_655358).sum := by decide
  have hdescent : baseEnd_655358 < baseStart_655358 := by decide
  rcases family_descends (prefixWord ++ tailWord_655358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655386 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_655386 : Nat := 118140960795 + 655386 * 2 ^ 59
def prefixEnd_655386 : Nat := 4983230072969 + 3 ^ 40 * 655386 * 2
def baseEnd_655386 : Nat := 224352021485118688640627

theorem tailTrace_655386 : CollatzResearch.WordTrace tailWord_655386 prefixEnd_655386 224352021485118688640627 := by
  unfold tailWord_655386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5975972800913981965656503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15935927469103951908417341 5975972800913981965656503)
  ·
    refine ⟨8963959201370972948484755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5975972800913981965656503 8963959201370972948484755)
    ·
      refine ⟨13445938802056459422727133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8963959201370972948484755 13445938802056459422727133)
      ·
        refine ⟨5042227050771172283522675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13445938802056459422727133 5042227050771172283522675)
        ·
          refine ⟨7563340576156758425284013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5042227050771172283522675 7563340576156758425284013)
          ·
            refine ⟨2836252716058784409481505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7563340576156758425284013 2836252716058784409481505)
            ·
              refine ⟨2127189537044088307111129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836252716058784409481505 2127189537044088307111129)
              ·
                refine ⟨1595392152783066230333347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127189537044088307111129 1595392152783066230333347)
                ·
                  refine ⟨2393088229174599345500021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595392152783066230333347 2393088229174599345500021)
                  ·
                    refine ⟨224352021485118688640627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2393088229174599345500021 224352021485118688640627)
                    ·
                      rfl

theorem cell22_655386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_655386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655386 prefixEnd_655386 := by exact prefixLift 655386
  have htrace : WordTrace (prefixWord ++ tailWord_655386) baseStart_655386 baseEnd_655386 := by
    simpa [prefixWord, tailWord_655386, baseEnd_655386] using wordTrace_append hprefix tailTrace_655386
  have hstable : (prefixWord ++ tailWord_655386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655386).length < 2 ^ (prefixWord ++ tailWord_655386).sum := by decide
  have hdescent : baseEnd_655386 < baseStart_655386 := by decide
  rcases family_descends (prefixWord ++ tailWord_655386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655388 : List Nat := [2, 2, 3, 1, 3, 1, 1, 5, 4]
def baseStart_655388 : Nat := 118140960795 + 655388 * 2 ^ 59
def prefixEnd_655388 : Nat := 4983230072969 + 3 ^ 40 * 655388 * 2
def baseEnd_655388 : Nat := 74784235375330450030207

theorem tailTrace_655388 : CollatzResearch.WordTrace tailWord_655388 prefixEnd_655388 74784235375330450030207 := by
  unfold tailWord_655388
  simp only [CollatzResearch.WordTrace]
  refine ⟨11951982074824341102099409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15935976099765788136132545 11951982074824341102099409)
  ·
    refine ⟨8963986556118255826574557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11951982074824341102099409 8963986556118255826574557)
    ·
      refine ⟨3361494958544345934965459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8963986556118255826574557 3361494958544345934965459)
      ·
        refine ⟨5042242437816518902448189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3361494958544345934965459 5042242437816518902448189)
        ·
          refine ⟨1890840914181194588418071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5042242437816518902448189 1890840914181194588418071)
          ·
            refine ⟨2836261371271791882627107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890840914181194588418071 2836261371271791882627107)
            ·
              refine ⟨4254392056907687823940661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2836261371271791882627107 4254392056907687823940661)
              ·
                refine ⟨398849255335095733494437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4254392056907687823940661 398849255335095733494437)
                ·
                  refine ⟨74784235375330450030207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 398849255335095733494437 74784235375330450030207)
                  ·
                    rfl

theorem cell22_655388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_655388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655388 prefixEnd_655388 := by exact prefixLift 655388
  have htrace : WordTrace (prefixWord ++ tailWord_655388) baseStart_655388 baseEnd_655388 := by
    simpa [prefixWord, tailWord_655388, baseEnd_655388] using wordTrace_append hprefix tailTrace_655388
  have hstable : (prefixWord ++ tailWord_655388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655388).length < 2 ^ (prefixWord ++ tailWord_655388).sum := by decide
  have hdescent : baseEnd_655388 < baseStart_655388 := by decide
  rcases family_descends (prefixWord ++ tailWord_655388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655420 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 2, 3]
def baseStart_655420 : Nat := 118140960795 + 655420 * 2 ^ 59
def prefixEnd_655420 : Nat := 4983230072969 + 3 ^ 40 * 655420 * 2
def baseEnd_655420 : Nat := 224363660379953933290523

theorem tailTrace_655420 : CollatzResearch.WordTrace tailWord_655420 prefixEnd_655420 224363660379953933290523 := by
  unfold tailWord_655420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11952565642766375834681857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15936754190355167779575809 11952565642766375834681857)
  ·
    refine ⟨8964424232074781876011393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11952565642766375834681857 8964424232074781876011393)
    ·
      refine ⟨6723318174056086407008545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8964424232074781876011393 6723318174056086407008545)
      ·
        refine ⟨5042488630542064805256409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6723318174056086407008545 5042488630542064805256409)
        ·
          refine ⟨3781866472906548603942307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5042488630542064805256409 3781866472906548603942307)
          ·
            refine ⟨5672799709359822905913461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3781866472906548603942307 5672799709359822905913461)
            ·
              refine ⟨531824972752483397429387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5672799709359822905913461 531824972752483397429387)
              ·
                refine ⟨797737459128725096144081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531824972752483397429387 797737459128725096144081)
                ·
                  refine ⟨598303094346543822108061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 797737459128725096144081 598303094346543822108061)
                  ·
                    refine ⟨224363660379953933290523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 598303094346543822108061 224363660379953933290523)
                    ·
                      rfl

theorem cell22_655420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_655420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655420 prefixEnd_655420 := by exact prefixLift 655420
  have htrace : WordTrace (prefixWord ++ tailWord_655420) baseStart_655420 baseEnd_655420 := by
    simpa [prefixWord, tailWord_655420, baseEnd_655420] using wordTrace_append hprefix tailTrace_655420
  have hstable : (prefixWord ++ tailWord_655420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655420).length < 2 ^ (prefixWord ++ tailWord_655420).sum := by decide
  have hdescent : baseEnd_655420 < baseStart_655420 := by decide
  rcases family_descends (prefixWord ++ tailWord_655420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655461 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 7]
def baseStart_655461 : Nat := 118140960795 + 655461 * 2 ^ 59
def prefixEnd_655461 : Nat := 4983230072969 + 3 ^ 40 * 655461 * 2
def baseEnd_655461 : Nat := 74792565172614497671799

theorem tailTrace_655461 : CollatzResearch.WordTrace tailWord_655461 prefixEnd_655461 74792565172614497671799 := by
  unfold tailWord_655461
  simp only [CollatzResearch.WordTrace]
  refine ⟨23906626678384215671606237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15937751118922810447737491 23906626678384215671606237)
  ·
    refine ⟨8964985004394080876852339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23906626678384215671606237 8964985004394080876852339)
    ·
      refine ⟨13447477506591121315278509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8964985004394080876852339 13447477506591121315278509)
      ·
        refine ⟨5042804064971670493229441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13447477506591121315278509 5042804064971670493229441)
        ·
          refine ⟨3782103048728752869922081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5042804064971670493229441 3782103048728752869922081)
          ·
            refine ⟨2836577286546564652441561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3782103048728752869922081 2836577286546564652441561)
            ·
              refine ⟨2127432964909923489331171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836577286546564652441561 2127432964909923489331171)
              ·
                refine ⟨3191149447364885233996757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127432964909923489331171 3191149447364885233996757)
                ·
                  refine ⟨74792565172614497671799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3191149447364885233996757 74792565172614497671799)
                  ·
                    rfl

theorem cell22_655461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_655461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655461 prefixEnd_655461 := by exact prefixLift 655461
  have htrace : WordTrace (prefixWord ++ tailWord_655461) baseStart_655461 baseEnd_655461 := by
    simpa [prefixWord, tailWord_655461, baseEnd_655461] using wordTrace_append hprefix tailTrace_655461
  have hstable : (prefixWord ++ tailWord_655461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655461).length < 2 ^ (prefixWord ++ tailWord_655461).sum := by decide
  have hdescent : baseEnd_655461 < baseStart_655461 := by decide
  rcases family_descends (prefixWord ++ tailWord_655461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655538 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_655538 : Nat := 118140960795 + 655538 * 2 ^ 59
def prefixEnd_655538 : Nat := 4983230072969 + 3 ^ 40 * 655538 * 2
def baseEnd_655538 : Nat := 224404054191440958840161

theorem tailTrace_655538 : CollatzResearch.WordTrace tailWord_655538 prefixEnd_655538 224404054191440958840161 := by
  unfold tailWord_655538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5977358774776314455539817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15939623399403505214772845 5977358774776314455539817)
  ·
    refine ⟨4483019081082235841654863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5977358774776314455539817 4483019081082235841654863)
    ·
      refine ⟨6724528621623353762482295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4483019081082235841654863 6724528621623353762482295)
      ·
        refine ⟨10086792932435030643723443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6724528621623353762482295 10086792932435030643723443)
        ·
          refine ⟨15130189398652545965585165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10086792932435030643723443 15130189398652545965585165)
          ·
            refine ⟨5673821024494704737094437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15130189398652545965585165 5673821024494704737094437)
            ·
              refine ⟨1063841442092757138205207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5673821024494704737094437 1063841442092757138205207)
              ·
                refine ⟨1595762163139135707307811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063841442092757138205207 1595762163139135707307811)
                ·
                  refine ⟨2393643244708703560961717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595762163139135707307811 2393643244708703560961717)
                  ·
                    refine ⟨224404054191440958840161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2393643244708703560961717 224404054191440958840161)
                    ·
                      rfl

theorem cell22_655538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_655538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655538 prefixEnd_655538 := by exact prefixLift 655538
  have htrace : WordTrace (prefixWord ++ tailWord_655538) baseStart_655538 baseEnd_655538 := by
    simpa [prefixWord, tailWord_655538, baseEnd_655538] using wordTrace_append hprefix tailTrace_655538
  have hstable : (prefixWord ++ tailWord_655538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655538).length < 2 ^ (prefixWord ++ tailWord_655538).sum := by decide
  have hdescent : baseEnd_655538 < baseStart_655538 := by decide
  rcases family_descends (prefixWord ++ tailWord_655538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655647 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 5]
def baseStart_655647 : Nat := 118140960795 + 655647 * 2 ^ 59
def prefixEnd_655647 : Nat := 4983230072969 + 3 ^ 40 * 655647 * 2
def baseEnd_655647 : Nat := 74813789039667002621609

theorem tailTrace_655647 : CollatzResearch.WordTrace tailWord_655647 prefixEnd_655647 74813789039667002621609 := by
  unfold tailWord_655647
  simp only [CollatzResearch.WordTrace]
  refine ⟨23913410655710369437877195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15942273770473579625251463 23913410655710369437877195)
  ·
    refine ⟨35870115983565554156815793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23913410655710369437877195 35870115983565554156815793)
    ·
      refine ⟨26902586987674165617611845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35870115983565554156815793 26902586987674165617611845)
      ·
        refine ⟨5044235060188906053302221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26902586987674165617611845 5044235060188906053302221)
        ·
          refine ⟨1891588147570839769988333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5044235060188906053302221 1891588147570839769988333)
          ·
            refine ⟨709345555339064913745625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1891588147570839769988333 709345555339064913745625)
            ·
              refine ⟨532009166504298685309219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709345555339064913745625 532009166504298685309219)
              ·
                refine ⟨798013749756448027963829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532009166504298685309219 798013749756448027963829)
                ·
                  refine ⟨74813789039667002621609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 798013749756448027963829 74813789039667002621609)
                  ·
                    rfl

theorem cell22_655647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 5].length) (baseStart_655647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655647 prefixEnd_655647 := by exact prefixLift 655647
  have htrace : WordTrace (prefixWord ++ tailWord_655647) baseStart_655647 baseEnd_655647 := by
    simpa [prefixWord, tailWord_655647, baseEnd_655647] using wordTrace_append hprefix tailTrace_655647
  have hstable : (prefixWord ++ tailWord_655647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655647).length < 2 ^ (prefixWord ++ tailWord_655647).sum := by decide
  have hdescent : baseEnd_655647 < baseStart_655647 := by decide
  rcases family_descends (prefixWord ++ tailWord_655647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655660 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_655660 : Nat := 118140960795 + 655660 * 2 ^ 59
def prefixEnd_655660 : Nat := 4983230072969 + 3 ^ 40 * 655660 * 2
def baseEnd_655660 : Nat := 224445817284673307289787

theorem tailTrace_655660 : CollatzResearch.WordTrace tailWord_655660 prefixEnd_655660 224445817284673307289787 := by
  unfold tailWord_655660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11956942402331636329050217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15942589869775515105400289 11956942402331636329050217)
  ·
    refine ⟨8967706801748727246787663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11956942402331636329050217 8967706801748727246787663)
    ·
      refine ⟨13451560202623090870181495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8967706801748727246787663 13451560202623090870181495)
      ·
        refine ⟨20177340303934636305272243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13451560202623090870181495 20177340303934636305272243)
        ·
          refine ⟨30266010455901954457908365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20177340303934636305272243 30266010455901954457908365)
          ·
            refine ⟨11349753920963232921715637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30266010455901954457908365 11349753920963232921715637)
            ·
              refine ⟨1064039430090303086410841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11349753920963232921715637 1064039430090303086410841)
              ·
                refine ⟨798029572567727314808131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064039430090303086410841 798029572567727314808131)
                ·
                  refine ⟨1197044358851590972212197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798029572567727314808131 1197044358851590972212197)
                  ·
                    refine ⟨224445817284673307289787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1197044358851590972212197 224445817284673307289787)
                    ·
                      rfl

theorem cell22_655660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_655660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655660 prefixEnd_655660 := by exact prefixLift 655660
  have htrace : WordTrace (prefixWord ++ tailWord_655660) baseStart_655660 baseEnd_655660 := by
    simpa [prefixWord, tailWord_655660, baseEnd_655660] using wordTrace_append hprefix tailTrace_655660
  have hstable : (prefixWord ++ tailWord_655660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655660).length < 2 ^ (prefixWord ++ tailWord_655660).sum := by decide
  have hdescent : baseEnd_655660 < baseStart_655660 := by decide
  rcases family_descends (prefixWord ++ tailWord_655660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655722 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_655722 : Nat := 118140960795 + 655722 * 2 ^ 59
def prefixEnd_655722 : Nat := 4983230072969 + 3 ^ 40 * 655722 * 2
def baseEnd_655722 : Nat := 224467041151725812239597

theorem tailTrace_655722 : CollatzResearch.WordTrace tailWord_655722 prefixEnd_655722 224467041151725812239597 := by
  unfold tailWord_655722
  simp only [CollatzResearch.WordTrace]
  refine ⟨5979036532609664311714355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15944097420292438164571613 5979036532609664311714355)
  ·
    refine ⟨8968554798914496467571533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5979036532609664311714355 8968554798914496467571533)
    ·
      refine ⟨3363208049592936175339325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8968554798914496467571533 3363208049592936175339325)
      ·
        refine ⟨1261203018597351065752247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3363208049592936175339325 1261203018597351065752247)
        ·
          refine ⟨1891804527896026598628371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261203018597351065752247 1891804527896026598628371)
          ·
            refine ⟨2837706791844039897942557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891804527896026598628371 2837706791844039897942557)
            ·
              refine ⟨1064140046941514961728459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2837706791844039897942557 1064140046941514961728459)
              ·
                refine ⟨1596210070412272442592689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064140046941514961728459 1596210070412272442592689)
                ·
                  refine ⟨1197157552809204331944517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1596210070412272442592689 1197157552809204331944517)
                  ·
                    refine ⟨224467041151725812239597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1197157552809204331944517 224467041151725812239597)
                    ·
                      rfl

theorem cell22_655722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_655722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655722 prefixEnd_655722 := by exact prefixLift 655722
  have htrace : WordTrace (prefixWord ++ tailWord_655722) baseStart_655722 baseEnd_655722 := by
    simpa [prefixWord, tailWord_655722, baseEnd_655722] using wordTrace_append hprefix tailTrace_655722
  have hstable : (prefixWord ++ tailWord_655722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655722).length < 2 ^ (prefixWord ++ tailWord_655722).sum := by decide
  have hdescent : baseEnd_655722 < baseStart_655722 := by decide
  rcases family_descends (prefixWord ++ tailWord_655722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655752 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 3, 3]
def baseStart_655752 : Nat := 118140960795 + 655752 * 2 ^ 59
def prefixEnd_655752 : Nat := 4983230072969 + 3 ^ 40 * 655752 * 2
def baseEnd_655752 : Nat := 224477310764815733989505

theorem tailTrace_655752 : CollatzResearch.WordTrace tailWord_655752 prefixEnd_655752 224477310764815733989505 := by
  unfold tailWord_655752
  simp only [CollatzResearch.WordTrace]
  refine ⟨11958620160164986185224755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15944826880219981580299673 11958620160164986185224755)
  ·
    refine ⟨17937930240247479277837133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11958620160164986185224755 17937930240247479277837133)
    ·
      refine ⟨6726723840092804729188925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17937930240247479277837133 6726723840092804729188925)
      ·
        refine ⟨2522521440034801773445847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6726723840092804729188925 2522521440034801773445847)
        ·
          refine ⟨3783782160052202660168771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522521440034801773445847 3783782160052202660168771)
          ·
            refine ⟨5675673240078303990253157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783782160052202660168771 5675673240078303990253157)
            ·
              refine ⟨1064188732514681998172467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5675673240078303990253157 1064188732514681998172467)
              ·
                refine ⟨1596283098772022997258701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064188732514681998172467 1596283098772022997258701)
                ·
                  refine ⟨598606162039508623972013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1596283098772022997258701 598606162039508623972013)
                  ·
                    refine ⟨224477310764815733989505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 598606162039508623972013 224477310764815733989505)
                    ·
                      rfl

theorem cell22_655752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_655752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655752 prefixEnd_655752 := by exact prefixLift 655752
  have htrace : WordTrace (prefixWord ++ tailWord_655752) baseStart_655752 baseEnd_655752 := by
    simpa [prefixWord, tailWord_655752, baseEnd_655752] using wordTrace_append hprefix tailTrace_655752
  have hstable : (prefixWord ++ tailWord_655752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655752).length < 2 ^ (prefixWord ++ tailWord_655752).sum := by decide
  have hdescent : baseEnd_655752 < baseStart_655752 := by decide
  rcases family_descends (prefixWord ++ tailWord_655752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655829 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 1, 4]
def baseStart_655829 : Nat := 118140960795 + 655829 * 2 ^ 59
def prefixEnd_655829 : Nat := 4983230072969 + 3 ^ 40 * 655829 * 2
def baseEnd_655829 : Nat := 224503669438413199814269

theorem tailTrace_655829 : CollatzResearch.WordTrace tailWord_655829 prefixEnd_655829 224503669438413199814269 := by
  unfold tailWord_655829
  simp only [CollatzResearch.WordTrace]
  refine ⟨23920048741051014521002541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15946699160700676347335027 23920048741051014521002541)
  ·
    refine ⟨8970018277894130445375953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23920048741051014521002541 8970018277894130445375953)
    ·
      refine ⟨6727513708420597834031965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8970018277894130445375953 6727513708420597834031965)
      ·
        refine ⟨2522817640657724187761987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6727513708420597834031965 2522817640657724187761987)
        ·
          refine ⟨3784226460986586281642981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522817640657724187761987 3784226460986586281642981)
          ·
            refine ⟨709542461434984927808059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3784226460986586281642981 709542461434984927808059)
            ·
              refine ⟨1064313692152477391712089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709542461434984927808059 1064313692152477391712089)
              ·
                refine ⟨798235269114358043784067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064313692152477391712089 798235269114358043784067)
                ·
                  refine ⟨1197352903671537065676101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798235269114358043784067 1197352903671537065676101)
                  ·
                    refine ⟨224503669438413199814269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1197352903671537065676101 224503669438413199814269)
                    ·
                      rfl

theorem cell22_655829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_655829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655829 prefixEnd_655829 := by exact prefixLift 655829
  have htrace : WordTrace (prefixWord ++ tailWord_655829) baseStart_655829 baseEnd_655829 := by
    simpa [prefixWord, tailWord_655829, baseEnd_655829] using wordTrace_append hprefix tailTrace_655829
  have hstable : (prefixWord ++ tailWord_655829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655829).length < 2 ^ (prefixWord ++ tailWord_655829).sum := by decide
  have hdescent : baseEnd_655829 < baseStart_655829 := by decide
  rcases family_descends (prefixWord ++ tailWord_655829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655861 : List Nat := [1, 3, 5, 1, 2, 1, 1, 4, 4]
def baseStart_655861 : Nat := 118140960795 + 655861 * 2 ^ 59
def prefixEnd_655861 : Nat := 4983230072969 + 3 ^ 40 * 655861 * 2
def baseEnd_655861 : Nat := 74838207897458594338057

theorem tailTrace_655861 : CollatzResearch.WordTrace tailWord_655861 prefixEnd_655861 74838207897458594338057 := by
  unfold tailWord_655861
  simp only [CollatzResearch.WordTrace]
  refine ⟨23921215876935083986167437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15947477251290055990778291 23921215876935083986167437)
  ·
    refine ⟨8970455953850656494812789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23921215876935083986167437 8970455953850656494812789)
    ·
      refine ⟨840980245673499046388699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8970455953850656494812789 840980245673499046388699)
      ·
        refine ⟨1261470368510248569583049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840980245673499046388699 1261470368510248569583049)
        ·
          refine ⟨946102776382686427187287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1261470368510248569583049 946102776382686427187287)
          ·
            refine ⟨1419154164574029640780931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946102776382686427187287 1419154164574029640780931)
            ·
              refine ⟨2128731246861044461171397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419154164574029640780931 2128731246861044461171397)
              ·
                refine ⟨399137108786445836469637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2128731246861044461171397 399137108786445836469637)
                ·
                  refine ⟨74838207897458594338057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 399137108786445836469637 74838207897458594338057)
                  ·
                    rfl

theorem cell22_655861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_655861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655861 prefixEnd_655861 := by exact prefixLift 655861
  have htrace : WordTrace (prefixWord ++ tailWord_655861) baseStart_655861 baseEnd_655861 := by
    simpa [prefixWord, tailWord_655861, baseEnd_655861] using wordTrace_append hprefix tailTrace_655861
  have hstable : (prefixWord ++ tailWord_655861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655861).length < 2 ^ (prefixWord ++ tailWord_655861).sum := by decide
  have hdescent : baseEnd_655861 < baseStart_655861 := by decide
  rcases family_descends (prefixWord ++ tailWord_655861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655932 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_655932 : Nat := 118140960795 + 655932 * 2 ^ 59
def prefixEnd_655932 : Nat := 4983230072969 + 3 ^ 40 * 655932 * 2
def baseEnd_655932 : Nat := 224538928443355264488953

theorem tailTrace_655932 : CollatzResearch.WordTrace tailWord_655932 prefixEnd_655932 224538928443355264488953 := by
  unfold tailWord_655932
  simp only [CollatzResearch.WordTrace]
  refine ⟨11961902729838931556001025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15949203639785242074668033 11961902729838931556001025)
  ·
    refine ⟨8971427047379198667000769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11961902729838931556001025 8971427047379198667000769)
    ·
      refine ⟨6728570285534399000250577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8971427047379198667000769 6728570285534399000250577)
      ·
        refine ⟨5046427714150799250187933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6728570285534399000250577 5046427714150799250187933)
        ·
          refine ⟨1892410392806549718820475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5046427714150799250187933 1892410392806549718820475)
          ·
            refine ⟨2838615589209824578230713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892410392806549718820475 2838615589209824578230713)
            ·
              refine ⟨2128961691907368433673035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2838615589209824578230713 2128961691907368433673035)
              ·
                refine ⟨3193442537861052650509553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2128961691907368433673035 3193442537861052650509553)
                ·
                  refine ⟨2395081903395789487882165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3193442537861052650509553 2395081903395789487882165)
                  ·
                    refine ⟨224538928443355264488953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2395081903395789487882165 224538928443355264488953)
                    ·
                      rfl

theorem cell22_655932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_655932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655932 prefixEnd_655932 := by exact prefixLift 655932
  have htrace : WordTrace (prefixWord ++ tailWord_655932) baseStart_655932 baseEnd_655932 := by
    simpa [prefixWord, tailWord_655932, baseEnd_655932] using wordTrace_append hprefix tailTrace_655932
  have hstable : (prefixWord ++ tailWord_655932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655932).length < 2 ^ (prefixWord ++ tailWord_655932).sum := by decide
  have hdescent : baseEnd_655932 < baseStart_655932 := by decide
  rcases family_descends (prefixWord ++ tailWord_655932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655940 : List Nat := [2, 3, 5, 1, 2, 1, 2, 6]
def baseStart_655940 : Nat := 118140960795 + 655940 * 2 ^ 59
def prefixEnd_655940 : Nat := 4983230072969 + 3 ^ 40 * 655940 * 2
def baseEnd_655940 : Nat := 24949074111871767809881

theorem tailTrace_655940 : CollatzResearch.WordTrace tailWord_655940 prefixEnd_655940 24949074111871767809881 := by
  unfold tailWord_655940
  simp only [CollatzResearch.WordTrace]
  refine ⟨11962048621824440239146637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15949398162432586985528849 11962048621824440239146637)
  ·
    refine ⟨4485768233184165089679989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11962048621824440239146637 4485768233184165089679989)
    ·
      refine ⟨420540771861015477157499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4485768233184165089679989 420540771861015477157499)
      ·
        refine ⟨630811157791523215736249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420540771861015477157499 630811157791523215736249)
        ·
          refine ⟨473108368343642411802187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630811157791523215736249 473108368343642411802187)
          ·
            refine ⟨709662552515463617703281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473108368343642411802187 709662552515463617703281)
            ·
              refine ⟨532246914386597713277461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709662552515463617703281 532246914386597713277461)
              ·
                refine ⟨24949074111871767809881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 532246914386597713277461 24949074111871767809881)
                ·
                  rfl

theorem cell22_655940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 6].length) (baseStart_655940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655940 prefixEnd_655940 := by exact prefixLift 655940
  have htrace : WordTrace (prefixWord ++ tailWord_655940) baseStart_655940 baseEnd_655940 := by
    simpa [prefixWord, tailWord_655940, baseEnd_655940] using wordTrace_append hprefix tailTrace_655940
  have hstable : (prefixWord ++ tailWord_655940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655940).length < 2 ^ (prefixWord ++ tailWord_655940).sum := by decide
  have hdescent : baseEnd_655940 < baseStart_655940 := by decide
  rcases family_descends (prefixWord ++ tailWord_655940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655947 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 1, 4]
def baseStart_655947 : Nat := 118140960795 + 655947 * 2 ^ 59
def prefixEnd_655947 : Nat := 4983230072969 + 3 ^ 40 * 655947 * 2
def baseEnd_655947 : Nat := 224544063249900225363907

theorem tailTrace_655947 : CollatzResearch.WordTrace tailWord_655947 prefixEnd_655947 224544063249900225363907 := by
  unfold tailWord_655947
  simp only [CollatzResearch.WordTrace]
  refine ⟨23924352554623520673798095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15949568369749013782532063 23924352554623520673798095)
  ·
    refine ⟨35886528831935281010697143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23924352554623520673798095 35886528831935281010697143)
    ·
      refine ⟨53829793247902921516045715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35886528831935281010697143 53829793247902921516045715)
      ·
        refine ⟨80744689871854382274068573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53829793247902921516045715 80744689871854382274068573)
        ·
          refine ⟨30279258701945393352775715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80744689871854382274068573 30279258701945393352775715)
          ·
            refine ⟨45418888052918090029163573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30279258701945393352775715 45418888052918090029163573)
            ·
              refine ⟨4258020754961070940234085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45418888052918090029163573 4258020754961070940234085)
              ·
                refine ⟨798378891555200801293891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4258020754961070940234085 798378891555200801293891)
                ·
                  refine ⟨1197568337332801201940837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798378891555200801293891 1197568337332801201940837)
                  ·
                    refine ⟨224544063249900225363907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1197568337332801201940837 224544063249900225363907)
                    ·
                      rfl

theorem cell22_655947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 4].length) (baseStart_655947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_655947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_655947 prefixEnd_655947 := by exact prefixLift 655947
  have htrace : WordTrace (prefixWord ++ tailWord_655947) baseStart_655947 baseEnd_655947 := by
    simpa [prefixWord, tailWord_655947, baseEnd_655947] using wordTrace_append hprefix tailTrace_655947
  have hstable : (prefixWord ++ tailWord_655947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655947).length < 2 ^ (prefixWord ++ tailWord_655947).sum := by decide
  have hdescent : baseEnd_655947 < baseStart_655947 := by decide
  rcases family_descends (prefixWord ++ tailWord_655947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656114 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_656114 : Nat := 118140960795 + 656114 * 2 ^ 59
def prefixEnd_656114 : Nat := 4983230072969 + 3 ^ 40 * 656114 * 2
def baseEnd_656114 : Nat := 74867076920922485479465

theorem tailTrace_656114 : CollatzResearch.WordTrace tailWord_656114 prefixEnd_656114 74867076920922485479465 := by
  unfold tailWord_656114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5982610886254627048781849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15953629030012338796751597 5982610886254627048781849)
  ·
    refine ⟨4486958164690970286586387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5982610886254627048781849 4486958164690970286586387)
    ·
      refine ⟨6730437247036455429879581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4486958164690970286586387 6730437247036455429879581)
      ·
        refine ⟨2523913967638670786204843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6730437247036455429879581 2523913967638670786204843)
        ·
          refine ⟨3785870951458006179307265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523913967638670786204843 3785870951458006179307265)
          ·
            refine ⟨2839403213593504634480449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3785870951458006179307265 2839403213593504634480449)
            ·
              refine ⟨2129552410195128475860337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2839403213593504634480449 2129552410195128475860337)
              ·
                refine ⟨1597164307646346356895253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129552410195128475860337 1597164307646346356895253)
                ·
                  refine ⟨74867076920922485479465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1597164307646346356895253 74867076920922485479465)
                  ·
                    rfl

theorem cell22_656114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_656114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656114 prefixEnd_656114 := by exact prefixLift 656114
  have htrace : WordTrace (prefixWord ++ tailWord_656114) baseStart_656114 baseEnd_656114 := by
    simpa [prefixWord, tailWord_656114, baseEnd_656114] using wordTrace_append hprefix tailTrace_656114
  have hstable : (prefixWord ++ tailWord_656114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656114).length < 2 ^ (prefixWord ++ tailWord_656114).sum := by decide
  have hdescent : baseEnd_656114 < baseStart_656114 := by decide
  rcases family_descends (prefixWord ++ tailWord_656114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656159 : List Nat := [1, 1, 2, 4, 2, 3, 2, 7]
def baseStart_656159 : Nat := 118140960795 + 656159 * 2 ^ 59
def prefixEnd_656159 : Nat := 4983230072969 + 3 ^ 40 * 656159 * 2
def baseEnd_656159 : Nat := 24957403909155815451473

theorem tailTrace_656159 : CollatzResearch.WordTrace tailWord_656159 prefixEnd_656159 24957403909155815451473 := by
  unfold tailWord_656159
  simp only [CollatzResearch.WordTrace]
  refine ⟨23932084829855480880515531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15954723219903653920343687 23932084829855480880515531)
  ·
    refine ⟨35898127244783221320773297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23932084829855480880515531 35898127244783221320773297)
    ·
      refine ⟨26923595433587415990579973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35898127244783221320773297 26923595433587415990579973)
      ·
        refine ⟨5048174143797640498233745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26923595433587415990579973 5048174143797640498233745)
        ·
          refine ⟨3786130607848230373675309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5048174143797640498233745 3786130607848230373675309)
          ·
            refine ⟨1419798977943086390128241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3786130607848230373675309 1419798977943086390128241)
            ·
              refine ⟨1064849233457314792596181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1419798977943086390128241 1064849233457314792596181)
              ·
                refine ⟨24957403909155815451473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1064849233457314792596181 24957403909155815451473)
                ·
                  rfl

theorem cell22_656159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 7].length) (baseStart_656159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656159 prefixEnd_656159 := by exact prefixLift 656159
  have htrace : WordTrace (prefixWord ++ tailWord_656159) baseStart_656159 baseEnd_656159 := by
    simpa [prefixWord, tailWord_656159, baseEnd_656159] using wordTrace_append hprefix tailTrace_656159
  have hstable : (prefixWord ++ tailWord_656159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656159).length < 2 ^ (prefixWord ++ tailWord_656159).sum := by decide
  have hdescent : baseEnd_656159 < baseStart_656159 := by decide
  rcases family_descends (prefixWord ++ tailWord_656159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656266 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_656266 : Nat := 118140960795 + 656266 * 2 ^ 59
def prefixEnd_656266 : Nat := 4983230072969 + 3 ^ 40 * 656266 * 2
def baseEnd_656266 : Nat := 74884421156363242212643

theorem tailTrace_656266 : CollatzResearch.WordTrace tailWord_656266 prefixEnd_656266 74884421156363242212643 := by
  unfold tailWord_656266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5983996860116959538665163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15957324960311892103107101 5983996860116959538665163)
  ·
    refine ⟨8975995290175439307997745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5983996860116959538665163 8975995290175439307997745)
    ·
      refine ⟨6731996467631579480998309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8975995290175439307997745 6731996467631579480998309)
      ·
        refine ⟨1262249337680921152687183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6731996467631579480998309 1262249337680921152687183)
        ·
          refine ⟨1893374006521381729030775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262249337680921152687183 1893374006521381729030775)
          ·
            refine ⟨2840061009782072593546163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893374006521381729030775 2840061009782072593546163)
            ·
              refine ⟨4260091514673108890319245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840061009782072593546163 4260091514673108890319245)
              ·
                refine ⟨1597534318002415833869717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4260091514673108890319245 1597534318002415833869717)
                ·
                  refine ⟨74884421156363242212643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1597534318002415833869717 74884421156363242212643)
                  ·
                    rfl

theorem cell22_656266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_656266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656266 prefixEnd_656266 := by exact prefixLift 656266
  have htrace : WordTrace (prefixWord ++ tailWord_656266) baseStart_656266 baseEnd_656266 := by
    simpa [prefixWord, tailWord_656266, baseEnd_656266] using wordTrace_append hprefix tailTrace_656266
  have hstable : (prefixWord ++ tailWord_656266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656266).length < 2 ^ (prefixWord ++ tailWord_656266).sum := by decide
  have hdescent : baseEnd_656266 < baseStart_656266 := by decide
  rcases family_descends (prefixWord ++ tailWord_656266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656279 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 3, 6]
def baseStart_656279 : Nat := 118140960795 + 656279 * 2 ^ 59
def prefixEnd_656279 : Nat := 4983230072969 + 3 ^ 40 * 656279 * 2
def baseEnd_656279 : Nat := 224657713634762026062889

theorem tailTrace_656279 : CollatzResearch.WordTrace tailWord_656279 prefixEnd_656279 224657713634762026062889 := by
  unfold tailWord_656279
  simp only [CollatzResearch.WordTrace]
  refine ⟨23936461589420741374883891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15957641059613827583255927 23936461589420741374883891)
  ·
    refine ⟨35904692384131112062325837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23936461589420741374883891 35904692384131112062325837)
    ·
      refine ⟨13464259644049167023372189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35904692384131112062325837 13464259644049167023372189)
      ·
        refine ⟨5049097366518437633764571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13464259644049167023372189 5049097366518437633764571)
        ·
          refine ⟨7573646049777656450646857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5049097366518437633764571 7573646049777656450646857)
          ·
            refine ⟨5680234537333242337985143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7573646049777656450646857 5680234537333242337985143)
            ·
              refine ⟨8520351805999863506977715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5680234537333242337985143 8520351805999863506977715)
              ·
                refine ⟨12780527708999795260466573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8520351805999863506977715 12780527708999795260466573)
                ·
                  refine ⟨4792697890874923222674965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12780527708999795260466573 4792697890874923222674965)
                  ·
                    refine ⟨224657713634762026062889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4792697890874923222674965 224657713634762026062889)
                    ·
                      rfl

theorem cell22_656279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_656279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656279 prefixEnd_656279 := by exact prefixLift 656279
  have htrace : WordTrace (prefixWord ++ tailWord_656279) baseStart_656279 baseEnd_656279 := by
    simpa [prefixWord, tailWord_656279, baseEnd_656279] using wordTrace_append hprefix tailTrace_656279
  have hstable : (prefixWord ++ tailWord_656279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656279).length < 2 ^ (prefixWord ++ tailWord_656279).sum := by decide
  have hdescent : baseEnd_656279 < baseStart_656279 := by decide
  rcases family_descends (prefixWord ++ tailWord_656279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656420 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_656420 : Nat := 118140960795 + 656420 * 2 ^ 59
def prefixEnd_656420 : Nat := 4983230072969 + 3 ^ 40 * 656420 * 2
def baseEnd_656420 : Nat := 224705980816284658287457

theorem tailTrace_656420 : CollatzResearch.WordTrace tailWord_656420 prefixEnd_656420 224705980816284658287457 := by
  unfold tailWord_656420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11970802140954961227883357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15961069521273281637177809 11970802140954961227883357)
  ·
    refine ⟨4489050802858110460456259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11970802140954961227883357 4489050802858110460456259)
    ·
      refine ⟨6733576204287165690684389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4489050802858110460456259 6733576204287165690684389)
      ·
        refine ⟨1262545538303843567003323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6733576204287165690684389 1262545538303843567003323)
        ·
          refine ⟨1893818307455765350504985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262545538303843567003323 1893818307455765350504985)
          ·
            refine ⟨1420363730591824012878739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1893818307455765350504985 1420363730591824012878739)
            ·
              refine ⟨2130545595887736019318109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420363730591824012878739 2130545595887736019318109)
              ·
                refine ⟨798954598457901007244291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2130545595887736019318109 798954598457901007244291)
                ·
                  refine ⟨1198431897686851510866437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798954598457901007244291 1198431897686851510866437)
                  ·
                    refine ⟨224705980816284658287457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1198431897686851510866437 224705980816284658287457)
                    ·
                      rfl

theorem cell22_656420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_656420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656420 prefixEnd_656420 := by exact prefixLift 656420
  have htrace : WordTrace (prefixWord ++ tailWord_656420) baseStart_656420 baseEnd_656420 := by
    simpa [prefixWord, tailWord_656420, baseEnd_656420] using wordTrace_append hprefix tailTrace_656420
  have hstable : (prefixWord ++ tailWord_656420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656420).length < 2 ^ (prefixWord ++ tailWord_656420).sum := by decide
  have hdescent : baseEnd_656420 < baseStart_656420 := by decide
  rcases family_descends (prefixWord ++ tailWord_656420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656433 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 4, 3]
def baseStart_656433 : Nat := 118140960795 + 656433 * 2 ^ 59
def prefixEnd_656433 : Nat := 4983230072969 + 3 ^ 40 * 656433 * 2
def baseEnd_656433 : Nat := 224710430981956957712417

theorem tailTrace_656433 : CollatzResearch.WordTrace tailWord_656433 prefixEnd_656433 224710430981956957712417 := by
  unfold tailWord_656433
  simp only [CollatzResearch.WordTrace]
  refine ⟨23942078430862825675989953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15961385620575217117326635 23942078430862825675989953)
  ·
    refine ⟨17956558823147119256992465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23942078430862825675989953 17956558823147119256992465)
    ·
      refine ⟨13467419117360339442744349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17956558823147119256992465 13467419117360339442744349)
      ·
        refine ⟨5050282169010127291029131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13467419117360339442744349 5050282169010127291029131)
        ·
          refine ⟨7575423253515190936543697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5050282169010127291029131 7575423253515190936543697)
          ·
            refine ⟨5681567440136393202407773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7575423253515190936543697 5681567440136393202407773)
            ·
              refine ⟨2130587790051147450902915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5681567440136393202407773 2130587790051147450902915)
              ·
                refine ⟨3195881685076721176354373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130587790051147450902915 3195881685076721176354373)
                ·
                  refine ⟨599227815951885220566445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3195881685076721176354373 599227815951885220566445)
                  ·
                    refine ⟨224710430981956957712417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 599227815951885220566445 224710430981956957712417)
                    ·
                      rfl

theorem cell22_656433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_656433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656433 prefixEnd_656433 := by exact prefixLift 656433
  have htrace : WordTrace (prefixWord ++ tailWord_656433) baseStart_656433 baseEnd_656433 := by
    simpa [prefixWord, tailWord_656433, baseEnd_656433] using wordTrace_append hprefix tailTrace_656433
  have hstable : (prefixWord ++ tailWord_656433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656433).length < 2 ^ (prefixWord ++ tailWord_656433).sum := by decide
  have hdescent : baseEnd_656433 < baseStart_656433 := by decide
  rcases family_descends (prefixWord ++ tailWord_656433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656501 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 2, 3]
def baseStart_656501 : Nat := 118140960795 + 656501 * 2 ^ 59
def prefixEnd_656501 : Nat := 4983230072969 + 3 ^ 40 * 656501 * 2
def baseEnd_656501 : Nat := 224733708771627447012209

theorem tailTrace_656501 : CollatzResearch.WordTrace tailWord_656501 prefixEnd_656501 224733708771627447012209 := by
  unfold tailWord_656501
  simp only [CollatzResearch.WordTrace]
  refine ⟨23944558594616473289465357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15963039063077648859643571 23944558594616473289465357)
  ·
    refine ⟨8979209472981177483549509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23944558594616473289465357 8979209472981177483549509)
    ·
      refine ⟨1683601776183970778165533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8979209472981177483549509 1683601776183970778165533)
      ·
        refine ⟨631350666068989041812075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1683601776183970778165533 631350666068989041812075)
        ·
          refine ⟨947025999103483562718113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631350666068989041812075 947025999103483562718113)
          ·
            refine ⟨710269499327612672038585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 947025999103483562718113 710269499327612672038585)
            ·
              refine ⟨532702124495709504028939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 710269499327612672038585 532702124495709504028939)
              ·
                refine ⟨799053186743564256043409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532702124495709504028939 799053186743564256043409)
                ·
                  refine ⟨599289890057673192032557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 799053186743564256043409 599289890057673192032557)
                  ·
                    refine ⟨224733708771627447012209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 599289890057673192032557 224733708771627447012209)
                    ·
                      rfl

theorem cell22_656501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_656501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656501 prefixEnd_656501 := by exact prefixLift 656501
  have htrace : WordTrace (prefixWord ++ tailWord_656501) baseStart_656501 baseEnd_656501 := by
    simpa [prefixWord, tailWord_656501, baseEnd_656501] using wordTrace_append hprefix tailTrace_656501
  have hstable : (prefixWord ++ tailWord_656501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656501).length < 2 ^ (prefixWord ++ tailWord_656501).sum := by decide
  have hdescent : baseEnd_656501 < baseStart_656501 := by decide
  rcases family_descends (prefixWord ++ tailWord_656501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656508 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 5]
def baseStart_656508 : Nat := 118140960795 + 656508 * 2 ^ 59
def prefixEnd_656508 : Nat := 4983230072969 + 3 ^ 40 * 656508 * 2
def baseEnd_656508 : Nat := 74912035004893920695729

theorem tailTrace_656508 : CollatzResearch.WordTrace tailWord_656508 prefixEnd_656508 74912035004893920695729 := by
  unfold tailWord_656508
  simp only [CollatzResearch.WordTrace]
  refine ⟨11972406952795556742485089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15963209270394075656646785 11972406952795556742485089)
  ·
    refine ⟨8979305214596667556863817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11972406952795556742485089 8979305214596667556863817)
    ·
      refine ⟨6734478910947500667647863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8979305214596667556863817 6734478910947500667647863)
      ·
        refine ⟨10101718366421251001471795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6734478910947500667647863 10101718366421251001471795)
        ·
          refine ⟨15152577549631876502207693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10101718366421251001471795 15152577549631876502207693)
          ·
            refine ⟨5682216581111953688327885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15152577549631876502207693 5682216581111953688327885)
            ·
              refine ⟨2130831217916982633122957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5682216581111953688327885 2130831217916982633122957)
              ·
                refine ⟨799061706718868487421109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2130831217916982633122957 799061706718868487421109)
                ·
                  refine ⟨74912035004893920695729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 799061706718868487421109 74912035004893920695729)
                  ·
                    rfl

theorem cell22_656508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_656508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656508 prefixEnd_656508 := by exact prefixLift 656508
  have htrace : WordTrace (prefixWord ++ tailWord_656508) baseStart_656508 baseEnd_656508 := by
    simpa [prefixWord, tailWord_656508, baseEnd_656508] using wordTrace_append hprefix tailTrace_656508
  have hstable : (prefixWord ++ tailWord_656508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656508).length < 2 ^ (prefixWord ++ tailWord_656508).sum := by decide
  have hdescent : baseEnd_656508 < baseStart_656508 := by decide
  rcases family_descends (prefixWord ++ tailWord_656508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656542 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_656542 : Nat := 118140960795 + 656542 * 2 ^ 59
def prefixEnd_656542 : Nat := 4983230072969 + 3 ^ 40 * 656542 * 2
def baseEnd_656542 : Nat := 74915914636505668912361

theorem tailTrace_656542 : CollatzResearch.WordTrace tailWord_656542 prefixEnd_656542 74915914636505668912361 := by
  unfold tailWord_656542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993256748433492161463485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15964035991645291527805253 2993256748433492161463485)
  ·
    refine ⟨1122471280662559560548807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2993256748433492161463485 1122471280662559560548807)
    ·
      refine ⟨1683706920993839340823211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122471280662559560548807 1683706920993839340823211)
      ·
        refine ⟨2525560381490759011234817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683706920993839340823211 2525560381490759011234817)
        ·
          refine ⟨1894170286118069258426113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2525560381490759011234817 1894170286118069258426113)
          ·
            refine ⟨1420627714588551943819585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1894170286118069258426113 1420627714588551943819585)
            ·
              refine ⟨1065470785941413957864689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420627714588551943819585 1065470785941413957864689)
              ·
                refine ⟨799103089456060468398517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065470785941413957864689 799103089456060468398517)
                ·
                  refine ⟨74915914636505668912361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 799103089456060468398517 74915914636505668912361)
                  ·
                    rfl

theorem cell22_656542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_656542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656542 prefixEnd_656542 := by exact prefixLift 656542
  have htrace : WordTrace (prefixWord ++ tailWord_656542) baseStart_656542 baseEnd_656542 := by
    simpa [prefixWord, tailWord_656542, baseEnd_656542] using wordTrace_append hprefix tailTrace_656542
  have hstable : (prefixWord ++ tailWord_656542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656542).length < 2 ^ (prefixWord ++ tailWord_656542).sum := by decide
  have hdescent : baseEnd_656542 < baseStart_656542 := by decide
  rcases family_descends (prefixWord ++ tailWord_656542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656643 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 7]
def baseStart_656643 : Nat := 118140960795 + 656643 * 2 ^ 59
def prefixEnd_656643 : Nat := 4983230072969 + 3 ^ 40 * 656643 * 2
def baseEnd_656643 : Nat := 74927439424528803320591

theorem tailTrace_656643 : CollatzResearch.WordTrace tailWord_656643 prefixEnd_656643 74927439424528803320591 := by
  unfold tailWord_656643
  simp only [CollatzResearch.WordTrace]
  refine ⟨23949737760102031541134583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15966491840068021027423055 23949737760102031541134583)
  ·
    refine ⟨35924606640153047311701875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23949737760102031541134583 35924606640153047311701875)
    ·
      refine ⟨53886909960229570967552813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35924606640153047311701875 53886909960229570967552813)
      ·
        refine ⟨20207591235086089112832305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53886909960229570967552813 20207591235086089112832305)
        ·
          refine ⟨15155693426314566834624229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20207591235086089112832305 15155693426314566834624229)
          ·
            refine ⟨2841692517433981281492043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15155693426314566834624229 2841692517433981281492043)
            ·
              refine ⟨4262538776150971922238065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841692517433981281492043 4262538776150971922238065)
              ·
                refine ⟨3196904082113228941678549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4262538776150971922238065 3196904082113228941678549)
                ·
                  refine ⟨74927439424528803320591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3196904082113228941678549 74927439424528803320591)
                  ·
                    rfl

theorem cell22_656643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 7].length) (baseStart_656643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656643 prefixEnd_656643 := by exact prefixLift 656643
  have htrace : WordTrace (prefixWord ++ tailWord_656643) baseStart_656643 baseEnd_656643 := by
    simpa [prefixWord, tailWord_656643, baseEnd_656643] using wordTrace_append hprefix tailTrace_656643
  have hstable : (prefixWord ++ tailWord_656643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656643).length < 2 ^ (prefixWord ++ tailWord_656643).sum := by decide
  have hdescent : baseEnd_656643 < baseStart_656643 := by decide
  rcases family_descends (prefixWord ++ tailWord_656643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656670 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_656670 : Nat := 118140960795 + 656670 * 2 ^ 59
def prefixEnd_656670 : Nat := 4983230072969 + 3 ^ 40 * 656670 * 2
def baseEnd_656670 : Nat := 224791560925367339536691

theorem tailTrace_656670 : CollatzResearch.WordTrace tailWord_656670 prefixEnd_656670 224791560925367339536691 := by
  unfold tailWord_656670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993840316375526894045933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15967148354002810101578309 2993840316375526894045933)
  ·
    refine ⟨1122690118640822585267225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2993840316375526894045933 1122690118640822585267225)
    ·
      refine ⟨842017588980616938950419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1122690118640822585267225 842017588980616938950419)
      ·
        refine ⟨1263026383470925408425629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842017588980616938950419 1263026383470925408425629)
        ·
          refine ⟨473634893801597028159611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1263026383470925408425629 473634893801597028159611)
          ·
            refine ⟨710452340702395542239417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473634893801597028159611 710452340702395542239417)
            ·
              refine ⟨532839255526796656679563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 710452340702395542239417 532839255526796656679563)
              ·
                refine ⟨799258883290194985019345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532839255526796656679563 799258883290194985019345)
                ·
                  refine ⟨599444162467646238764509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 799258883290194985019345 599444162467646238764509)
                  ·
                    refine ⟨224791560925367339536691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 599444162467646238764509 224791560925367339536691)
                    ·
                      rfl

theorem cell22_656670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_656670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656670 prefixEnd_656670 := by exact prefixLift 656670
  have htrace : WordTrace (prefixWord ++ tailWord_656670) baseStart_656670 baseEnd_656670 := by
    simpa [prefixWord, tailWord_656670, baseEnd_656670] using wordTrace_append hprefix tailTrace_656670
  have hstable : (prefixWord ++ tailWord_656670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656670).length < 2 ^ (prefixWord ++ tailWord_656670).sum := by decide
  have hdescent : baseEnd_656670 < baseStart_656670 := by decide
  rcases family_descends (prefixWord ++ tailWord_656670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656673 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_656673 : Nat := 118140960795 + 656673 * 2 ^ 59
def prefixEnd_656673 : Nat := 4983230072969 + 3 ^ 40 * 656673 * 2
def baseEnd_656673 : Nat := 224792587886676331711681

theorem tailTrace_656673 : CollatzResearch.WordTrace tailWord_656673 prefixEnd_656673 224792587886676331711681 := by
  unfold tailWord_656673
  simp only [CollatzResearch.WordTrace]
  refine ⟨23950831949993346664726673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15967221299995564443151115 23950831949993346664726673)
  ·
    refine ⟨17963123962495009998545005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23950831949993346664726673 17963123962495009998545005)
    ·
      refine ⟨6736171485935628749454377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17963123962495009998545005 6736171485935628749454377)
      ·
        refine ⟨5052128614451721562090783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6736171485935628749454377 5052128614451721562090783)
        ·
          refine ⟨7578192921677582343136175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5052128614451721562090783 7578192921677582343136175)
          ·
            refine ⟨11367289382516373514704263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7578192921677582343136175 11367289382516373514704263)
            ·
              refine ⟨17050934073774560272056395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11367289382516373514704263 17050934073774560272056395)
              ·
                refine ⟨25576401110661840408084593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17050934073774560272056395 25576401110661840408084593)
                ·
                  refine ⟨19182300832996380306063445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25576401110661840408084593 19182300832996380306063445)
                  ·
                    refine ⟨224792587886676331711681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19182300832996380306063445 224792587886676331711681)
                    ·
                      rfl

theorem cell22_656673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_656673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656673 prefixEnd_656673 := by exact prefixLift 656673
  have htrace : WordTrace (prefixWord ++ tailWord_656673) baseStart_656673 baseEnd_656673 := by
    simpa [prefixWord, tailWord_656673, baseEnd_656673] using wordTrace_append hprefix tailTrace_656673
  have hstable : (prefixWord ++ tailWord_656673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656673).length < 2 ^ (prefixWord ++ tailWord_656673).sum := by decide
  have hdescent : baseEnd_656673 < baseStart_656673 := by decide
  rcases family_descends (prefixWord ++ tailWord_656673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656677 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 5]
def baseStart_656677 : Nat := 118140960795 + 656677 * 2 ^ 59
def prefixEnd_656677 : Nat := 4983230072969 + 3 ^ 40 * 656677 * 2
def baseEnd_656677 : Nat := 74931319056140551537223

theorem tailTrace_656677 : CollatzResearch.WordTrace tailWord_656677 prefixEnd_656677 74931319056140551537223 := by
  unfold tailWord_656677
  simp only [CollatzResearch.WordTrace]
  refine ⟨23950977841978855347872285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15967318561319236898581523 23950977841978855347872285)
  ·
    refine ⟨8981616690742070755452107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23950977841978855347872285 8981616690742070755452107)
    ·
      refine ⟨13472425036113106133178161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8981616690742070755452107 13472425036113106133178161)
      ·
        refine ⟨10104318777084829599883621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13472425036113106133178161 10104318777084829599883621)
        ·
          refine ⟨1894559770703405549978179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10104318777084829599883621 1894559770703405549978179)
          ·
            refine ⟨2841839656055108324967269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894559770703405549978179 2841839656055108324967269)
            ·
              refine ⟨532844935510332810931363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2841839656055108324967269 532844935510332810931363)
              ·
                refine ⟨799267403265499216397045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532844935510332810931363 799267403265499216397045)
                ·
                  refine ⟨74931319056140551537223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 799267403265499216397045 74931319056140551537223)
                  ·
                    rfl

theorem cell22_656677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_656677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656677 prefixEnd_656677 := by exact prefixLift 656677
  have htrace : WordTrace (prefixWord ++ tailWord_656677) baseStart_656677 baseEnd_656677 := by
    simpa [prefixWord, tailWord_656677, baseEnd_656677] using wordTrace_append hprefix tailTrace_656677
  have hstable : (prefixWord ++ tailWord_656677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656677).length < 2 ^ (prefixWord ++ tailWord_656677).sum := by decide
  have hdescent : baseEnd_656677 < baseStart_656677 := by decide
  rcases family_descends (prefixWord ++ tailWord_656677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656688 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 8]
def baseStart_656688 : Nat := 118140960795 + 656688 * 2 ^ 59
def prefixEnd_656688 : Nat := 4983230072969 + 3 ^ 40 * 656688 * 2
def baseEnd_656688 : Nat := 74932574231073764195545

theorem tailTrace_656688 : CollatzResearch.WordTrace tailWord_656688 prefixEnd_656688 74932574231073764195545 := by
  unfold tailWord_656688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11975689522469502113261359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15967586029959336151015145 11975689522469502113261359)
  ·
    refine ⟨17963534283704253169892039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11975689522469502113261359 17963534283704253169892039)
    ·
      refine ⟨26945301425556379754838059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17963534283704253169892039 26945301425556379754838059)
      ·
        refine ⟨40417952138334569632257089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26945301425556379754838059 40417952138334569632257089)
        ·
          refine ⟨30313464103750927224192817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40417952138334569632257089 30313464103750927224192817)
          ·
            refine ⟨22735098077813195418144613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30313464103750927224192817 22735098077813195418144613)
            ·
              refine ⟨4262830889589974140902115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22735098077813195418144613 4262830889589974140902115)
              ·
                refine ⟨6394246334384961211353173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262830889589974140902115 6394246334384961211353173)
                ·
                  refine ⟨74932574231073764195545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6394246334384961211353173 74932574231073764195545)
                  ·
                    rfl

theorem cell22_656688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_656688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656688 prefixEnd_656688 := by exact prefixLift 656688
  have htrace : WordTrace (prefixWord ++ tailWord_656688) baseStart_656688 baseEnd_656688 := by
    simpa [prefixWord, tailWord_656688, baseEnd_656688] using wordTrace_append hprefix tailTrace_656688
  have hstable : (prefixWord ++ tailWord_656688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656688).length < 2 ^ (prefixWord ++ tailWord_656688).sum := by decide
  have hdescent : baseEnd_656688 < baseStart_656688 := by decide
  rcases family_descends (prefixWord ++ tailWord_656688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656855 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 5, 5]
def baseStart_656855 : Nat := 118140960795 + 656855 * 2 ^ 59
def prefixEnd_656855 : Nat := 4983230072969 + 3 ^ 40 * 656855 * 2
def baseEnd_656855 : Nat := 224854890206088523661123

theorem tailTrace_656855 : CollatzResearch.WordTrace tailWord_656855 prefixEnd_656855 224854890206088523661123 := by
  unfold tailWord_656855
  simp only [CollatzResearch.WordTrace]
  refine ⟨23957470035333991747852019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15971646690222661165234679 23957470035333991747852019)
  ·
    refine ⟨35936205053000987621778029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23957470035333991747852019 35936205053000987621778029)
    ·
      refine ⟨13476076894875370358166761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35936205053000987621778029 13476076894875370358166761)
      ·
        refine ⟨10107057671156527768625071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13476076894875370358166761 10107057671156527768625071)
        ·
          refine ⟨15160586506734791652937607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10107057671156527768625071 15160586506734791652937607)
          ·
            refine ⟨22740879760102187479406411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15160586506734791652937607 22740879760102187479406411)
            ·
              refine ⟨34111319640153281219109617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22740879760102187479406411 34111319640153281219109617)
              ·
                refine ⟨25583489730114960914332213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34111319640153281219109617 25583489730114960914332213)
                ·
                  refine ⟨2398452162198277585718645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25583489730114960914332213 2398452162198277585718645)
                  ·
                    refine ⟨224854890206088523661123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2398452162198277585718645 224854890206088523661123)
                    ·
                      rfl

theorem cell22_656855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_656855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656855 prefixEnd_656855 := by exact prefixLift 656855
  have htrace : WordTrace (prefixWord ++ tailWord_656855) baseStart_656855 baseEnd_656855 := by
    simpa [prefixWord, tailWord_656855, baseEnd_656855] using wordTrace_append hprefix tailTrace_656855
  have hstable : (prefixWord ++ tailWord_656855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656855).length < 2 ^ (prefixWord ++ tailWord_656855).sum := by decide
  have hdescent : baseEnd_656855 < baseStart_656855 := by decide
  rcases family_descends (prefixWord ++ tailWord_656855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656872 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_656872 : Nat := 118140960795 + 656872 * 2 ^ 59
def prefixEnd_656872 : Nat := 4983230072969 + 3 ^ 40 * 656872 * 2
def baseEnd_656872 : Nat := 224860709653506145986071

theorem tailTrace_656872 : CollatzResearch.WordTrace tailWord_656872 prefixEnd_656872 224860709653506145986071 := by
  unfold tailWord_656872
  simp only [CollatzResearch.WordTrace]
  refine ⟨11979045038136201825610435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15972060050848269100813913 11979045038136201825610435)
  ·
    refine ⟨17968567557204302738415653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11979045038136201825610435 17968567557204302738415653)
    ·
      refine ⟨3369106416975806763452935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17968567557204302738415653 3369106416975806763452935)
      ·
        refine ⟨5053659625463710145179403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369106416975806763452935 5053659625463710145179403)
        ·
          refine ⟨7580489438195565217769105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5053659625463710145179403 7580489438195565217769105)
          ·
            refine ⟨5685367078646673913326829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7580489438195565217769105 5685367078646673913326829)
            ·
              refine ⟨2132012654492502717497561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5685367078646673913326829 2132012654492502717497561)
              ·
                refine ⟨1599009490869377038123171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132012654492502717497561 1599009490869377038123171)
                ·
                  refine ⟨2398514236304065557184757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599009490869377038123171 2398514236304065557184757)
                  ·
                    refine ⟨224860709653506145986071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2398514236304065557184757 224860709653506145986071)
                    ·
                      rfl

theorem cell22_656872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_656872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656872 prefixEnd_656872 := by exact prefixLift 656872
  have htrace : WordTrace (prefixWord ++ tailWord_656872) baseStart_656872 baseEnd_656872 := by
    simpa [prefixWord, tailWord_656872, baseEnd_656872] using wordTrace_append hprefix tailTrace_656872
  have hstable : (prefixWord ++ tailWord_656872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656872).length < 2 ^ (prefixWord ++ tailWord_656872).sum := by decide
  have hdescent : baseEnd_656872 < baseStart_656872 := by decide
  rcases family_descends (prefixWord ++ tailWord_656872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656947 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 7]
def baseStart_656947 : Nat := 118140960795 + 656947 * 2 ^ 59
def prefixEnd_656947 : Nat := 4983230072969 + 3 ^ 40 * 656947 * 2
def baseEnd_656947 : Nat := 74962127895410316786947

theorem tailTrace_656947 : CollatzResearch.WordTrace tailWord_656947 prefixEnd_656947 74962127895410316786947 := by
  unfold tailWord_656947
  simp only [CollatzResearch.WordTrace]
  refine ⟨23960825551000691460201095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15973883700667127640134063 23960825551000691460201095)
  ·
    refine ⟨35941238326501037190301643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23960825551000691460201095 35941238326501037190301643)
    ·
      refine ⟨53911857489751555785452465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35941238326501037190301643 53911857489751555785452465)
      ·
        refine ⟨40433893117313666839089349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53911857489751555785452465 40433893117313666839089349)
        ·
          refine ⟨7581354959496312532329253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40433893117313666839089349 7581354959496312532329253)
          ·
            refine ⟨1421504054905558599811735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7581354959496312532329253 1421504054905558599811735)
            ·
              refine ⟨2132256082358337899717603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421504054905558599811735 2132256082358337899717603)
              ·
                refine ⟨3198384123537506849576405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132256082358337899717603 3198384123537506849576405)
                ·
                  refine ⟨74962127895410316786947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3198384123537506849576405 74962127895410316786947)
                  ·
                    rfl

theorem cell22_656947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 7].length) (baseStart_656947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656947 prefixEnd_656947 := by exact prefixLift 656947
  have htrace : WordTrace (prefixWord ++ tailWord_656947) baseStart_656947 baseEnd_656947 := by
    simpa [prefixWord, tailWord_656947, baseEnd_656947] using wordTrace_append hprefix tailTrace_656947
  have hstable : (prefixWord ++ tailWord_656947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656947).length < 2 ^ (prefixWord ++ tailWord_656947).sum := by decide
  have hdescent : baseEnd_656947 < baseStart_656947 := by decide
  rcases family_descends (prefixWord ++ tailWord_656947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656951 : List Nat := [1, 1, 3, 1, 2, 4, 2, 4, 1, 3]
def baseStart_656951 : Nat := 118140960795 + 656951 * 2 ^ 59
def prefixEnd_656951 : Nat := 4983230072969 + 3 ^ 40 * 656951 * 2
def baseEnd_656951 : Nat := 224887752967976273260829

theorem tailTrace_656951 : CollatzResearch.WordTrace tailWord_656951 prefixEnd_656951 224887752967976273260829 := by
  unfold tailWord_656951
  simp only [CollatzResearch.WordTrace]
  refine ⟨23960971442986200143346707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15973980961990800095564471 23960971442986200143346707)
  ·
    refine ⟨35941457164479300215020061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23960971442986200143346707 35941457164479300215020061)
    ·
      refine ⟨13478046436679737580632523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35941457164479300215020061 13478046436679737580632523)
      ·
        refine ⟨20217069655019606370948785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13478046436679737580632523 20217069655019606370948785)
        ·
          refine ⟨15162802241264704778211589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20217069655019606370948785 15162802241264704778211589)
          ·
            refine ⟨2843025420237132145914673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15162802241264704778211589 2843025420237132145914673)
            ·
              refine ⟨2132269065177849109436005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2843025420237132145914673 2132269065177849109436005)
              ·
                refine ⟨399800449720846708019251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2132269065177849109436005 399800449720846708019251)
                ·
                  refine ⟨599700674581270062028877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399800449720846708019251 599700674581270062028877)
                  ·
                    refine ⟨224887752967976273260829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 599700674581270062028877 224887752967976273260829)
                    ·
                      rfl

theorem cell22_656951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_656951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_656951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_656951 prefixEnd_656951 := by exact prefixLift 656951
  have htrace : WordTrace (prefixWord ++ tailWord_656951) baseStart_656951 baseEnd_656951 := by
    simpa [prefixWord, tailWord_656951, baseEnd_656951] using wordTrace_append hprefix tailTrace_656951
  have hstable : (prefixWord ++ tailWord_656951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656951).length < 2 ^ (prefixWord ++ tailWord_656951).sum := by decide
  have hdescent : baseEnd_656951 < baseStart_656951 := by decide
  rcases family_descends (prefixWord ++ tailWord_656951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657009 : List Nat := [1, 2, 2, 2, 1, 1, 1, 8, 4]
def baseStart_657009 : Nat := 118140960795 + 657009 * 2 ^ 59
def prefixEnd_657009 : Nat := 4983230072969 + 3 ^ 40 * 657009 * 2
def baseEnd_657009 : Nat := 74969202517761151770217

theorem tailTrace_657009 : CollatzResearch.WordTrace tailWord_657009 prefixEnd_657009 74969202517761151770217 := by
  unfold tailWord_657009
  simp only [CollatzResearch.WordTrace]
  refine ⟨23963086876776076048958081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15975391251184050699305387 23963086876776076048958081)
  ·
    refine ⟨17972315157582057036718561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23963086876776076048958081 17972315157582057036718561)
    ·
      refine ⟨13479236368186542777538921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17972315157582057036718561 13479236368186542777538921)
      ·
        refine ⟨10109427276139907083154191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13479236368186542777538921 10109427276139907083154191)
        ·
          refine ⟨15164140914209860624731287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10109427276139907083154191 15164140914209860624731287)
          ·
            refine ⟨22746211371314790937096931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15164140914209860624731287 22746211371314790937096931)
            ·
              refine ⟨34119317056972186405645397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22746211371314790937096931 34119317056972186405645397)
              ·
                refine ⟨399835746761392809441157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 34119317056972186405645397 399835746761392809441157)
                ·
                  refine ⟨74969202517761151770217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 399835746761392809441157 74969202517761151770217)
                  ·
                    rfl

theorem cell22_657009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 4].length) (baseStart_657009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657009 prefixEnd_657009 := by exact prefixLift 657009
  have htrace : WordTrace (prefixWord ++ tailWord_657009) baseStart_657009 baseEnd_657009 := by
    simpa [prefixWord, tailWord_657009, baseEnd_657009] using wordTrace_append hprefix tailTrace_657009
  have hstable : (prefixWord ++ tailWord_657009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657009).length < 2 ^ (prefixWord ++ tailWord_657009).sum := by decide
  have hdescent : baseEnd_657009 < baseStart_657009 := by decide
  rcases family_descends (prefixWord ++ tailWord_657009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657028 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_657028 : Nat := 118140960795 + 657028 * 2 ^ 59
def prefixEnd_657028 : Nat := 4983230072969 + 3 ^ 40 * 657028 * 2
def baseEnd_657028 : Nat := 224914111641573739085593

theorem tailTrace_657028 : CollatzResearch.WordTrace tailWord_657028 prefixEnd_657028 224914111641573739085593 := by
  unfold tailWord_657028
  simp only [CollatzResearch.WordTrace]
  refine ⟨11981889931853621146949869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15975853242471494862599825 11981889931853621146949869)
  ·
    refine ⟨4493208724445107930106201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11981889931853621146949869 4493208724445107930106201)
    ·
      refine ⟨3369906543333830947579651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4493208724445107930106201 3369906543333830947579651)
      ·
        refine ⟨5054859815000746421369477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369906543333830947579651 5054859815000746421369477)
        ·
          refine ⟨947786215312639954006777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5054859815000746421369477 947786215312639954006777)
          ·
            refine ⟨710839661484479965505083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 947786215312639954006777 710839661484479965505083)
            ·
              refine ⟨1066259492226719948257625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710839661484479965505083 1066259492226719948257625)
              ·
                refine ⟨799694619170039961193219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1066259492226719948257625 799694619170039961193219)
                ·
                  refine ⟨1199541928755059941789829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799694619170039961193219 1199541928755059941789829)
                  ·
                    refine ⟨224914111641573739085593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1199541928755059941789829 224914111641573739085593)
                    ·
                      rfl

theorem cell22_657028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_657028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657028 prefixEnd_657028 := by exact prefixLift 657028
  have htrace : WordTrace (prefixWord ++ tailWord_657028) baseStart_657028 baseEnd_657028 := by
    simpa [prefixWord, tailWord_657028, baseEnd_657028] using wordTrace_append hprefix tailTrace_657028
  have hstable : (prefixWord ++ tailWord_657028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657028).length < 2 ^ (prefixWord ++ tailWord_657028).sum := by decide
  have hdescent : baseEnd_657028 < baseStart_657028 := by decide
  rcases family_descends (prefixWord ++ tailWord_657028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657054 : List Nat := [4, 3, 1, 1, 1, 12]
def baseStart_657054 : Nat := 118140960795 + 657054 * 2 ^ 59
def prefixEnd_657054 : Nat := 4983230072969 + 3 ^ 40 * 657054 * 2
def baseEnd_657054 : Nat := 2776827308307633801673

theorem tailTrace_657054 : CollatzResearch.WordTrace tailWord_657054 prefixEnd_657054 2776827308307633801673 := by
  unfold tailWord_657054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995591020201631091793277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15976485441075365822897477 2995591020201631091793277)
  ·
    refine ⟨1123346632575611659422479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2995591020201631091793277 1123346632575611659422479)
    ·
      refine ⟨1685019948863417489133719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123346632575611659422479 1685019948863417489133719)
      ·
        refine ⟨2527529923295126233700579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1685019948863417489133719 2527529923295126233700579)
        ·
          refine ⟨3791294884942689350550869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527529923295126233700579 3791294884942689350550869)
          ·
            refine ⟨2776827308307633801673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3791294884942689350550869 2776827308307633801673)
            ·
              rfl

theorem cell22_657054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 12].length) (baseStart_657054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657054 prefixEnd_657054 := by exact prefixLift 657054
  have htrace : WordTrace (prefixWord ++ tailWord_657054) baseStart_657054 baseEnd_657054 := by
    simpa [prefixWord, tailWord_657054, baseEnd_657054] using wordTrace_append hprefix tailTrace_657054
  have hstable : (prefixWord ++ tailWord_657054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657054).length < 2 ^ (prefixWord ++ tailWord_657054).sum := by decide
  have hdescent : baseEnd_657054 < baseStart_657054 := by decide
  rcases family_descends (prefixWord ++ tailWord_657054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657086 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_657086 : Nat := 118140960795 + 657086 * 2 ^ 59
def prefixEnd_657086 : Nat := 4983230072969 + 3 ^ 40 * 657086 * 2
def baseEnd_657086 : Nat := 224933966226880921135415

theorem tailTrace_657086 : CollatzResearch.WordTrace tailWord_657086 prefixEnd_657086 224933966226880921135415 := by
  unfold tailWord_657086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995736912187139774938889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15977263531664745466340741 2995736912187139774938889)
  ·
    refine ⟨2246802684140354831204167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2995736912187139774938889 2246802684140354831204167)
    ·
      refine ⟨3370204026210532246806251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246802684140354831204167 3370204026210532246806251)
      ·
        refine ⟨5055306039315798370209377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3370204026210532246806251 5055306039315798370209377)
        ·
          refine ⟨3791479529486848777657033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5055306039315798370209377 3791479529486848777657033)
          ·
            refine ⟨2843609647115136583242775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3791479529486848777657033 2843609647115136583242775)
            ·
              refine ⟨4265414470672704874864163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843609647115136583242775 4265414470672704874864163)
              ·
                refine ⟨6398121706009057312296245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4265414470672704874864163 6398121706009057312296245)
                ·
                  refine ⟨599823909938349123027773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6398121706009057312296245 599823909938349123027773)
                  ·
                    refine ⟨224933966226880921135415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 599823909938349123027773 224933966226880921135415)
                    ·
                      rfl

theorem cell22_657086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_657086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657086 prefixEnd_657086 := by exact prefixLift 657086
  have htrace : WordTrace (prefixWord ++ tailWord_657086) baseStart_657086 baseEnd_657086 := by
    simpa [prefixWord, tailWord_657086, baseEnd_657086] using wordTrace_append hprefix tailTrace_657086
  have hstable : (prefixWord ++ tailWord_657086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657086).length < 2 ^ (prefixWord ++ tailWord_657086).sum := by decide
  have hdescent : baseEnd_657086 < baseStart_657086 := by decide
  rcases family_descends (prefixWord ++ tailWord_657086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657090 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_657090 : Nat := 118140960795 + 657090 * 2 ^ 59
def prefixEnd_657090 : Nat := 4983230072969 + 3 ^ 40 * 657090 * 2
def baseEnd_657090 : Nat := 224935335508626244035403

theorem tailTrace_657090 : CollatzResearch.WordTrace tailWord_657090 prefixEnd_657090 224935335508626244035403 := by
  unfold tailWord_657090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5991510297370656720664181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15977360792988417921771149 5991510297370656720664181)
  ·
    refine ⟨561704090378499067562267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5991510297370656720664181 561704090378499067562267)
    ·
      refine ⟨842556135567748601343401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 561704090378499067562267 842556135567748601343401)
      ·
        refine ⟨631917101675811451007551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 842556135567748601343401 631917101675811451007551)
        ·
          refine ⟨947875652513717176511327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631917101675811451007551 947875652513717176511327)
          ·
            refine ⟨1421813478770575764766991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947875652513717176511327 1421813478770575764766991)
            ·
              refine ⟨2132720218155863647150487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421813478770575764766991 2132720218155863647150487)
              ·
                refine ⟨3199080327233795470725731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132720218155863647150487 3199080327233795470725731)
                ·
                  refine ⟨4798620490850693206088597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199080327233795470725731 4798620490850693206088597)
                  ·
                    refine ⟨224935335508626244035403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4798620490850693206088597 224935335508626244035403)
                    ·
                      rfl

theorem cell22_657090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_657090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657090 prefixEnd_657090 := by exact prefixLift 657090
  have htrace : WordTrace (prefixWord ++ tailWord_657090) baseStart_657090 baseEnd_657090 := by
    simpa [prefixWord, tailWord_657090, baseEnd_657090] using wordTrace_append hprefix tailTrace_657090
  have hstable : (prefixWord ++ tailWord_657090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657090).length < 2 ^ (prefixWord ++ tailWord_657090).sum := by decide
  have hdescent : baseEnd_657090 < baseStart_657090 := by decide
  rcases family_descends (prefixWord ++ tailWord_657090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657114 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_657114 : Nat := 118140960795 + 657114 * 2 ^ 59
def prefixEnd_657114 : Nat := 4983230072969 + 3 ^ 40 * 657114 * 2
def baseEnd_657114 : Nat := 224943551199098181435329

theorem tailTrace_657114 : CollatzResearch.WordTrace tailWord_657114 prefixEnd_657114 224943551199098181435329 := by
  unfold tailWord_657114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5991729135348919745382599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15977944360930452654353597 5991729135348919745382599)
  ·
    refine ⟨8987593703023379618073899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5991729135348919745382599 8987593703023379618073899)
    ·
      refine ⟨13481390554535069427110849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8987593703023379618073899 13481390554535069427110849)
      ·
        refine ⟨10111042915901302070333137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13481390554535069427110849 10111042915901302070333137)
        ·
          refine ⟨7583282186925976552749853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10111042915901302070333137 7583282186925976552749853)
          ·
            refine ⟨2843730820097241207281195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7583282186925976552749853 2843730820097241207281195)
            ·
              refine ⟨4265596230145861810921793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843730820097241207281195 4265596230145861810921793)
              ·
                refine ⟨3199197172609396358191345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4265596230145861810921793 3199197172609396358191345)
                ·
                  refine ⟨2399397879457047268643509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3199197172609396358191345 2399397879457047268643509)
                  ·
                    refine ⟨224943551199098181435329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2399397879457047268643509 224943551199098181435329)
                    ·
                      rfl

theorem cell22_657114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_657114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657114 prefixEnd_657114 := by exact prefixLift 657114
  have htrace : WordTrace (prefixWord ++ tailWord_657114) baseStart_657114 baseEnd_657114 := by
    simpa [prefixWord, tailWord_657114, baseEnd_657114] using wordTrace_append hprefix tailTrace_657114
  have hstable : (prefixWord ++ tailWord_657114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657114).length < 2 ^ (prefixWord ++ tailWord_657114).sum := by decide
  have hdescent : baseEnd_657114 < baseStart_657114 := by decide
  rcases family_descends (prefixWord ++ tailWord_657114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657133 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 5]
def baseStart_657133 : Nat := 118140960795 + 657133 * 2 ^ 59
def prefixEnd_657133 : Nat := 4983230072969 + 3 ^ 40 * 657133 * 2
def baseEnd_657133 : Nat := 74983351762462821736757

theorem tailTrace_657133 : CollatzResearch.WordTrace tailWord_657133 prefixEnd_657133 74983351762462821736757 := by
  unfold tailWord_657133
  simp only [CollatzResearch.WordTrace]
  refine ⟨23967609528326845226472053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15978406352217896817648035 23967609528326845226472053)
  ·
    refine ⟨2246963393280641739981755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23967609528326845226472053 2246963393280641739981755)
    ·
      refine ⟨3370445089920962609972633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246963393280641739981755 3370445089920962609972633)
      ·
        refine ⟨2527833817440721957479475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3370445089920962609972633 2527833817440721957479475)
        ·
          refine ⟨3791750726161082936219213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527833817440721957479475 3791750726161082936219213)
          ·
            refine ⟨1421906522310406101082205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3791750726161082936219213 1421906522310406101082205)
            ·
              refine ⟨533214945866402287905827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1421906522310406101082205 533214945866402287905827)
              ·
                refine ⟨799822418799603431858741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533214945866402287905827 799822418799603431858741)
                ·
                  refine ⟨74983351762462821736757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 799822418799603431858741 74983351762462821736757)
                  ·
                    rfl

theorem cell22_657133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_657133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657133 prefixEnd_657133 := by exact prefixLift 657133
  have htrace : WordTrace (prefixWord ++ tailWord_657133) baseStart_657133 baseEnd_657133 := by
    simpa [prefixWord, tailWord_657133, baseEnd_657133] using wordTrace_append hprefix tailTrace_657133
  have hstable : (prefixWord ++ tailWord_657133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657133).length < 2 ^ (prefixWord ++ tailWord_657133).sum := by decide
  have hdescent : baseEnd_657133 < baseStart_657133 := by decide
  rcases family_descends (prefixWord ++ tailWord_657133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657176 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 4, 3]
def baseStart_657176 : Nat := 118140960795 + 657176 * 2 ^ 59
def prefixEnd_657176 : Nat := 4983230072969 + 3 ^ 40 * 657176 * 2
def baseEnd_657176 : Nat := 224964775066150686385139

theorem tailTrace_657176 : CollatzResearch.WordTrace tailWord_657176 prefixEnd_657176 224964775066150686385139 := by
  unfold tailWord_657176
  simp only [CollatzResearch.WordTrace]
  refine ⟨11984588933585531785143691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15979451911447375713524921 11984588933585531785143691)
  ·
    refine ⟨17976883400378297677715537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11984588933585531785143691 17976883400378297677715537)
    ·
      refine ⟨13482662550283723258286653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17976883400378297677715537 13482662550283723258286653)
      ·
        refine ⟨5055998456356396221857495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13482662550283723258286653 5055998456356396221857495)
        ·
          refine ⟨7583997684534594332786243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5055998456356396221857495 7583997684534594332786243)
          ·
            refine ⟨11375996526801891499179365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7583997684534594332786243 11375996526801891499179365)
            ·
              refine ⟨2132999348775354656096131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11375996526801891499179365 2132999348775354656096131)
              ·
                refine ⟨3199499023163031984144197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132999348775354656096131 3199499023163031984144197)
                ·
                  refine ⟨599906066843068497027037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3199499023163031984144197 599906066843068497027037)
                  ·
                    refine ⟨224964775066150686385139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 599906066843068497027037 224964775066150686385139)
                    ·
                      rfl

theorem cell22_657176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_657176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657176 prefixEnd_657176 := by exact prefixLift 657176
  have htrace : WordTrace (prefixWord ++ tailWord_657176) baseStart_657176 baseEnd_657176 := by
    simpa [prefixWord, tailWord_657176, baseEnd_657176] using wordTrace_append hprefix tailTrace_657176
  have hstable : (prefixWord ++ tailWord_657176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657176).length < 2 ^ (prefixWord ++ tailWord_657176).sum := by decide
  have hdescent : baseEnd_657176 < baseStart_657176 := by decide
  rcases family_descends (prefixWord ++ tailWord_657176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657189 : List Nat := [1, 3, 1, 2, 3, 2, 1, 9]
def baseStart_657189 : Nat := 118140960795 + 657189 * 2 ^ 59
def prefixEnd_657189 : Nat := 4983230072969 + 3 ^ 40 * 657189 * 2
def baseEnd_657189 : Nat := 24996580581313665090011

theorem tailTrace_657189 : CollatzResearch.WordTrace tailWord_657189 prefixEnd_657189 24996580581313665090011 := by
  unfold tailWord_657189
  simp only [CollatzResearch.WordTrace]
  refine ⟨23969652016123966790510621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15979768010749311193673747 23969652016123966790510621)
  ·
    refine ⟨8988619506046487546441483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23969652016123966790510621 8988619506046487546441483)
    ·
      refine ⟨13482929259069731319662225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8988619506046487546441483 13482929259069731319662225)
      ·
        refine ⟨10112196944302298489746669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13482929259069731319662225 10112196944302298489746669)
        ·
          refine ⟨3792073854113361933655001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10112196944302298489746669 3792073854113361933655001)
          ·
            refine ⟨2844055390585021450241251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3792073854113361933655001 2844055390585021450241251)
            ·
              refine ⟨4266083085877532175361877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844055390585021450241251 4266083085877532175361877)
              ·
                refine ⟨24996580581313665090011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4266083085877532175361877 24996580581313665090011)
                ·
                  rfl

theorem cell22_657189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 9].length) (baseStart_657189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657189 prefixEnd_657189 := by exact prefixLift 657189
  have htrace : WordTrace (prefixWord ++ tailWord_657189) baseStart_657189 baseEnd_657189 := by
    simpa [prefixWord, tailWord_657189, baseEnd_657189] using wordTrace_append hprefix tailTrace_657189
  have hstable : (prefixWord ++ tailWord_657189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657189).length < 2 ^ (prefixWord ++ tailWord_657189).sum := by decide
  have hdescent : baseEnd_657189 < baseStart_657189 := by decide
  rcases family_descends (prefixWord ++ tailWord_657189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657236 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_657236 : Nat := 118140960795 + 657236 * 2 ^ 59
def prefixEnd_657236 : Nat := 4983230072969 + 3 ^ 40 * 657236 * 2
def baseEnd_657236 : Nat := 224985314292330529884955

theorem tailTrace_657236 : CollatzResearch.WordTrace tailWord_657236 prefixEnd_657236 224985314292330529884955 := by
  unfold tailWord_657236
  simp only [CollatzResearch.WordTrace]
  refine ⟨11985683123476846908735781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15980910831302462544981041 11985683123476846908735781)
  ·
    refine ⟨2247315585651908795387959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11985683123476846908735781 2247315585651908795387959)
    ·
      refine ⟨3370973378477863193081939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2247315585651908795387959 3370973378477863193081939)
      ·
        refine ⟨5056460067716794789622909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3370973378477863193081939 5056460067716794789622909)
        ·
          refine ⟨1896172525393798046108591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5056460067716794789622909 1896172525393798046108591)
          ·
            refine ⟨2844258788090697069162887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896172525393798046108591 2844258788090697069162887)
            ·
              refine ⟨4266388182136045603744331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844258788090697069162887 4266388182136045603744331)
              ·
                refine ⟨6399582273204068405616497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4266388182136045603744331 6399582273204068405616497)
                ·
                  refine ⟨4799686704903051304212373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6399582273204068405616497 4799686704903051304212373)
                  ·
                    refine ⟨224985314292330529884955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4799686704903051304212373 224985314292330529884955)
                    ·
                      rfl

theorem cell22_657236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_657236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657236 prefixEnd_657236 := by exact prefixLift 657236
  have htrace : WordTrace (prefixWord ++ tailWord_657236) baseStart_657236 baseEnd_657236 := by
    simpa [prefixWord, tailWord_657236, baseEnd_657236] using wordTrace_append hprefix tailTrace_657236
  have hstable : (prefixWord ++ tailWord_657236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657236).length < 2 ^ (prefixWord ++ tailWord_657236).sum := by decide
  have hdescent : baseEnd_657236 < baseStart_657236 := by decide
  rcases family_descends (prefixWord ++ tailWord_657236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657279 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 10]
def baseStart_657279 : Nat := 118140960795 + 657279 * 2 ^ 59
def prefixEnd_657279 : Nat := 4983230072969 + 3 ^ 40 * 657279 * 2
def baseEnd_657279 : Nat := 75000011357030917019941

theorem tailTrace_657279 : CollatzResearch.WordTrace tailWord_657279 prefixEnd_657279 75000011357030917019941 := by
  unfold tailWord_657279
  simp only [CollatzResearch.WordTrace]
  refine ⟨23972934585797912161286891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15981956390531941440857927 23972934585797912161286891)
  ·
    refine ⟨35959401878696868241930337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23972934585797912161286891 35959401878696868241930337)
    ·
      refine ⟨26969551409022651181447753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35959401878696868241930337 26969551409022651181447753)
      ·
        refine ⟨20227163556766988386085815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26969551409022651181447753 20227163556766988386085815)
        ·
          refine ⟨30340745335150482579128723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20227163556766988386085815 30340745335150482579128723)
          ·
            refine ⟨45511118002725723868693085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30340745335150482579128723 45511118002725723868693085)
            ·
              refine ⟨17066669251022146450759907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45511118002725723868693085 17066669251022146450759907)
              ·
                refine ⟨25600003876533219676139861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17066669251022146450759907 25600003876533219676139861)
                ·
                  refine ⟨75000011357030917019941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 25600003876533219676139861 75000011357030917019941)
                  ·
                    rfl

theorem cell22_657279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 10].length) (baseStart_657279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657279 prefixEnd_657279 := by exact prefixLift 657279
  have htrace : WordTrace (prefixWord ++ tailWord_657279) baseStart_657279 baseEnd_657279 := by
    simpa [prefixWord, tailWord_657279, baseEnd_657279] using wordTrace_append hprefix tailTrace_657279
  have hstable : (prefixWord ++ tailWord_657279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657279).length < 2 ^ (prefixWord ++ tailWord_657279).sum := by decide
  have hdescent : baseEnd_657279 < baseStart_657279 := by decide
  rcases family_descends (prefixWord ++ tailWord_657279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657341 : List Nat := [1, 4, 1, 2, 3, 1, 10]
def baseStart_657341 : Nat := 118140960795 + 657341 * 2 ^ 59
def prefixEnd_657341 : Nat := 4983230072969 + 3 ^ 40 * 657341 * 2
def baseEnd_657341 : Nat := 8334120664375750222579

theorem tailTrace_657341 : CollatzResearch.WordTrace tailWord_657341 prefixEnd_657341 8334120664375750222579 := by
  unfold tailWord_657341
  simp only [CollatzResearch.WordTrace]
  refine ⟨23975195911573296750043877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15983463941048864500029251 23975195911573296750043877)
  ·
    refine ⟨4495349233419993140633227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23975195911573296750043877 4495349233419993140633227)
    ·
      refine ⟨6743023850129989710949841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4495349233419993140633227 6743023850129989710949841)
      ·
        refine ⟨5057267887597492283212381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6743023850129989710949841 5057267887597492283212381)
        ·
          refine ⟨1896475457849059606204643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5057267887597492283212381 1896475457849059606204643)
          ·
            refine ⟨2844713186773589409306965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896475457849059606204643 2844713186773589409306965)
            ·
              refine ⟨8334120664375750222579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2844713186773589409306965 8334120664375750222579)
              ·
                rfl

theorem cell22_657341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 10].length) (baseStart_657341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657341 prefixEnd_657341 := by exact prefixLift 657341
  have htrace : WordTrace (prefixWord ++ tailWord_657341) baseStart_657341 baseEnd_657341 := by
    simpa [prefixWord, tailWord_657341, baseEnd_657341] using wordTrace_append hprefix tailTrace_657341
  have hstable : (prefixWord ++ tailWord_657341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657341).length < 2 ^ (prefixWord ++ tailWord_657341).sum := by decide
  have hdescent : baseEnd_657341 < baseStart_657341 := by decide
  rcases family_descends (prefixWord ++ tailWord_657341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657362 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_657362 : Nat := 118140960795 + 657362 * 2 ^ 59
def prefixEnd_657362 : Nat := 4983230072969 + 3 ^ 40 * 657362 * 2
def baseEnd_657362 : Nat := 225028446667308201234569

theorem tailTrace_657362 : CollatzResearch.WordTrace tailWord_657362 prefixEnd_657362 225028446667308201234569 := by
  unfold tailWord_657362
  simp only [CollatzResearch.WordTrace]
  refine ⟨5993990461124304334139585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15983974562998144891038893 5993990461124304334139585)
  ·
    refine ⟨4495492845843228250604689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5993990461124304334139585 4495492845843228250604689)
    ·
      refine ⟨3371619634382421187953517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4495492845843228250604689 3371619634382421187953517)
      ·
        refine ⟨1264357362893407945482569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3371619634382421187953517 1264357362893407945482569)
        ·
          refine ⟨948268022170055959111927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1264357362893407945482569 948268022170055959111927)
          ·
            refine ⟨1422402033255083938667891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948268022170055959111927 1422402033255083938667891)
            ·
              refine ⟨2133603049882625908001837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422402033255083938667891 2133603049882625908001837)
              ·
                refine ⟨800101143705984715500689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2133603049882625908001837 800101143705984715500689)
                ·
                  refine ⟨600075857779488536625517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 800101143705984715500689 600075857779488536625517)
                  ·
                    refine ⟨225028446667308201234569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 600075857779488536625517 225028446667308201234569)
                    ·
                      rfl

theorem cell22_657362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_657362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657362 prefixEnd_657362 := by exact prefixLift 657362
  have htrace : WordTrace (prefixWord ++ tailWord_657362) baseStart_657362 baseEnd_657362 := by
    simpa [prefixWord, tailWord_657362, baseEnd_657362] using wordTrace_append hprefix tailTrace_657362
  have hstable : (prefixWord ++ tailWord_657362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657362).length < 2 ^ (prefixWord ++ tailWord_657362).sum := by decide
  have hdescent : baseEnd_657362 < baseStart_657362 := by decide
  rcases family_descends (prefixWord ++ tailWord_657362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657433 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 1, 4]
def baseStart_657433 : Nat := 118140960795 + 657433 * 2 ^ 59
def prefixEnd_657433 : Nat := 4983230072969 + 3 ^ 40 * 657433 * 2
def baseEnd_657433 : Nat := 225052751418287682709351

theorem tailTrace_657433 : CollatzResearch.WordTrace tailWord_657433 prefixEnd_657433 225052751418287682709351 := by
  unfold tailWord_657433
  simp only [CollatzResearch.WordTrace]
  refine ⟨23978551427239996462392953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15985700951493330974928635 23978551427239996462392953)
  ·
    refine ⟨17983913570429997346794715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23978551427239996462392953 17983913570429997346794715)
    ·
      refine ⟨26975870355644996020192073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17983913570429997346794715 26975870355644996020192073)
      ·
        refine ⟨20231902766733747015144055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26975870355644996020192073 20231902766733747015144055)
        ·
          refine ⟨30347854150100620522716083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20231902766733747015144055 30347854150100620522716083)
          ·
            refine ⟨45521781225150930784074125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30347854150100620522716083 45521781225150930784074125)
            ·
              refine ⟨17070667959431599044027797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45521781225150930784074125 17070667959431599044027797)
              ·
                refine ⟨800187560598356205188803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17070667959431599044027797 800187560598356205188803)
                ·
                  refine ⟨1200281340897534307783205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800187560598356205188803 1200281340897534307783205)
                  ·
                    refine ⟨225052751418287682709351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1200281340897534307783205 225052751418287682709351)
                    ·
                      rfl

theorem cell22_657433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_657433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657433 prefixEnd_657433 := by exact prefixLift 657433
  have htrace : WordTrace (prefixWord ++ tailWord_657433) baseStart_657433 baseEnd_657433 := by
    simpa [prefixWord, tailWord_657433, baseEnd_657433] using wordTrace_append hprefix tailTrace_657433
  have hstable : (prefixWord ++ tailWord_657433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657433).length < 2 ^ (prefixWord ++ tailWord_657433).sum := by decide
  have hdescent : baseEnd_657433 < baseStart_657433 := by decide
  rcases family_descends (prefixWord ++ tailWord_657433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657465 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 6]
def baseStart_657465 : Nat := 118140960795 + 657465 * 2 ^ 59
def prefixEnd_657465 : Nat := 4983230072969 + 3 ^ 40 * 657465 * 2
def baseEnd_657465 : Nat := 75021235224083421969751

theorem tailTrace_657465 : CollatzResearch.WordTrace tailWord_657465 prefixEnd_657465 75021235224083421969751 := by
  unfold tailWord_657465
  simp only [CollatzResearch.WordTrace]
  refine ⟨23979718563124065927557849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15986479042082710618371899 23979718563124065927557849)
  ·
    refine ⟨17984788922343049445668387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23979718563124065927557849 17984788922343049445668387)
    ·
      refine ⟨26977183383514574168502581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17984788922343049445668387 26977183383514574168502581)
      ·
        refine ⟨2529110942204491328297117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26977183383514574168502581 2529110942204491328297117)
        ·
          refine ⟨948416603326684248111419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2529110942204491328297117 948416603326684248111419)
          ·
            refine ⟨1422624904990026372167129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948416603326684248111419 1422624904990026372167129)
            ·
              refine ⟨1066968678742519779125347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422624904990026372167129 1066968678742519779125347)
              ·
                refine ⟨1600453018113779668688021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066968678742519779125347 1600453018113779668688021)
                ·
                  refine ⟨75021235224083421969751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1600453018113779668688021 75021235224083421969751)
                  ·
                    rfl

theorem cell22_657465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_657465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657465 prefixEnd_657465 := by exact prefixLift 657465
  have htrace : WordTrace (prefixWord ++ tailWord_657465) baseStart_657465 baseEnd_657465 := by
    simpa [prefixWord, tailWord_657465, baseEnd_657465] using wordTrace_append hprefix tailTrace_657465
  have hstable : (prefixWord ++ tailWord_657465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657465).length < 2 ^ (prefixWord ++ tailWord_657465).sum := by decide
  have hdescent : baseEnd_657465 < baseStart_657465 := by decide
  rcases family_descends (prefixWord ++ tailWord_657465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657493 : List Nat := [1, 3, 2, 2, 1, 4, 1, 8]
def baseStart_657493 : Nat := 118140960795 + 657493 * 2 ^ 59
def prefixEnd_657493 : Nat := 4983230072969 + 3 ^ 40 * 657493 * 2
def baseEnd_657493 : Nat := 25008143404940836245463

theorem tailTrace_657493 : CollatzResearch.WordTrace tailWord_657493 prefixEnd_657493 25008143404940836245463 := by
  unfold tailWord_657493
  simp only [CollatzResearch.WordTrace]
  refine ⟨23980739807022626709577133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15987159871348417806384755 23980739807022626709577133)
  ·
    refine ⟨8992777427633485016091425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23980739807022626709577133 8992777427633485016091425)
    ·
      refine ⟨6744583070725113762068569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8992777427633485016091425 6744583070725113762068569)
      ·
        refine ⟨5058437303043835321551427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6744583070725113762068569 5058437303043835321551427)
        ·
          refine ⟨7587655954565752982327141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5058437303043835321551427 7587655954565752982327141)
          ·
            refine ⟨1422685491481078684186339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7587655954565752982327141 1422685491481078684186339)
            ·
              refine ⟨2134028237221618026279509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422685491481078684186339 2134028237221618026279509)
              ·
                refine ⟨25008143404940836245463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2134028237221618026279509 25008143404940836245463)
                ·
                  rfl

theorem cell22_657493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 8].length) (baseStart_657493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657493 prefixEnd_657493 := by exact prefixLift 657493
  have htrace : WordTrace (prefixWord ++ tailWord_657493) baseStart_657493 baseEnd_657493 := by
    simpa [prefixWord, tailWord_657493, baseEnd_657493] using wordTrace_append hprefix tailTrace_657493
  have hstable : (prefixWord ++ tailWord_657493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657493).length < 2 ^ (prefixWord ++ tailWord_657493).sum := by decide
  have hdescent : baseEnd_657493 < baseStart_657493 := by decide
  rcases family_descends (prefixWord ++ tailWord_657493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657572 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 5]
def baseStart_657572 : Nat := 118140960795 + 657572 * 2 ^ 59
def prefixEnd_657572 : Nat := 4983230072969 + 3 ^ 40 * 657572 * 2
def baseEnd_657572 : Nat := 75033444652979217827975

theorem tailTrace_657572 : CollatzResearch.WordTrace tailWord_657572 prefixEnd_657572 75033444652979217827975 := by
  unfold tailWord_657572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11991810586868211600851485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15989080782490948801135313 11991810586868211600851485)
  ·
    refine ⟨4496928970075579350319307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11991810586868211600851485 4496928970075579350319307)
    ·
      refine ⟨6745393455113369025478961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4496928970075579350319307 6745393455113369025478961)
      ·
        refine ⟨5059045091335026769109221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6745393455113369025478961 5059045091335026769109221)
        ·
          refine ⟨948570954625317519207979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5059045091335026769109221 948570954625317519207979)
          ·
            refine ⟨1422856431937976278811969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948570954625317519207979 1422856431937976278811969)
            ·
              refine ⟨1067142323953482209108977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422856431937976278811969 1067142323953482209108977)
              ·
                refine ⟨800356742965111656831733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067142323953482209108977 800356742965111656831733)
                ·
                  refine ⟨75033444652979217827975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 800356742965111656831733 75033444652979217827975)
                  ·
                    rfl

theorem cell22_657572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_657572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657572 prefixEnd_657572 := by exact prefixLift 657572
  have htrace : WordTrace (prefixWord ++ tailWord_657572) baseStart_657572 baseEnd_657572 := by
    simpa [prefixWord, tailWord_657572, baseEnd_657572] using wordTrace_append hprefix tailTrace_657572
  have hstable : (prefixWord ++ tailWord_657572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657572).length < 2 ^ (prefixWord ++ tailWord_657572).sum := by decide
  have hdescent : baseEnd_657572 < baseStart_657572 := by decide
  rcases family_descends (prefixWord ++ tailWord_657572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657583 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 6]
def baseStart_657583 : Nat := 118140960795 + 657583 * 2 ^ 59
def prefixEnd_657583 : Nat := 4983230072969 + 3 ^ 40 * 657583 * 2
def baseEnd_657583 : Nat := 75034699827912430486297

theorem tailTrace_657583 : CollatzResearch.WordTrace tailWord_657583 prefixEnd_657583 75034699827912430486297 := by
  unfold tailWord_657583
  simp only [CollatzResearch.WordTrace]
  refine ⟨23984022376696572080353403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15989348251131048053568935 23984022376696572080353403)
  ·
    refine ⟨35976033565044858120530105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23984022376696572080353403 35976033565044858120530105)
    ·
      refine ⟨26982025173783643590397579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35976033565044858120530105 26982025173783643590397579)
      ·
        refine ⟨40473037760675465385596369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26982025173783643590397579 40473037760675465385596369)
        ·
          refine ⟨30354778320506599039197277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40473037760675465385596369 30354778320506599039197277)
          ·
            refine ⟨11383041870189974639698979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30354778320506599039197277 11383041870189974639698979)
            ·
              refine ⟨17074562805284961959548469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11383041870189974639698979 17074562805284961959548469)
              ·
                refine ⟨1600740262995465183707669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17074562805284961959548469 1600740262995465183707669)
                ·
                  refine ⟨75034699827912430486297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1600740262995465183707669 75034699827912430486297)
                  ·
                    rfl

theorem cell22_657583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 6].length) (baseStart_657583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657583 prefixEnd_657583 := by exact prefixLift 657583
  have htrace : WordTrace (prefixWord ++ tailWord_657583) baseStart_657583 baseEnd_657583 := by
    simpa [prefixWord, tailWord_657583, baseEnd_657583] using wordTrace_append hprefix tailTrace_657583
  have hstable : (prefixWord ++ tailWord_657583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657583).length < 2 ^ (prefixWord ++ tailWord_657583).sum := by decide
  have hdescent : baseEnd_657583 < baseStart_657583 := by decide
  rcases family_descends (prefixWord ++ tailWord_657583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657600 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 6]
def baseStart_657600 : Nat := 118140960795 + 657600 * 2 ^ 59
def prefixEnd_657600 : Nat := 4983230072969 + 3 ^ 40 * 657600 * 2
def baseEnd_657600 : Nat := 75036639643718304594613

theorem tailTrace_657600 : CollatzResearch.WordTrace tailWord_657600 prefixEnd_657600 75036639643718304594613 := by
  unfold tailWord_657600
  simp only [CollatzResearch.WordTrace]
  refine ⟨11992321208817491991861127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15989761611756655989148169 11992321208817491991861127)
  ·
    refine ⟨17988481813226237987791691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11992321208817491991861127 17988481813226237987791691)
    ·
      refine ⟨26982722719839356981687537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17988481813226237987791691 26982722719839356981687537)
      ·
        refine ⟨20237042039879517736265653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26982722719839356981687537 20237042039879517736265653)
        ·
          refine ⟨1897222691238704787774905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20237042039879517736265653 1897222691238704787774905)
          ·
            refine ⟨1422917018429028590831179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897222691238704787774905 1422917018429028590831179)
            ·
              refine ⟨2134375527643542886246769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422917018429028590831179 2134375527643542886246769)
              ·
                refine ⟨1600781645732657164685077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2134375527643542886246769 1600781645732657164685077)
                ·
                  refine ⟨75036639643718304594613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1600781645732657164685077 75036639643718304594613)
                  ·
                    rfl

theorem cell22_657600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_657600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657600 prefixEnd_657600 := by exact prefixLift 657600
  have htrace : WordTrace (prefixWord ++ tailWord_657600) baseStart_657600 baseEnd_657600 := by
    simpa [prefixWord, tailWord_657600, baseEnd_657600] using wordTrace_append hprefix tailTrace_657600
  have hstable : (prefixWord ++ tailWord_657600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657600).length < 2 ^ (prefixWord ++ tailWord_657600).sum := by decide
  have hdescent : baseEnd_657600 < baseStart_657600 := by decide
  rcases family_descends (prefixWord ++ tailWord_657600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657615 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 4, 3]
def baseStart_657615 : Nat := 118140960795 + 657615 * 2 ^ 59
def prefixEnd_657615 : Nat := 4983230072969 + 3 ^ 40 * 657615 * 2
def baseEnd_657615 : Nat := 225115053737699874658793

theorem tailTrace_657615 : CollatzResearch.WordTrace tailWord_657615 prefixEnd_657615 225115053737699874658793 := by
  unfold tailWord_657615
  simp only [CollatzResearch.WordTrace]
  refine ⟨23985189512580641545518299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15990126341720427697012199 23985189512580641545518299)
  ·
    refine ⟨35977784268870962318277449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23985189512580641545518299 35977784268870962318277449)
    ·
      refine ⟨26983338201653221738708087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35977784268870962318277449 26983338201653221738708087)
      ·
        refine ⟨40475007302479832608062131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26983338201653221738708087 40475007302479832608062131)
        ·
          refine ⟨60712510953719748912093197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40475007302479832608062131 60712510953719748912093197)
          ·
            refine ⟨22767191607644905842034949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60712510953719748912093197 22767191607644905842034949)
            ·
              refine ⟨4268848426433419845381553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22767191607644905842034949 4268848426433419845381553)
              ·
                refine ⟨3201636319825064884036165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4268848426433419845381553 3201636319825064884036165)
                ·
                  refine ⟨600306809967199665756781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3201636319825064884036165 600306809967199665756781)
                  ·
                    refine ⟨225115053737699874658793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 600306809967199665756781 225115053737699874658793)
                    ·
                      rfl

theorem cell22_657615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 3].length) (baseStart_657615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657615 prefixEnd_657615 := by exact prefixLift 657615
  have htrace : WordTrace (prefixWord ++ tailWord_657615) baseStart_657615 baseEnd_657615 := by
    simpa [prefixWord, tailWord_657615, baseEnd_657615] using wordTrace_append hprefix tailTrace_657615
  have hstable : (prefixWord ++ tailWord_657615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657615).length < 2 ^ (prefixWord ++ tailWord_657615).sum := by decide
  have hdescent : baseEnd_657615 < baseStart_657615 := by decide
  rcases family_descends (prefixWord ++ tailWord_657615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657767 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 1, 5]
def baseStart_657767 : Nat := 118140960795 + 657767 * 2 ^ 59
def prefixEnd_657767 : Nat := 4983230072969 + 3 ^ 40 * 657767 * 2
def baseEnd_657767 : Nat := 225167086444022144858327

theorem tailTrace_657767 : CollatzResearch.WordTrace tailWord_657767 prefixEnd_657767 225167086444022144858327 := by
  unfold tailWord_657767
  simp only [CollatzResearch.WordTrace]
  refine ⟨23990733408029971505051555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15993822272019981003367703 23990733408029971505051555)
  ·
    refine ⟨35986100112044957257577333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23990733408029971505051555 35986100112044957257577333)
    ·
      refine ⟨3373696885504214742897875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35986100112044957257577333 3373696885504214742897875)
      ·
        refine ⟨5060545328256322114346813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3373696885504214742897875 5060545328256322114346813)
        ·
          refine ⟨1897704498096120792880055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5060545328256322114346813 1897704498096120792880055)
          ·
            refine ⟨2846556747144181189320083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897704498096120792880055 2846556747144181189320083)
            ·
              refine ⟨4269835120716271783980125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846556747144181189320083 4269835120716271783980125)
              ·
                refine ⟨1601188170268601918992547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4269835120716271783980125 1601188170268601918992547)
                ·
                  refine ⟨2401782255402902878488821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601188170268601918992547 2401782255402902878488821)
                  ·
                    refine ⟨225167086444022144858327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2401782255402902878488821 225167086444022144858327)
                    ·
                      rfl

theorem cell22_657767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_657767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657767 prefixEnd_657767 := by exact prefixLift 657767
  have htrace : WordTrace (prefixWord ++ tailWord_657767) baseStart_657767 baseEnd_657767 := by
    simpa [prefixWord, tailWord_657767, baseEnd_657767] using wordTrace_append hprefix tailTrace_657767
  have hstable : (prefixWord ++ tailWord_657767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657767).length < 2 ^ (prefixWord ++ tailWord_657767).sum := by decide
  have hdescent : baseEnd_657767 < baseStart_657767 := by decide
  rcases family_descends (prefixWord ++ tailWord_657767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657801 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 2, 3]
def baseStart_657801 : Nat := 118140960795 + 657801 * 2 ^ 59
def prefixEnd_657801 : Nat := 4983230072969 + 3 ^ 40 * 657801 * 2
def baseEnd_657801 : Nat := 225178725338857389508223

theorem tailTrace_657801 : CollatzResearch.WordTrace tailWord_657801 prefixEnd_657801 225178725338857389508223 := by
  unfold tailWord_657801
  simp only [CollatzResearch.WordTrace]
  refine ⟨23991973489906795311789257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15994648993271196874526171 23991973489906795311789257)
  ·
    refine ⟨17993980117430096483841943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23991973489906795311789257 17993980117430096483841943)
    ·
      refine ⟨26990970176145144725762915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17993980117430096483841943 26990970176145144725762915)
      ·
        refine ⟨40486455264217717088644373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26990970176145144725762915 40486455264217717088644373)
        ·
          refine ⟨1897802590510205488530205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40486455264217717088644373 1897802590510205488530205)
          ·
            refine ⟨711675971441327058198827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1897802590510205488530205 711675971441327058198827)
            ·
              refine ⟨1067513957161990587298241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711675971441327058198827 1067513957161990587298241)
              ·
                refine ⟨800635467871492940473681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067513957161990587298241 800635467871492940473681)
                ·
                  refine ⟨600476600903619705355261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 800635467871492940473681 600476600903619705355261)
                  ·
                    refine ⟨225178725338857389508223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 600476600903619705355261 225178725338857389508223)
                    ·
                      rfl

theorem cell22_657801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 3].length) (baseStart_657801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657801 prefixEnd_657801 := by exact prefixLift 657801
  have htrace : WordTrace (prefixWord ++ tailWord_657801) baseStart_657801 baseEnd_657801 := by
    simpa [prefixWord, tailWord_657801, baseEnd_657801] using wordTrace_append hprefix tailTrace_657801
  have hstable : (prefixWord ++ tailWord_657801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657801).length < 2 ^ (prefixWord ++ tailWord_657801).sum := by decide
  have hdescent : baseEnd_657801 < baseStart_657801 := by decide
  rcases family_descends (prefixWord ++ tailWord_657801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657863 : List Nat := [1, 1, 4, 1, 1, 5, 3, 2, 1, 3]
def baseStart_657863 : Nat := 118140960795 + 657863 * 2 ^ 59
def prefixEnd_657863 : Nat := 4983230072969 + 3 ^ 40 * 657863 * 2
def baseEnd_657863 : Nat := 225199949205909894458033

theorem tailTrace_657863 : CollatzResearch.WordTrace tailWord_657863 prefixEnd_657863 225199949205909894458033 := by
  unfold tailWord_657863
  simp only [CollatzResearch.WordTrace]
  refine ⟨23994234815682179900546243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15996156543788119933697495 23994234815682179900546243)
  ·
    refine ⟨35991352223523269850819365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23994234815682179900546243 35991352223523269850819365)
    ·
      refine ⟨6748378541910613097028631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35991352223523269850819365 6748378541910613097028631)
      ·
        refine ⟨10122567812865919645542947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6748378541910613097028631 10122567812865919645542947)
        ·
          refine ⟨15183851719298879468314421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10122567812865919645542947 15183851719298879468314421)
          ·
            refine ⟨1423486098684269950154477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15183851719298879468314421 1423486098684269950154477)
            ·
              refine ⟨533807287006601231307929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1423486098684269950154477 533807287006601231307929)
              ·
                refine ⟨400355465254950923480947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533807287006601231307929 400355465254950923480947)
                ·
                  refine ⟨600533197882426385221421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400355465254950923480947 600533197882426385221421)
                  ·
                    refine ⟨225199949205909894458033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 600533197882426385221421 225199949205909894458033)
                    ·
                      rfl

theorem cell22_657863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_657863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657863 prefixEnd_657863 := by exact prefixLift 657863
  have htrace : WordTrace (prefixWord ++ tailWord_657863) baseStart_657863 baseEnd_657863 := by
    simpa [prefixWord, tailWord_657863, baseEnd_657863] using wordTrace_append hprefix tailTrace_657863
  have hstable : (prefixWord ++ tailWord_657863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657863).length < 2 ^ (prefixWord ++ tailWord_657863).sum := by decide
  have hdescent : baseEnd_657863 < baseStart_657863 := by decide
  rcases family_descends (prefixWord ++ tailWord_657863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657876 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 5]
def baseStart_657876 : Nat := 118140960795 + 657876 * 2 ^ 59
def prefixEnd_657876 : Nat := 4983230072969 + 3 ^ 40 * 657876 * 2
def baseEnd_657876 : Nat := 75068133123860731294331

theorem tailTrace_657876 : CollatzResearch.WordTrace tailWord_657876 prefixEnd_657876 75068133123860731294331 := by
  unfold tailWord_657876
  simp only [CollatzResearch.WordTrace]
  refine ⟨11997354482317541560384741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15996472643090055413846321 11997354482317541560384741)
  ·
    refine ⟨2249503965434539042572139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11997354482317541560384741 2249503965434539042572139)
    ·
      refine ⟨3374255948151808563858209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2249503965434539042572139 3374255948151808563858209)
      ·
        refine ⟨2530691961113856422893657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3374255948151808563858209 2530691961113856422893657)
        ·
          refine ⟨1898018970835392317170243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2530691961113856422893657 1898018970835392317170243)
          ·
            refine ⟨2847028456253088475755365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898018970835392317170243 2847028456253088475755365)
            ·
              refine ⟨533817835547454089204131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2847028456253088475755365 533817835547454089204131)
              ·
                refine ⟨800726753321181133806197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533817835547454089204131 800726753321181133806197)
                ·
                  refine ⟨75068133123860731294331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 800726753321181133806197 75068133123860731294331)
                  ·
                    rfl

theorem cell22_657876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_657876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657876 prefixEnd_657876 := by exact prefixLift 657876
  have htrace : WordTrace (prefixWord ++ tailWord_657876) baseStart_657876 baseEnd_657876 := by
    simpa [prefixWord, tailWord_657876, baseEnd_657876] using wordTrace_append hprefix tailTrace_657876
  have hstable : (prefixWord ++ tailWord_657876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657876).length < 2 ^ (prefixWord ++ tailWord_657876).sum := by decide
  have hdescent : baseEnd_657876 < baseStart_657876 := by decide
  rcases family_descends (prefixWord ++ tailWord_657876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657904 : List Nat := [2, 1, 1, 1, 3, 3, 2, 5, 4]
def baseStart_657904 : Nat := 118140960795 + 657904 * 2 ^ 59
def prefixEnd_657904 : Nat := 4983230072969 + 3 ^ 40 * 657904 * 2
def baseEnd_657904 : Nat := 75071328114599818060969

theorem tailTrace_657904 : CollatzResearch.WordTrace tailWord_657904 prefixEnd_657904 75071328114599818060969 := by
  unfold tailWord_657904
  simp only [CollatzResearch.WordTrace]
  refine ⟨11997865104266821951394383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15997153472355762601859177 11997865104266821951394383)
  ·
    refine ⟨17996797656400232927091575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11997865104266821951394383 17996797656400232927091575)
    ·
      refine ⟨26995196484600349390637363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17996797656400232927091575 26995196484600349390637363)
      ·
        refine ⟨40492794726900524085956045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26995196484600349390637363 40492794726900524085956045)
        ·
          refine ⟨15184798022587696532233517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40492794726900524085956045 15184798022587696532233517)
          ·
            refine ⟨5694299258470386199587569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15184798022587696532233517 5694299258470386199587569)
            ·
              refine ⟨4270724443852789649690677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5694299258470386199587569 4270724443852789649690677)
              ·
                refine ⟨400380416611199029658501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4270724443852789649690677 400380416611199029658501)
                ·
                  refine ⟨75071328114599818060969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400380416611199029658501 75071328114599818060969)
                  ·
                    rfl

theorem cell22_657904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 4].length) (baseStart_657904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657904 prefixEnd_657904 := by exact prefixLift 657904
  have htrace : WordTrace (prefixWord ++ tailWord_657904) baseStart_657904 baseEnd_657904 := by
    simpa [prefixWord, tailWord_657904, baseEnd_657904] using wordTrace_append hprefix tailTrace_657904
  have hstable : (prefixWord ++ tailWord_657904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657904).length < 2 ^ (prefixWord ++ tailWord_657904).sum := by decide
  have hdescent : baseEnd_657904 < baseStart_657904 := by decide
  rcases family_descends (prefixWord ++ tailWord_657904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657921 : List Nat := [1, 2, 4, 1, 3, 2, 1, 4, 4]
def baseStart_657921 : Nat := 118140960795 + 657921 * 2 ^ 59
def prefixEnd_657921 : Nat := 4983230072969 + 3 ^ 40 * 657921 * 2
def baseEnd_657921 : Nat := 75073267930405692169285

theorem tailTrace_657921 : CollatzResearch.WordTrace tailWord_657921 prefixEnd_657921 75073267930405692169285 := by
  unfold tailWord_657921
  simp only [CollatzResearch.WordTrace]
  refine ⟨23996350249472055806157617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15997566832981370537438411 23996350249472055806157617)
  ·
    refine ⟨17997262687104041854618213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23996350249472055806157617 17997262687104041854618213)
    ·
      refine ⟨3374486753832007847740915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17997262687104041854618213 3374486753832007847740915)
      ·
        refine ⟨5061730130748011771611373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374486753832007847740915 5061730130748011771611373)
        ·
          refine ⟨1898148799030504414354265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5061730130748011771611373 1898148799030504414354265)
          ·
            refine ⟨1423611599272878310765699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1898148799030504414354265 1423611599272878310765699)
            ·
              refine ⟨2135417398909317466148549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423611599272878310765699 2135417398909317466148549)
              ·
                refine ⟨400390762295497024902853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2135417398909317466148549 400390762295497024902853)
                ·
                  refine ⟨75073267930405692169285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400390762295497024902853 75073267930405692169285)
                  ·
                    rfl

theorem cell22_657921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 4].length) (baseStart_657921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657921 prefixEnd_657921 := by exact prefixLift 657921
  have htrace : WordTrace (prefixWord ++ tailWord_657921) baseStart_657921 baseEnd_657921 := by
    simpa [prefixWord, tailWord_657921, baseEnd_657921] using wordTrace_append hprefix tailTrace_657921
  have hstable : (prefixWord ++ tailWord_657921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657921).length < 2 ^ (prefixWord ++ tailWord_657921).sum := by decide
  have hdescent : baseEnd_657921 < baseStart_657921 := by decide
  rcases family_descends (prefixWord ++ tailWord_657921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657981 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_657981 : Nat := 118140960795 + 657981 * 2 ^ 59
def prefixEnd_657981 : Nat := 4983230072969 + 3 ^ 40 * 657981 * 2
def baseEnd_657981 : Nat := 225240343017396920007671

theorem tailTrace_657981 : CollatzResearch.WordTrace tailWord_657981 prefixEnd_657981 225240343017396920007671 := by
  unfold tailWord_657981
  simp only [CollatzResearch.WordTrace]
  refine ⟨23998538629254686053341797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15999025752836457368894531 23998538629254686053341797)
  ·
    refine ⟨4499725992985253635001587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23998538629254686053341797 4499725992985253635001587)
    ·
      refine ⟨6749588989477880452502381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4499725992985253635001587 6749588989477880452502381)
      ·
        refine ⟨2531095871054205169688393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6749588989477880452502381 2531095871054205169688393)
        ·
          refine ⟨1898321903290653877266295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2531095871054205169688393 1898321903290653877266295)
          ·
            refine ⟨2847482854935980815899443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898321903290653877266295 2847482854935980815899443)
            ·
              refine ⟨4271224282403971223849165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847482854935980815899443 4271224282403971223849165)
              ·
                refine ⟨1601709105901489208943437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4271224282403971223849165 1601709105901489208943437)
                ·
                  refine ⟨600640914713058453353789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1601709105901489208943437 600640914713058453353789)
                  ·
                    refine ⟨225240343017396920007671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 600640914713058453353789 225240343017396920007671)
                    ·
                      rfl

theorem cell22_657981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_657981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_657981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_657981 prefixEnd_657981 := by exact prefixLift 657981
  have htrace : WordTrace (prefixWord ++ tailWord_657981) baseStart_657981 baseEnd_657981 := by
    simpa [prefixWord, tailWord_657981, baseEnd_657981] using wordTrace_append hprefix tailTrace_657981
  have hstable : (prefixWord ++ tailWord_657981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657981).length < 2 ^ (prefixWord ++ tailWord_657981).sum := by decide
  have hdescent : baseEnd_657981 < baseStart_657981 := by decide
  rcases family_descends (prefixWord ++ tailWord_657981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658039 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 6]
def baseStart_658039 : Nat := 118140960795 + 658039 * 2 ^ 59
def prefixEnd_658039 : Nat := 4983230072969 + 3 ^ 40 * 658039 * 2
def baseEnd_658039 : Nat := 75086732534234700685831

theorem tailTrace_658039 : CollatzResearch.WordTrace tailWord_658039 prefixEnd_658039 75086732534234700685831 := by
  unfold tailWord_658039
  simp only [CollatzResearch.WordTrace]
  refine ⟨24000654063044561958953171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16000436042029707972635447 24000654063044561958953171)
  ·
    refine ⟨36000981094566842938429757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24000654063044561958953171 36000981094566842938429757)
    ·
      refine ⟨13500367910462566101911159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36000981094566842938429757 13500367910462566101911159)
      ·
        refine ⟨20250551865693849152866739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13500367910462566101911159 20250551865693849152866739)
        ·
          refine ⟨30375827798540773729300109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20250551865693849152866739 30375827798540773729300109)
          ·
            refine ⟨11390935424452790148487541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30375827798540773729300109 11390935424452790148487541)
            ·
              refine ⟨1067900196042449076420707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11390935424452790148487541 1067900196042449076420707)
              ·
                refine ⟨1601850294063673614631061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067900196042449076420707 1601850294063673614631061)
                ·
                  refine ⟨75086732534234700685831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1601850294063673614631061 75086732534234700685831)
                  ·
                    rfl

theorem cell22_658039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 6].length) (baseStart_658039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658039 prefixEnd_658039 := by exact prefixLift 658039
  have htrace : WordTrace (prefixWord ++ tailWord_658039) baseStart_658039 baseEnd_658039 := by
    simpa [prefixWord, tailWord_658039, baseEnd_658039] using wordTrace_append hprefix tailTrace_658039
  have hstable : (prefixWord ++ tailWord_658039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658039).length < 2 ^ (prefixWord ++ tailWord_658039).sum := by decide
  have hdescent : baseEnd_658039 < baseStart_658039 := by decide
  rcases family_descends (prefixWord ++ tailWord_658039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658045 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 5]
def baseStart_658045 : Nat := 118140960795 + 658045 * 2 ^ 59
def prefixEnd_658045 : Nat := 4983230072969 + 3 ^ 40 * 658045 * 2
def baseEnd_658045 : Nat := 75087417175107362135825

theorem tailTrace_658045 : CollatzResearch.WordTrace tailWord_658045 prefixEnd_658045 75087417175107362135825 := by
  unfold tailWord_658045
  simp only [CollatzResearch.WordTrace]
  refine ⟨24000872901022824983671589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16000581934015216655781059 24000872901022824983671589)
  ·
    refine ⟨4500163668941779684438423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24000872901022824983671589 4500163668941779684438423)
    ·
      refine ⟨6750245503412669526657635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4500163668941779684438423 6750245503412669526657635)
      ·
        refine ⟨10125368255119004289986453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6750245503412669526657635 10125368255119004289986453)
        ·
          refine ⟨474626636958703326093115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10125368255119004289986453 474626636958703326093115)
          ·
            refine ⟨711939955438054989139673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474626636958703326093115 711939955438054989139673)
            ·
              refine ⟨533954966578541241854755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711939955438054989139673 533954966578541241854755)
              ·
                refine ⟨800932449867811862782133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533954966578541241854755 800932449867811862782133)
                ·
                  refine ⟨75087417175107362135825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 800932449867811862782133 75087417175107362135825)
                  ·
                    rfl

theorem cell22_658045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_658045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658045 prefixEnd_658045 := by exact prefixLift 658045
  have htrace : WordTrace (prefixWord ++ tailWord_658045) baseStart_658045 baseEnd_658045 := by
    simpa [prefixWord, tailWord_658045, baseEnd_658045] using wordTrace_append hprefix tailTrace_658045
  have hstable : (prefixWord ++ tailWord_658045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658045).length < 2 ^ (prefixWord ++ tailWord_658045).sum := by decide
  have hdescent : baseEnd_658045 < baseStart_658045 := by decide
  rcases family_descends (prefixWord ++ tailWord_658045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658101 : List Nat := [1, 3, 3, 3, 1, 1, 3, 7]
def baseStart_658101 : Nat := 118140960795 + 658101 * 2 ^ 59
def prefixEnd_658101 : Nat := 4983230072969 + 3 ^ 40 * 658101 * 2
def baseEnd_658101 : Nat := 25031269052195178556367

theorem tailTrace_658101 : CollatzResearch.WordTrace tailWord_658101 prefixEnd_658101 25031269052195178556367 := by
  unfold tailWord_658101
  simp only [CollatzResearch.WordTrace]
  refine ⟨24002915388819946547710157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16001943592546631031806771 24002915388819946547710157)
  ·
    refine ⟨9001093270807479955391309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24002915388819946547710157 9001093270807479955391309)
    ·
      refine ⟨3375409976552804983271741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9001093270807479955391309 3375409976552804983271741)
      ·
        refine ⟨1265778741207301868726903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3375409976552804983271741 1265778741207301868726903)
        ·
          refine ⟨1898668111810952803090355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265778741207301868726903 1898668111810952803090355)
          ·
            refine ⟨2848002167716429204635533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898668111810952803090355 2848002167716429204635533)
            ·
              refine ⟨1068000812893660951738325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2848002167716429204635533 1068000812893660951738325)
              ·
                refine ⟨25031269052195178556367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1068000812893660951738325 25031269052195178556367)
                ·
                  rfl

theorem cell22_658101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 7].length) (baseStart_658101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658101 prefixEnd_658101 := by exact prefixLift 658101
  have htrace : WordTrace (prefixWord ++ tailWord_658101) baseStart_658101 baseEnd_658101 := by
    simpa [prefixWord, tailWord_658101, baseEnd_658101] using wordTrace_append hprefix tailTrace_658101
  have hstable : (prefixWord ++ tailWord_658101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658101).length < 2 ^ (prefixWord ++ tailWord_658101).sum := by decide
  have hdescent : baseEnd_658101 < baseStart_658101 := by decide
  rcases family_descends (prefixWord ++ tailWord_658101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658129 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 7]
def baseStart_658129 : Nat := 118140960795 + 658129 * 2 ^ 59
def prefixEnd_658129 : Nat := 4983230072969 + 3 ^ 40 * 658129 * 2
def baseEnd_658129 : Nat := 75097002147324622435739

theorem tailTrace_658129 : CollatzResearch.WordTrace tailWord_658129 prefixEnd_658129 75097002147324622435739 := by
  unfold tailWord_658129
  simp only [CollatzResearch.WordTrace]
  refine ⟨24003936632718507329729441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16002624421812338219819627 24003936632718507329729441)
  ·
    refine ⟨18002952474538880497297081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24003936632718507329729441 18002952474538880497297081)
    ·
      refine ⟨13502214355904160372972811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18002952474538880497297081 13502214355904160372972811)
      ·
        refine ⟨20253321533856240559459217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13502214355904160372972811 20253321533856240559459217)
        ·
          refine ⟨15189991150392180419594413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20253321533856240559459217 15189991150392180419594413)
          ·
            refine ⟨5696246681397067657347905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15189991150392180419594413 5696246681397067657347905)
            ·
              refine ⟨4272185011047800743010929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5696246681397067657347905 4272185011047800743010929)
              ·
                refine ⟨3204138758285850557258197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4272185011047800743010929 3204138758285850557258197)
                ·
                  refine ⟨75097002147324622435739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3204138758285850557258197 75097002147324622435739)
                  ·
                    rfl

theorem cell22_658129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_658129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658129 prefixEnd_658129 := by exact prefixLift 658129
  have htrace : WordTrace (prefixWord ++ tailWord_658129) baseStart_658129 baseEnd_658129 := by
    simpa [prefixWord, tailWord_658129, baseEnd_658129] using wordTrace_append hprefix tailTrace_658129
  have hstable : (prefixWord ++ tailWord_658129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658129).length < 2 ^ (prefixWord ++ tailWord_658129).sum := by decide
  have hdescent : baseEnd_658129 < baseStart_658129 := by decide
  rcases family_descends (prefixWord ++ tailWord_658129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658208 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 6]
def baseStart_658208 : Nat := 118140960795 + 658208 * 2 ^ 59
def prefixEnd_658208 : Nat := 4983230072969 + 3 ^ 40 * 658208 * 2
def baseEnd_658208 : Nat := 75106016585481331527325

theorem tailTrace_658208 : CollatzResearch.WordTrace tailWord_658208 prefixEnd_658208 75106016585481331527325 := by
  unfold tailWord_658208
  simp only [CollatzResearch.WordTrace]
  refine ⟨12003408999716151910927639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16004545332954869214570185 12003408999716151910927639)
  ·
    refine ⟨18005113499574227866391459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12003408999716151910927639 18005113499574227866391459)
    ·
      refine ⟨27007670249361341799587189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18005113499574227866391459 27007670249361341799587189)
      ·
        refine ⟨2531969085877625793711299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27007670249361341799587189 2531969085877625793711299)
        ·
          refine ⟨3797953628816438690566949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2531969085877625793711299 3797953628816438690566949)
          ·
            refine ⟨712116305403082254481303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3797953628816438690566949 712116305403082254481303)
            ·
              refine ⟨1068174458104623381721955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712116305403082254481303 1068174458104623381721955)
              ·
                refine ⟨1602261687156935072582933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068174458104623381721955 1602261687156935072582933)
                ·
                  refine ⟨75106016585481331527325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1602261687156935072582933 75106016585481331527325)
                  ·
                    rfl

theorem cell22_658208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 6].length) (baseStart_658208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658208 prefixEnd_658208 := by exact prefixLift 658208
  have htrace : WordTrace (prefixWord ++ tailWord_658208) baseStart_658208 baseEnd_658208 := by
    simpa [prefixWord, tailWord_658208, baseEnd_658208] using wordTrace_append hprefix tailTrace_658208
  have hstable : (prefixWord ++ tailWord_658208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658208).length < 2 ^ (prefixWord ++ tailWord_658208).sum := by decide
  have hdescent : baseEnd_658208 < baseStart_658208 := by decide
  rcases family_descends (prefixWord ++ tailWord_658208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658219 : List Nat := [1, 1, 1, 1, 2, 1, 2, 13]
def baseStart_658219 : Nat := 118140960795 + 658219 * 2 ^ 59
def prefixEnd_658219 : Nat := 4983230072969 + 3 ^ 40 * 658219 * 2
def baseEnd_658219 : Nat := 25035757253471514728549

theorem tailTrace_658219 : CollatzResearch.WordTrace tailWord_658219 prefixEnd_658219 25035757253471514728549 := by
  unfold tailWord_658219
  simp only [CollatzResearch.WordTrace]
  refine ⟨24007219202392452700505711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16004812801594968467003807 24007219202392452700505711)
  ·
    refine ⟨36010828803588679050758567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24007219202392452700505711 36010828803588679050758567)
    ·
      refine ⟨54016243205383018576137851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36010828803588679050758567 54016243205383018576137851)
      ·
        refine ⟨81024364808074527864206777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54016243205383018576137851 81024364808074527864206777)
        ·
          refine ⟨60768273606055895898155083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81024364808074527864206777 60768273606055895898155083)
          ·
            refine ⟨91152410409083843847232625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60768273606055895898155083 91152410409083843847232625)
            ·
              refine ⟨68364307806812882885424469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91152410409083843847232625 68364307806812882885424469)
              ·
                refine ⟨25035757253471514728549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 68364307806812882885424469 25035757253471514728549)
                ·
                  rfl

theorem cell22_658219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 13].length) (baseStart_658219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658219 prefixEnd_658219 := by exact prefixLift 658219
  have htrace : WordTrace (prefixWord ++ tailWord_658219) baseStart_658219 baseEnd_658219 := by
    simpa [prefixWord, tailWord_658219, baseEnd_658219] using wordTrace_append hprefix tailTrace_658219
  have hstable : (prefixWord ++ tailWord_658219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658219).length < 2 ^ (prefixWord ++ tailWord_658219).sum := by decide
  have hdescent : baseEnd_658219 < baseStart_658219 := by decide
  rcases family_descends (prefixWord ++ tailWord_658219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658244 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_658244 : Nat := 118140960795 + 658244 * 2 ^ 59
def prefixEnd_658244 : Nat := 4983230072969 + 3 ^ 40 * 658244 * 2
def baseEnd_658244 : Nat := 225330373292151900681865

theorem tailTrace_658244 : CollatzResearch.WordTrace tailWord_658244 prefixEnd_658244 225330373292151900681865 := by
  unfold tailWord_658244
  simp only [CollatzResearch.WordTrace]
  refine ⟨12004065513650940985082893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16005420684867921313443857 12004065513650940985082893)
  ·
    refine ⟨4501524567619102869406085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12004065513650940985082893 4501524567619102869406085)
    ·
      refine ⟨844035856428581788013641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4501524567619102869406085 844035856428581788013641)
      ·
        refine ⟨633026892321436341010231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 844035856428581788013641 633026892321436341010231)
        ·
          refine ⟨949540338482154511515347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633026892321436341010231 949540338482154511515347)
          ·
            refine ⟨1424310507723231767273021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949540338482154511515347 1424310507723231767273021)
            ·
              refine ⟨534116440396211912727383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1424310507723231767273021 534116440396211912727383)
              ·
                refine ⟨801174660594317869091075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534116440396211912727383 801174660594317869091075)
                ·
                  refine ⟨1201761990891476803636613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801174660594317869091075 1201761990891476803636613)
                  ·
                    refine ⟨225330373292151900681865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1201761990891476803636613 225330373292151900681865)
                    ·
                      rfl

theorem cell22_658244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_658244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658244 prefixEnd_658244 := by exact prefixLift 658244
  have htrace : WordTrace (prefixWord ++ tailWord_658244) baseStart_658244 baseEnd_658244 := by
    simpa [prefixWord, tailWord_658244, baseEnd_658244] using wordTrace_append hprefix tailTrace_658244
  have hstable : (prefixWord ++ tailWord_658244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658244).length < 2 ^ (prefixWord ++ tailWord_658244).sum := by decide
  have hdescent : baseEnd_658244 < baseStart_658244 := by decide
  rcases family_descends (prefixWord ++ tailWord_658244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658253 : List Nat := [1, 6, 1, 2, 2, 10]
def baseStart_658253 : Nat := 118140960795 + 658253 * 2 ^ 59
def prefixEnd_658253 : Nat := 4983230072969 + 3 ^ 40 * 658253 * 2
def baseEnd_658253 : Nat := 2781894496000973792677

theorem tailTrace_658253 : CollatzResearch.WordTrace tailWord_658253 prefixEnd_658253 2781894496000973792677 := by
  unfold tailWord_658253
  simp only [CollatzResearch.WordTrace]
  refine ⟨24008459284269276507243413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16005639522846184338162275 24008459284269276507243413)
  ·
    refine ⟨1125396528950122336277035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24008459284269276507243413 1125396528950122336277035)
    ·
      refine ⟨1688094793425183504415553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125396528950122336277035 1688094793425183504415553)
      ·
        refine ⟨1266071095068887628311665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1688094793425183504415553 1266071095068887628311665)
        ·
          refine ⟨949553321301665721233749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1266071095068887628311665 949553321301665721233749)
          ·
            refine ⟨2781894496000973792677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 949553321301665721233749 2781894496000973792677)
            ·
              rfl

theorem cell22_658253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 10].length) (baseStart_658253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658253 prefixEnd_658253 := by exact prefixLift 658253
  have htrace : WordTrace (prefixWord ++ tailWord_658253) baseStart_658253 baseEnd_658253 := by
    simpa [prefixWord, tailWord_658253, baseEnd_658253] using wordTrace_append hprefix tailTrace_658253
  have hstable : (prefixWord ++ tailWord_658253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658253).length < 2 ^ (prefixWord ++ tailWord_658253).sum := by decide
  have hdescent : baseEnd_658253 < baseStart_658253 := by decide
  rcases family_descends (prefixWord ++ tailWord_658253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658266 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_658266 : Nat := 118140960795 + 658266 * 2 ^ 59
def prefixEnd_658266 : Nat := 4983230072969 + 3 ^ 40 * 658266 * 2
def baseEnd_658266 : Nat := 225337904341751176631797

theorem tailTrace_658266 : CollatzResearch.WordTrace tailWord_658266 prefixEnd_658266 225337904341751176631797 := by
  unfold tailWord_658266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6002233358305544931866663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16005955622148119818311101 6002233358305544931866663)
  ·
    refine ⟨9003350037458317397799995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6002233358305544931866663 9003350037458317397799995)
    ·
      refine ⟨13505025056187476096699993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9003350037458317397799995 13505025056187476096699993)
      ·
        refine ⟨10128768792140607072524995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13505025056187476096699993 10128768792140607072524995)
        ·
          refine ⟨15193153188210910608787493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10128768792140607072524995 15193153188210910608787493)
          ·
            refine ⟨2848716222789545739147655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15193153188210910608787493 2848716222789545739147655)
            ·
              refine ⟨4273074334184318608721483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848716222789545739147655 4273074334184318608721483)
              ·
                refine ⟨6409611501276477913082225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273074334184318608721483 6409611501276477913082225)
                ·
                  refine ⟨4807208625957358434811669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6409611501276477913082225 4807208625957358434811669)
                  ·
                    refine ⟨225337904341751176631797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4807208625957358434811669 225337904341751176631797)
                    ·
                      rfl

theorem cell22_658266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_658266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658266 prefixEnd_658266 := by exact prefixLift 658266
  have htrace : WordTrace (prefixWord ++ tailWord_658266) baseStart_658266 baseEnd_658266 := by
    simpa [prefixWord, tailWord_658266, baseEnd_658266] using wordTrace_append hprefix tailTrace_658266
  have hstable : (prefixWord ++ tailWord_658266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658266).length < 2 ^ (prefixWord ++ tailWord_658266).sum := by decide
  have hdescent : baseEnd_658266 < baseStart_658266 := by decide
  rcases family_descends (prefixWord ++ tailWord_658266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658332 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 5]
def baseStart_658332 : Nat := 118140960795 + 658332 * 2 ^ 59
def prefixEnd_658332 : Nat := 4983230072969 + 3 ^ 40 * 658332 * 2
def baseEnd_658332 : Nat := 75120165830183001493865

theorem tailTrace_658332 : CollatzResearch.WordTrace tailWord_658332 prefixEnd_658332 75120165830183001493865 := by
  unfold tailWord_658332
  simp only [CollatzResearch.WordTrace]
  refine ⟨12005670325491536499684625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16007560433988715332912833 12005670325491536499684625)
  ·
    refine ⟨9004252744118652374763469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12005670325491536499684625 9004252744118652374763469)
    ·
      refine ⟨3376594779044494640536301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9004252744118652374763469 3376594779044494640536301)
      ·
        refine ⟨1266223042141685490201113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3376594779044494640536301 1266223042141685490201113)
        ·
          refine ⟨949667281606264117650835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1266223042141685490201113 949667281606264117650835)
          ·
            refine ⟨1424500922409396176476253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949667281606264117650835 1424500922409396176476253)
            ·
              refine ⟨534187845903523566178595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1424500922409396176476253 534187845903523566178595)
              ·
                refine ⟨801281768855285349267893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534187845903523566178595 801281768855285349267893)
                ·
                  refine ⟨75120165830183001493865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 801281768855285349267893 75120165830183001493865)
                  ·
                    rfl

theorem cell22_658332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_658332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658332 prefixEnd_658332 := by exact prefixLift 658332
  have htrace : WordTrace (prefixWord ++ tailWord_658332) baseStart_658332 baseEnd_658332 := by
    simpa [prefixWord, tailWord_658332, baseEnd_658332] using wordTrace_append hprefix tailTrace_658332
  have hstable : (prefixWord ++ tailWord_658332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658332).length < 2 ^ (prefixWord ++ tailWord_658332).sum := by decide
  have hdescent : baseEnd_658332 < baseStart_658332 := by decide
  rcases family_descends (prefixWord ++ tailWord_658332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658360 : List Nat := [2, 1, 2, 1, 2, 4, 3, 3, 4]
def baseStart_658360 : Nat := 118140960795 + 658360 * 2 ^ 59
def prefixEnd_658360 : Nat := 4983230072969 + 3 ^ 40 * 658360 * 2
def baseEnd_658360 : Nat := 75123360820922088260503

theorem tailTrace_658360 : CollatzResearch.WordTrace tailWord_658360 prefixEnd_658360 75123360820922088260503 := by
  unfold tailWord_658360
  simp only [CollatzResearch.WordTrace]
  refine ⟨12006180947440816890694267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16008241263254422520925689 12006180947440816890694267)
  ·
    refine ⟨18009271421161225336041401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12006180947440816890694267 18009271421161225336041401)
    ·
      refine ⟨13506953565870919002031051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18009271421161225336041401 13506953565870919002031051)
      ·
        refine ⟨20260430348806378503046577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13506953565870919002031051 20260430348806378503046577)
        ·
          refine ⟨15195322761604783877284933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20260430348806378503046577 15195322761604783877284933)
          ·
            refine ⟨2849123017800896976990925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15195322761604783877284933 2849123017800896976990925)
            ·
              refine ⟨1068421131675336366371597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2849123017800896976990925 1068421131675336366371597)
              ·
                refine ⟨400657924378251137389349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1068421131675336366371597 400657924378251137389349)
                ·
                  refine ⟨75123360820922088260503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400657924378251137389349 75123360820922088260503)
                  ·
                    rfl

theorem cell22_658360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 4].length) (baseStart_658360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658360 prefixEnd_658360 := by exact prefixLift 658360
  have htrace : WordTrace (prefixWord ++ tailWord_658360) baseStart_658360 baseEnd_658360 := by
    simpa [prefixWord, tailWord_658360, baseEnd_658360] using wordTrace_append hprefix tailTrace_658360
  have hstable : (prefixWord ++ tailWord_658360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658360).length < 2 ^ (prefixWord ++ tailWord_658360).sum := by decide
  have hdescent : baseEnd_658360 < baseStart_658360 := by decide
  rcases family_descends (prefixWord ++ tailWord_658360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658388 : List Nat := [2, 4, 1, 2, 1, 2, 1, 9]
def baseStart_658388 : Nat := 118140960795 + 658388 * 2 ^ 59
def prefixEnd_658388 : Nat := 4983230072969 + 3 ^ 40 * 658388 * 2
def baseEnd_658388 : Nat := 25042185270553725009047

theorem tailTrace_658388 : CollatzResearch.WordTrace tailWord_658388 prefixEnd_658388 25042185270553725009047 := by
  unfold tailWord_658388
  simp only [CollatzResearch.WordTrace]
  refine ⟨12006691569390097281703909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16008922092520129708938545 12006691569390097281703909)
  ·
    refine ⟨2251254669260643240319483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12006691569390097281703909 2251254669260643240319483)
    ·
      refine ⟨3376882003890964860479225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2251254669260643240319483 3376882003890964860479225)
      ·
        refine ⟨2532661502918223645359419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3376882003890964860479225 2532661502918223645359419)
        ·
          refine ⟨3798992254377335468039129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2532661502918223645359419 3798992254377335468039129)
          ·
            refine ⟨2849244190783001601029347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3798992254377335468039129 2849244190783001601029347)
            ·
              refine ⟨4273866286174502401544021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2849244190783001601029347 4273866286174502401544021)
              ·
                refine ⟨25042185270553725009047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4273866286174502401544021 25042185270553725009047)
                ·
                  rfl

theorem cell22_658388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 9].length) (baseStart_658388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658388 prefixEnd_658388 := by exact prefixLift 658388
  have htrace : WordTrace (prefixWord ++ tailWord_658388) baseStart_658388 baseEnd_658388 := by
    simpa [prefixWord, tailWord_658388, baseEnd_658388] using wordTrace_append hprefix tailTrace_658388
  have hstable : (prefixWord ++ tailWord_658388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658388).length < 2 ^ (prefixWord ++ tailWord_658388).sum := by decide
  have hdescent : baseEnd_658388 < baseStart_658388 := by decide
  rcases family_descends (prefixWord ++ tailWord_658388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658392 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 2, 3]
def baseStart_658392 : Nat := 118140960795 + 658392 * 2 ^ 59
def prefixEnd_658392 : Nat := 4983230072969 + 3 ^ 40 * 658392 * 2
def baseEnd_658392 : Nat := 225381036716728847981411

theorem tailTrace_658392 : CollatzResearch.WordTrace tailWord_658392 prefixEnd_658392 225381036716728847981411 := by
  unfold tailWord_658392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12006764515382851623276715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16009019353843802164368953 12006764515382851623276715)
  ·
    refine ⟨18010146773074277434915073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12006764515382851623276715 18010146773074277434915073)
    ·
      refine ⟨13507610079805708076186305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18010146773074277434915073 13507610079805708076186305)
      ·
        refine ⟨10130707559854281057139729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13507610079805708076186305 10130707559854281057139729)
        ·
          refine ⟨7598030669890710792854797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10130707559854281057139729 7598030669890710792854797)
          ·
            refine ⟨2849261501209016547320549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7598030669890710792854797 2849261501209016547320549)
            ·
              refine ⟨534236531476690602622603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2849261501209016547320549 534236531476690602622603)
              ·
                refine ⟨801354797215035903933905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534236531476690602622603 801354797215035903933905)
                ·
                  refine ⟨601016097911276927950429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 801354797215035903933905 601016097911276927950429)
                  ·
                    refine ⟨225381036716728847981411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601016097911276927950429 225381036716728847981411)
                    ·
                      rfl

theorem cell22_658392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_658392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658392 prefixEnd_658392 := by exact prefixLift 658392
  have htrace : WordTrace (prefixWord ++ tailWord_658392) baseStart_658392 baseEnd_658392 := by
    simpa [prefixWord, tailWord_658392, baseEnd_658392] using wordTrace_append hprefix tailTrace_658392
  have hstable : (prefixWord ++ tailWord_658392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658392).length < 2 ^ (prefixWord ++ tailWord_658392).sum := by decide
  have hdescent : baseEnd_658392 < baseStart_658392 := by decide
  rcases family_descends (prefixWord ++ tailWord_658392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658437 : List Nat := [1, 3, 1, 1, 2, 3, 3, 4, 1, 3]
def baseStart_658437 : Nat := 118140960795 + 658437 * 2 ^ 59
def prefixEnd_658437 : Nat := 4983230072969 + 3 ^ 40 * 658437 * 2
def baseEnd_658437 : Nat := 225396441136363730606273

theorem tailTrace_658437 : CollatzResearch.WordTrace tailWord_658437 prefixEnd_658437 225396441136363730606273 := by
  unfold tailWord_658437
  simp only [CollatzResearch.WordTrace]
  refine ⟨24015170315602675931941565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16010113543735117287961043 24015170315602675931941565)
  ·
    refine ⟨9005688868351003474478087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24015170315602675931941565 9005688868351003474478087)
    ·
      refine ⟨13508533302526505211717131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9005688868351003474478087 13508533302526505211717131)
      ·
        refine ⟨20262799953789757817575697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13508533302526505211717131 20262799953789757817575697)
        ·
          refine ⟨15197099965342318363181773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20262799953789757817575697 15197099965342318363181773)
          ·
            refine ⟨5698912487003369386193165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15197099965342318363181773 5698912487003369386193165)
            ·
              refine ⟨2137092182626263519822437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5698912487003369386193165 2137092182626263519822437)
              ·
                refine ⟨400704784242424409966707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2137092182626263519822437 400704784242424409966707)
                ·
                  refine ⟨601057176363636614950061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400704784242424409966707 601057176363636614950061)
                  ·
                    refine ⟨225396441136363730606273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601057176363636614950061 225396441136363730606273)
                    ·
                      rfl

theorem cell22_658437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_658437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658437 prefixEnd_658437 := by exact prefixLift 658437
  have htrace : WordTrace (prefixWord ++ tailWord_658437) baseStart_658437 baseEnd_658437 := by
    simpa [prefixWord, tailWord_658437, baseEnd_658437] using wordTrace_append hprefix tailTrace_658437
  have hstable : (prefixWord ++ tailWord_658437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658437).length < 2 ^ (prefixWord ++ tailWord_658437).sum := by decide
  have hdescent : baseEnd_658437 < baseStart_658437 := by decide
  rcases family_descends (prefixWord ++ tailWord_658437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658471 : List Nat := [1, 1, 7, 1, 1, 2, 2, 3, 1, 3]
def baseStart_658471 : Nat := 118140960795 + 658471 * 2 ^ 59
def prefixEnd_658471 : Nat := 4983230072969 + 3 ^ 40 * 658471 * 2
def baseEnd_658471 : Nat := 225408080031198975256169

theorem tailTrace_658471 : CollatzResearch.WordTrace tailWord_658471 prefixEnd_658471 225408080031198975256169 := by
  unfold tailWord_658471
  simp only [CollatzResearch.WordTrace]
  refine ⟨24016410397479499738679267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16010940264986333159119511 24016410397479499738679267)
  ·
    refine ⟨36024615596219249608018901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24016410397479499738679267 36024615596219249608018901)
    ·
      refine ⟨844326928036388662687943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 36024615596219249608018901 844326928036388662687943)
      ·
        refine ⟨1266490392054582994031915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844326928036388662687943 1266490392054582994031915)
        ·
          refine ⟨1899735588081874491047873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266490392054582994031915 1899735588081874491047873)
          ·
            refine ⟨1424801691061405868285905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1899735588081874491047873 1424801691061405868285905)
            ·
              refine ⟨1068601268296054401214429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424801691061405868285905 1068601268296054401214429)
              ·
                refine ⟨400725475611020400455411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1068601268296054401214429 400725475611020400455411)
                ·
                  refine ⟨601088213416530600683117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400725475611020400455411 601088213416530600683117)
                  ·
                    refine ⟨225408080031198975256169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601088213416530600683117 225408080031198975256169)
                    ·
                      rfl

theorem cell22_658471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_658471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658471 prefixEnd_658471 := by exact prefixLift 658471
  have htrace : WordTrace (prefixWord ++ tailWord_658471) baseStart_658471 baseEnd_658471 := by
    simpa [prefixWord, tailWord_658471, baseEnd_658471] using wordTrace_append hprefix tailTrace_658471
  have hstable : (prefixWord ++ tailWord_658471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658471).length < 2 ^ (prefixWord ++ tailWord_658471).sum := by decide
  have hdescent : baseEnd_658471 < baseStart_658471 := by decide
  rcases family_descends (prefixWord ++ tailWord_658471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658480 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 1, 4]
def baseStart_658480 : Nat := 118140960795 + 658480 * 2 ^ 59
def prefixEnd_658480 : Nat := 4983230072969 + 3 ^ 40 * 658480 * 2
def baseEnd_658480 : Nat := 225411160915125951781141

theorem tailTrace_658480 : CollatzResearch.WordTrace tailWord_658480 prefixEnd_658480 225411160915125951781141 := by
  unfold tailWord_658480
  simp only [CollatzResearch.WordTrace]
  refine ⟨12008369327223447137878447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16011159102964596183837929 12008369327223447137878447)
  ·
    refine ⟨18012553990835170706817671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12008369327223447137878447 18012553990835170706817671)
    ·
      refine ⟨27018830986252756060226507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18012553990835170706817671 27018830986252756060226507)
      ·
        refine ⟨40528246479379134090339761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27018830986252756060226507 40528246479379134090339761)
        ·
          refine ⟨30396184859534350567754821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40528246479379134090339761 30396184859534350567754821)
          ·
            refine ⟨5699284661162690731454029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30396184859534350567754821 5699284661162690731454029)
            ·
              refine ⟨2137231747936009024295261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5699284661162690731454029 2137231747936009024295261)
              ·
                refine ⟨801461905476003384110723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2137231747936009024295261 801461905476003384110723)
                ·
                  refine ⟨1202192858214005076166085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801461905476003384110723 1202192858214005076166085)
                  ·
                    refine ⟨225411160915125951781141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1202192858214005076166085 225411160915125951781141)
                    ·
                      rfl

theorem cell22_658480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_658480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658480 prefixEnd_658480 := by exact prefixLift 658480
  have htrace : WordTrace (prefixWord ++ tailWord_658480) baseStart_658480 baseEnd_658480 := by
    simpa [prefixWord, tailWord_658480, baseEnd_658480] using wordTrace_append hprefix tailTrace_658480
  have hstable : (prefixWord ++ tailWord_658480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658480).length < 2 ^ (prefixWord ++ tailWord_658480).sum := by decide
  have hdescent : baseEnd_658480 < baseStart_658480 := by decide
  rcases family_descends (prefixWord ++ tailWord_658480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658484 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 5]
def baseStart_658484 : Nat := 118140960795 + 658484 * 2 ^ 59
def prefixEnd_658484 : Nat := 4983230072969 + 3 ^ 40 * 658484 * 2
def baseEnd_658484 : Nat := 75137510065623758227043

theorem tailTrace_658484 : CollatzResearch.WordTrace tailWord_658484 prefixEnd_658484 75137510065623758227043 := by
  unfold tailWord_658484
  simp only [CollatzResearch.WordTrace]
  refine ⟨12008442273216201479451253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16011256364288268639268337 12008442273216201479451253)
  ·
    refine ⟨1125791463114018888698555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12008442273216201479451253 1125791463114018888698555)
    ·
      refine ⟨1688687194671028333047833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125791463114018888698555 1688687194671028333047833)
      ·
        refine ⟨1266515396003271249785875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1688687194671028333047833 1266515396003271249785875)
        ·
          refine ⟨1899773094004906874678813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266515396003271249785875 1899773094004906874678813)
          ·
            refine ⟨712414910251840078004555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1899773094004906874678813 712414910251840078004555)
            ·
              refine ⟨1068622365377760117006833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712414910251840078004555 1068622365377760117006833)
              ·
                refine ⟨801466774033320087755125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068622365377760117006833 801466774033320087755125)
                ·
                  refine ⟨75137510065623758227043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 801466774033320087755125 75137510065623758227043)
                  ·
                    rfl

theorem cell22_658484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_658484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658484 prefixEnd_658484 := by exact prefixLift 658484
  have htrace : WordTrace (prefixWord ++ tailWord_658484) baseStart_658484 baseEnd_658484 := by
    simpa [prefixWord, tailWord_658484, baseEnd_658484] using wordTrace_append hprefix tailTrace_658484
  have hstable : (prefixWord ++ tailWord_658484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658484).length < 2 ^ (prefixWord ++ tailWord_658484).sum := by decide
  have hdescent : baseEnd_658484 < baseStart_658484 := by decide
  rcases family_descends (prefixWord ++ tailWord_658484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658542 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_658542 : Nat := 118140960795 + 658542 * 2 ^ 59
def prefixEnd_658542 : Nat := 4983230072969 + 3 ^ 40 * 658542 * 2
def baseEnd_658542 : Nat := 225432384782178456730951

theorem tailTrace_658542 : CollatzResearch.WordTrace tailWord_658542 prefixEnd_658542 225432384782178456730951 := by
  unfold tailWord_658542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002374997527784858064235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16012666653481519243009253 3002374997527784858064235)
  ·
    refine ⟨4503562496291677287096353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3002374997527784858064235 4503562496291677287096353)
    ·
      refine ⟨3377671872218757965322265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4503562496291677287096353 3377671872218757965322265)
      ·
        refine ⟨2533253904164068473991699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3377671872218757965322265 2533253904164068473991699)
        ·
          refine ⟨3799880856246102710987549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533253904164068473991699 3799880856246102710987549)
          ·
            refine ⟨1424955321092288516620331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3799880856246102710987549 1424955321092288516620331)
            ·
              refine ⟨2137432981638432774930497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424955321092288516620331 2137432981638432774930497)
              ·
                refine ⟨1603074736228824581197873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137432981638432774930497 1603074736228824581197873)
                ·
                  refine ⟨1202306052171618435898405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1603074736228824581197873 1202306052171618435898405)
                  ·
                    refine ⟨225432384782178456730951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1202306052171618435898405 225432384782178456730951)
                    ·
                      rfl

theorem cell22_658542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_658542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658542 prefixEnd_658542 := by exact prefixLift 658542
  have htrace : WordTrace (prefixWord ++ tailWord_658542) baseStart_658542 baseEnd_658542 := by
    simpa [prefixWord, tailWord_658542, baseEnd_658542] using wordTrace_append hprefix tailTrace_658542
  have hstable : (prefixWord ++ tailWord_658542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658542).length < 2 ^ (prefixWord ++ tailWord_658542).sum := by decide
  have hdescent : baseEnd_658542 < baseStart_658542 := by decide
  rcases family_descends (prefixWord ++ tailWord_658542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658561 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 2, 3]
def baseStart_658561 : Nat := 118140960795 + 658561 * 2 ^ 59
def prefixEnd_658561 : Nat := 4983230072969 + 3 ^ 40 * 658561 * 2
def baseEnd_658561 : Nat := 225438888870468740505893

theorem tailTrace_658561 : CollatzResearch.WordTrace tailWord_658561 prefixEnd_658561 225438888870468740505893 := by
  unfold tailWord_658561
  simp only [CollatzResearch.WordTrace]
  refine ⟨24019692967153445109455537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16013128644768963406303691 24019692967153445109455537)
  ·
    refine ⟨18014769725365083832091653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24019692967153445109455537 18014769725365083832091653)
    ·
      refine ⟨3377769323505953218517185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18014769725365083832091653 3377769323505953218517185)
      ·
        refine ⟨2533326992629464913887889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3377769323505953218517185 2533326992629464913887889)
        ·
          refine ⟨1899995244472098685415917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2533326992629464913887889 1899995244472098685415917)
          ·
            refine ⟨712498216677037007030969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1899995244472098685415917 712498216677037007030969)
            ·
              refine ⟨534373662507777755273227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712498216677037007030969 534373662507777755273227)
              ·
                refine ⟨801560493761666632909841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534373662507777755273227 801560493761666632909841)
                ·
                  refine ⟨601170370321249974682381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 801560493761666632909841 601170370321249974682381)
                  ·
                    refine ⟨225438888870468740505893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601170370321249974682381 225438888870468740505893)
                    ·
                      rfl

theorem cell22_658561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_658561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658561 prefixEnd_658561 := by exact prefixLift 658561
  have htrace : WordTrace (prefixWord ++ tailWord_658561) baseStart_658561 baseEnd_658561 := by
    simpa [prefixWord, tailWord_658561, baseEnd_658561] using wordTrace_append hprefix tailTrace_658561
  have hstable : (prefixWord ++ tailWord_658561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658561).length < 2 ^ (prefixWord ++ tailWord_658561).sum := by decide
  have hdescent : baseEnd_658561 < baseStart_658561 := by decide
  rcases family_descends (prefixWord ++ tailWord_658561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658589 : List Nat := [1, 4, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_658589 : Nat := 118140960795 + 658589 * 2 ^ 59
def prefixEnd_658589 : Nat := 4983230072969 + 3 ^ 40 * 658589 * 2
def baseEnd_658589 : Nat := 225448473842686000805807

theorem tailTrace_658589 : CollatzResearch.WordTrace tailWord_658589 prefixEnd_658589 225448473842686000805807 := by
  unfold tailWord_658589
  simp only [CollatzResearch.WordTrace]
  refine ⟨24020714211052005891474821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16013809474034670594316547 24020714211052005891474821)
  ·
    refine ⟨4503883914572251104651529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24020714211052005891474821 4503883914572251104651529)
    ·
      refine ⟨3377912935929188328488647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4503883914572251104651529 3377912935929188328488647)
      ·
        refine ⟨5066869403893782492732971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3377912935929188328488647 5066869403893782492732971)
        ·
          refine ⟨7600304105840673739099457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5066869403893782492732971 7600304105840673739099457)
          ·
            refine ⟨5700228079380505304324593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7600304105840673739099457 5700228079380505304324593)
            ·
              refine ⟨4275171059535378978243445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5700228079380505304324593 4275171059535378978243445)
              ·
                refine ⟨400797286831441779210323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4275171059535378978243445 400797286831441779210323)
                ·
                  refine ⟨601195930247162668815485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400797286831441779210323 601195930247162668815485)
                  ·
                    refine ⟨225448473842686000805807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601195930247162668815485 225448473842686000805807)
                    ·
                      rfl

theorem cell22_658589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_658589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658589 prefixEnd_658589 := by exact prefixLift 658589
  have htrace : WordTrace (prefixWord ++ tailWord_658589) baseStart_658589 baseEnd_658589 := by
    simpa [prefixWord, tailWord_658589, baseEnd_658589] using wordTrace_append hprefix tailTrace_658589
  have hstable : (prefixWord ++ tailWord_658589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658589).length < 2 ^ (prefixWord ++ tailWord_658589).sum := by decide
  have hdescent : baseEnd_658589 < baseStart_658589 := by decide
  rcases family_descends (prefixWord ++ tailWord_658589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658615 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 5, 4]
def baseStart_658615 : Nat := 118140960795 + 658615 * 2 ^ 59
def prefixEnd_658615 : Nat := 4983230072969 + 3 ^ 40 * 658615 * 2
def baseEnd_658615 : Nat := 225457374174030599655727

theorem tailTrace_658615 : CollatzResearch.WordTrace tailWord_658615 prefixEnd_658615 225457374174030599655727 := by
  unfold tailWord_658615
  simp only [CollatzResearch.WordTrace]
  refine ⟨24021662508957812331921299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16014441672638541554614199 24021662508957812331921299)
  ·
    refine ⟨36032493763436718497881949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24021662508957812331921299 36032493763436718497881949)
    ·
      refine ⟨13512185161288769436705731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36032493763436718497881949 13512185161288769436705731)
      ·
        refine ⟨20268277741933154155058597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13512185161288769436705731 20268277741933154155058597)
        ·
          refine ⟨3800302076612466404073487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20268277741933154155058597 3800302076612466404073487)
          ·
            refine ⟨5700453114918699606110231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800302076612466404073487 5700453114918699606110231)
            ·
              refine ⟨8550679672378049409165347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5700453114918699606110231 8550679672378049409165347)
              ·
                refine ⟨12826019508567074113748021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8550679672378049409165347 12826019508567074113748021)
                ·
                  refine ⟨1202439328928163198163877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12826019508567074113748021 1202439328928163198163877)
                  ·
                    refine ⟨225457374174030599655727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1202439328928163198163877 225457374174030599655727)
                    ·
                      rfl

theorem cell22_658615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_658615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658615 prefixEnd_658615 := by exact prefixLift 658615
  have htrace : WordTrace (prefixWord ++ tailWord_658615) baseStart_658615 baseEnd_658615 := by
    simpa [prefixWord, tailWord_658615, baseEnd_658615] using wordTrace_append hprefix tailTrace_658615
  have hstable : (prefixWord ++ tailWord_658615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658615).length < 2 ^ (prefixWord ++ tailWord_658615).sum := by decide
  have hdescent : baseEnd_658615 < baseStart_658615 := by decide
  rcases family_descends (prefixWord ++ tailWord_658615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658647 : List Nat := [1, 1, 3, 2, 1, 2, 3, 5, 4]
def baseStart_658647 : Nat := 118140960795 + 658647 * 2 ^ 59
def prefixEnd_658647 : Nat := 4983230072969 + 3 ^ 40 * 658647 * 2
def baseEnd_658647 : Nat := 75156109475997727618543

theorem tailTrace_658647 : CollatzResearch.WordTrace tailWord_658647 prefixEnd_658647 75156109475997727618543 := by
  unfold tailWord_658647
  simp only [CollatzResearch.WordTrace]
  refine ⟨24022829644841881797086195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16015219763227921198057463 24022829644841881797086195)
  ·
    refine ⟨36034244467262822695629293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24022829644841881797086195 36034244467262822695629293)
    ·
      refine ⟨13512841675223558510860985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36034244467262822695629293 13512841675223558510860985)
      ·
        refine ⟨10134631256417668883145739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13512841675223558510860985 10134631256417668883145739)
        ·
          refine ⟨15201946884626503324718609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10134631256417668883145739 15201946884626503324718609)
          ·
            refine ⟨11401460163469877493538957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15201946884626503324718609 11401460163469877493538957)
            ·
              refine ⟨4275547561301204060077109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11401460163469877493538957 4275547561301204060077109)
              ·
                refine ⟨400832583871987880632229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4275547561301204060077109 400832583871987880632229)
                ·
                  refine ⟨75156109475997727618543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400832583871987880632229 75156109475997727618543)
                  ·
                    rfl

theorem cell22_658647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 4].length) (baseStart_658647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658647 prefixEnd_658647 := by exact prefixLift 658647
  have htrace : WordTrace (prefixWord ++ tailWord_658647) baseStart_658647 baseEnd_658647 := by
    simpa [prefixWord, tailWord_658647, baseEnd_658647] using wordTrace_append hprefix tailTrace_658647
  have hstable : (prefixWord ++ tailWord_658647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658647).length < 2 ^ (prefixWord ++ tailWord_658647).sum := by decide
  have hdescent : baseEnd_658647 < baseStart_658647 := by decide
  rcases family_descends (prefixWord ++ tailWord_658647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658692 : List Nat := [2, 3, 2, 2, 2, 2, 1, 8]
def baseStart_658692 : Nat := 118140960795 + 658692 * 2 ^ 59
def prefixEnd_658692 : Nat := 4983230072969 + 3 ^ 40 * 658692 * 2
def baseEnd_658692 : Nat := 25053748094180896164499

theorem tailTrace_658692 : CollatzResearch.WordTrace tailWord_658692 prefixEnd_658692 25053748094180896164499 := by
  unfold tailWord_658692
  simp only [CollatzResearch.WordTrace]
  refine ⟨12012235464839427241237165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16016313953119236321649553 12012235464839427241237165)
  ·
    refine ⟨4504588299314785215463937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12012235464839427241237165 4504588299314785215463937)
    ·
      refine ⟨3378441224486088911597953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4504588299314785215463937 3378441224486088911597953)
      ·
        refine ⟨2533830918364566683698465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3378441224486088911597953 2533830918364566683698465)
        ·
          refine ⟨1900373188773425012773849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2533830918364566683698465 1900373188773425012773849)
          ·
            refine ⟨1425279891580068759580387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1900373188773425012773849 1425279891580068759580387)
            ·
              refine ⟨2137919837370103139370581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425279891580068759580387 2137919837370103139370581)
              ·
                refine ⟨25053748094180896164499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2137919837370103139370581 25053748094180896164499)
                ·
                  rfl

theorem cell22_658692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 8].length) (baseStart_658692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658692 prefixEnd_658692 := by exact prefixLift 658692
  have htrace : WordTrace (prefixWord ++ tailWord_658692) baseStart_658692 baseEnd_658692 := by
    simpa [prefixWord, tailWord_658692, baseEnd_658692] using wordTrace_append hprefix tailTrace_658692
  have hstable : (prefixWord ++ tailWord_658692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658692).length < 2 ^ (prefixWord ++ tailWord_658692).sum := by decide
  have hdescent : baseEnd_658692 < baseStart_658692 := by decide
  rcases family_descends (prefixWord ++ tailWord_658692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658735 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 1, 7]
def baseStart_658735 : Nat := 118140960795 + 658735 * 2 ^ 59
def prefixEnd_658735 : Nat := 4983230072969 + 3 ^ 40 * 658735 * 2
def baseEnd_658735 : Nat := 225498452626390286655359

theorem tailTrace_658735 : CollatzResearch.WordTrace tailWord_658735 prefixEnd_658735 225498452626390286655359 := by
  unfold tailWord_658735
  simp only [CollatzResearch.WordTrace]
  refine ⟨24026039268523072826289659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16017359512348715217526439 24026039268523072826289659)
  ·
    refine ⟨36039058902784609239434489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24026039268523072826289659 36039058902784609239434489)
    ·
      refine ⟨27029294177088456929575867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36039058902784609239434489 27029294177088456929575867)
      ·
        refine ⟨40543941265632685394363801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27029294177088456929575867 40543941265632685394363801)
        ·
          refine ⟨30407955949224514045772851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40543941265632685394363801 30407955949224514045772851)
          ·
            refine ⟨45611933923836771068659277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30407955949224514045772851 45611933923836771068659277)
            ·
              refine ⟨17104475221438789150747229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45611933923836771068659277 17104475221438789150747229)
              ·
                refine ⟨6414178208039545931530211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17104475221438789150747229 6414178208039545931530211)
                ·
                  refine ⟨9621267312059318897295317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6414178208039545931530211 9621267312059318897295317)
                  ·
                    refine ⟨225498452626390286655359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9621267312059318897295317 225498452626390286655359)
                    ·
                      rfl

theorem cell22_658735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_658735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658735 prefixEnd_658735 := by exact prefixLift 658735
  have htrace : WordTrace (prefixWord ++ tailWord_658735) baseStart_658735 baseEnd_658735 := by
    simpa [prefixWord, tailWord_658735, baseEnd_658735] using wordTrace_append hprefix tailTrace_658735
  have hstable : (prefixWord ++ tailWord_658735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658735).length < 2 ^ (prefixWord ++ tailWord_658735).sum := by decide
  have hdescent : baseEnd_658735 < baseStart_658735 := by decide
  rcases family_descends (prefixWord ++ tailWord_658735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658812 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_658812 : Nat := 118140960795 + 658812 * 2 ^ 59
def prefixEnd_658812 : Nat := 4983230072969 + 3 ^ 40 * 658812 * 2
def baseEnd_658812 : Nat := 225524811299987752480123

theorem tailTrace_658812 : CollatzResearch.WordTrace tailWord_658812 prefixEnd_658812 225524811299987752480123 := by
  unfold tailWord_658812
  simp only [CollatzResearch.WordTrace]
  refine ⟨12014423844622057488421345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16019231792829409984561793 12014423844622057488421345)
  ·
    refine ⟨9010817883466543116316009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12014423844622057488421345 9010817883466543116316009)
    ·
      refine ⟨6758113412599907337237007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9010817883466543116316009 6758113412599907337237007)
      ·
        refine ⟨10137170118899861005855511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758113412599907337237007 10137170118899861005855511)
        ·
          refine ⟨15205755178349791508783267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10137170118899861005855511 15205755178349791508783267)
          ·
            refine ⟨22808632767524687263174901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15205755178349791508783267 22808632767524687263174901)
            ·
              refine ⟨2138309321955439430922647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22808632767524687263174901 2138309321955439430922647)
              ·
                refine ⟨3207463982933159146383971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138309321955439430922647 3207463982933159146383971)
                ·
                  refine ⟨4811195974399738719575957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207463982933159146383971 4811195974399738719575957)
                  ·
                    refine ⟨225524811299987752480123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4811195974399738719575957 225524811299987752480123)
                    ·
                      rfl

theorem cell22_658812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_658812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658812 prefixEnd_658812 := by exact prefixLift 658812
  have htrace : WordTrace (prefixWord ++ tailWord_658812) baseStart_658812 baseEnd_658812 := by
    simpa [prefixWord, tailWord_658812, baseEnd_658812] using wordTrace_append hprefix tailTrace_658812
  have hstable : (prefixWord ++ tailWord_658812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658812).length < 2 ^ (prefixWord ++ tailWord_658812).sum := by decide
  have hdescent : baseEnd_658812 < baseStart_658812 := by decide
  rcases family_descends (prefixWord ++ tailWord_658812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658818 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_658818 : Nat := 118140960795 + 658818 * 2 ^ 59
def prefixEnd_658818 : Nat := 4983230072969 + 3 ^ 40 * 658818 * 2
def baseEnd_658818 : Nat := 225526865222605736830105

theorem tailTrace_658818 : CollatzResearch.WordTrace tailWord_658818 prefixEnd_658818 225526865222605736830105 := by
  unfold tailWord_658818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6007266631805594500390277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16019377684814918667707405 6007266631805594500390277)
  ·
    refine ⟨1126362493463548968823177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6007266631805594500390277 1126362493463548968823177)
    ·
      refine ⟨844771870097661726617383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1126362493463548968823177 844771870097661726617383)
      ·
        refine ⟨1267157805146492589926075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844771870097661726617383 1267157805146492589926075)
        ·
          refine ⟨1900736707719738884889113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267157805146492589926075 1900736707719738884889113)
          ·
            refine ⟨1425552530789804163666835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1900736707719738884889113 1425552530789804163666835)
            ·
              refine ⟨2138328796184706245500253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425552530789804163666835 2138328796184706245500253)
              ·
                refine ⟨801873298569264842062595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2138328796184706245500253 801873298569264842062595)
                ·
                  refine ⟨1202809947853897263093893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801873298569264842062595 1202809947853897263093893)
                  ·
                    refine ⟨225526865222605736830105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1202809947853897263093893 225526865222605736830105)
                    ·
                      rfl

theorem cell22_658818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_658818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658818 prefixEnd_658818 := by exact prefixLift 658818
  have htrace : WordTrace (prefixWord ++ tailWord_658818) baseStart_658818 baseEnd_658818 := by
    simpa [prefixWord, tailWord_658818, baseEnd_658818] using wordTrace_append hprefix tailTrace_658818
  have hstable : (prefixWord ++ tailWord_658818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658818).length < 2 ^ (prefixWord ++ tailWord_658818).sum := by decide
  have hdescent : baseEnd_658818 < baseStart_658818 := by decide
  rcases family_descends (prefixWord ++ tailWord_658818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658861 : List Nat := [1, 5, 2, 2, 1, 1, 4, 6]
def baseStart_658861 : Nat := 118140960795 + 658861 * 2 ^ 59
def prefixEnd_658861 : Nat := 4983230072969 + 3 ^ 40 * 658861 * 2
def baseEnd_658861 : Nat := 25060176111263106444997

theorem tailTrace_658861 : CollatzResearch.WordTrace tailWord_658861 prefixEnd_658861 25060176111263106444997 := by
  unfold tailWord_658861
  simp only [CollatzResearch.WordTrace]
  refine ⟨24030634866066596345376437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16020423244044397563584291 24030634866066596345376437)
  ·
    refine ⟨2252872018693743407379041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24030634866066596345376437 2252872018693743407379041)
    ·
      refine ⟨1689654014020307555534281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2252872018693743407379041 1689654014020307555534281)
      ·
        refine ⟨1267240510515230666650711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1689654014020307555534281 1267240510515230666650711)
        ·
          refine ⟨1900860765772845999976067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267240510515230666650711 1900860765772845999976067)
          ·
            refine ⟨2851291148659268999964101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900860765772845999976067 2851291148659268999964101)
            ·
              refine ⟨534617090373612937493269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2851291148659268999964101 534617090373612937493269)
              ·
                refine ⟨25060176111263106444997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 534617090373612937493269 25060176111263106444997)
                ·
                  rfl

theorem cell22_658861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 6].length) (baseStart_658861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658861 prefixEnd_658861 := by exact prefixLift 658861
  have htrace : WordTrace (prefixWord ++ tailWord_658861) baseStart_658861 baseEnd_658861 := by
    simpa [prefixWord, tailWord_658861, baseEnd_658861] using wordTrace_append hprefix tailTrace_658861
  have hstable : (prefixWord ++ tailWord_658861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658861).length < 2 ^ (prefixWord ++ tailWord_658861).sum := by decide
  have hdescent : baseEnd_658861 < baseStart_658861 := by decide
  rcases family_descends (prefixWord ++ tailWord_658861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658872 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 7]
def baseStart_658872 : Nat := 118140960795 + 658872 * 2 ^ 59
def prefixEnd_658872 : Nat := 4983230072969 + 3 ^ 40 * 658872 * 2
def baseEnd_658872 : Nat := 75181783508722531993313

theorem tailTrace_658872 : CollatzResearch.WordTrace tailWord_658872 prefixEnd_658872 75181783508722531993313 := by
  unfold tailWord_658872
  simp only [CollatzResearch.WordTrace]
  refine ⟨12015518034513372612013435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16020690712684496816017913 12015518034513372612013435)
  ·
    refine ⟨18023277051770058918020153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12015518034513372612013435 18023277051770058918020153)
    ·
      refine ⟨13517457788827544188515115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18023277051770058918020153 13517457788827544188515115)
      ·
        refine ⟨20276186683241316282772673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13517457788827544188515115 20276186683241316282772673)
        ·
          refine ⟨15207140012430987212079505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20276186683241316282772673 15207140012430987212079505)
          ·
            refine ⟨11405355009323240409059629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15207140012430987212079505 11405355009323240409059629)
            ·
              refine ⟨4277008128496215153397361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11405355009323240409059629 4277008128496215153397361)
              ·
                refine ⟨3207756096372161365048021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4277008128496215153397361 3207756096372161365048021)
                ·
                  refine ⟨75181783508722531993313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3207756096372161365048021 75181783508722531993313)
                  ·
                    rfl

theorem cell22_658872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_658872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658872 prefixEnd_658872 := by exact prefixLift 658872
  have htrace : WordTrace (prefixWord ++ tailWord_658872) baseStart_658872 baseEnd_658872 := by
    simpa [prefixWord, tailWord_658872, baseEnd_658872] using wordTrace_append hprefix tailTrace_658872
  have hstable : (prefixWord ++ tailWord_658872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658872).length < 2 ^ (prefixWord ++ tailWord_658872).sum := by decide
  have hdescent : baseEnd_658872 < baseStart_658872 := by decide
  rcases family_descends (prefixWord ++ tailWord_658872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658906 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_658906 : Nat := 118140960795 + 658906 * 2 ^ 59
def prefixEnd_658906 : Nat := 4983230072969 + 3 ^ 40 * 658906 * 2
def baseEnd_658906 : Nat := 75185663140334280209945

theorem tailTrace_658906 : CollatzResearch.WordTrace tailWord_658906 prefixEnd_658906 75185663140334280209945 := by
  unfold tailWord_658906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6008069037725892257691143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16021517433935712687176381 6008069037725892257691143)
  ·
    refine ⟨9012103556588838386536715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6008069037725892257691143 9012103556588838386536715)
    ·
      refine ⟨13518155334883257579805073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9012103556588838386536715 13518155334883257579805073)
      ·
        refine ⟨10138616501162443184853805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13518155334883257579805073 10138616501162443184853805)
        ·
          refine ⟨3801981187935916194320177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10138616501162443184853805 3801981187935916194320177)
          ·
            refine ⟨2851485890951937145740133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3801981187935916194320177 2851485890951937145740133)
            ·
              refine ⟨534653604553488214826275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2851485890951937145740133 534653604553488214826275)
              ·
                refine ⟨801980406830232322239413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534653604553488214826275 801980406830232322239413)
                ·
                  refine ⟨75185663140334280209945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 801980406830232322239413 75185663140334280209945)
                  ·
                    rfl

theorem cell22_658906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_658906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_658906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_658906 prefixEnd_658906 := by exact prefixLift 658906
  have htrace : WordTrace (prefixWord ++ tailWord_658906) baseStart_658906 baseEnd_658906 := by
    simpa [prefixWord, tailWord_658906, baseEnd_658906] using wordTrace_append hprefix tailTrace_658906
  have hstable : (prefixWord ++ tailWord_658906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658906).length < 2 ^ (prefixWord ++ tailWord_658906).sum := by decide
  have hdescent : baseEnd_658906 < baseStart_658906 := by decide
  rcases family_descends (prefixWord ++ tailWord_658906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659030 : List Nat := [5, 2, 2, 2, 1, 1, 1, 8]
def baseStart_659030 : Nat := 118140960795 + 659030 * 2 ^ 59
def prefixEnd_659030 : Nat := 4983230072969 + 3 ^ 40 * 659030 * 2
def baseEnd_659030 : Nat := 25066604128345316725495

theorem tailTrace_659030 : CollatzResearch.WordTrace tailWord_659030 prefixEnd_659030 25066604128345316725495 := by
  unfold tailWord_659030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1502299925153396138017409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16024532534969558805519029 1502299925153396138017409)
  ·
    refine ⟨1126724943865047103513057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1502299925153396138017409 1126724943865047103513057)
    ·
      refine ⟨845043707898785327634793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1126724943865047103513057 845043707898785327634793)
      ·
        refine ⟨633782780924088995726095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 845043707898785327634793 633782780924088995726095)
        ·
          refine ⟨950674171386133493589143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633782780924088995726095 950674171386133493589143)
          ·
            refine ⟨1426011257079200240383715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950674171386133493589143 1426011257079200240383715)
            ·
              refine ⟨2139016885618800360575573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426011257079200240383715 2139016885618800360575573)
              ·
                refine ⟨25066604128345316725495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2139016885618800360575573 25066604128345316725495)
                ·
                  rfl

theorem cell22_659030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_659030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659030 prefixEnd_659030 := by exact prefixLift 659030
  have htrace : WordTrace (prefixWord ++ tailWord_659030) baseStart_659030 baseEnd_659030 := by
    simpa [prefixWord, tailWord_659030, baseEnd_659030] using wordTrace_append hprefix tailTrace_659030
  have hstable : (prefixWord ++ tailWord_659030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659030).length < 2 ^ (prefixWord ++ tailWord_659030).sum := by decide
  have hdescent : baseEnd_659030 < baseStart_659030 := by decide
  rcases family_descends (prefixWord ++ tailWord_659030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659045 : List Nat := [1, 3, 1, 3, 3, 1, 3, 3, 1, 3]
def baseStart_659045 : Nat := 118140960795 + 659045 * 2 ^ 59
def prefixEnd_659045 : Nat := 4983230072969 + 3 ^ 40 * 659045 * 2
def baseEnd_659045 : Nat := 225604571961652811404409

theorem tailTrace_659045 : CollatzResearch.WordTrace tailWord_659045 prefixEnd_659045 225604571961652811404409 := by
  unfold tailWord_659045
  simp only [CollatzResearch.WordTrace]
  refine ⟨24037345897399995770074589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16024897264933330513383059 24037345897399995770074589)
  ·
    refine ⟨9014004711524998413777971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24037345897399995770074589 9014004711524998413777971)
    ·
      refine ⟨13521007067287497620666957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9014004711524998413777971 13521007067287497620666957)
      ·
        refine ⟨5070377650232811607750109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13521007067287497620666957 5070377650232811607750109)
        ·
          refine ⟨1901391618837304352906291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5070377650232811607750109 1901391618837304352906291)
          ·
            refine ⟨2852087428255956529359437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901391618837304352906291 2852087428255956529359437)
            ·
              refine ⟨1069532785595983698509789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2852087428255956529359437 1069532785595983698509789)
              ·
                refine ⟨401074794598493886941171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1069532785595983698509789 401074794598493886941171)
                ·
                  refine ⟨601612191897740830411757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401074794598493886941171 601612191897740830411757)
                  ·
                    refine ⟨225604571961652811404409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601612191897740830411757 225604571961652811404409)
                    ·
                      rfl

theorem cell22_659045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_659045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659045 prefixEnd_659045 := by exact prefixLift 659045
  have htrace : WordTrace (prefixWord ++ tailWord_659045) baseStart_659045 baseEnd_659045 := by
    simpa [prefixWord, tailWord_659045, baseEnd_659045] using wordTrace_append hprefix tailTrace_659045
  have hstable : (prefixWord ++ tailWord_659045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659045).length < 2 ^ (prefixWord ++ tailWord_659045).sum := by decide
  have hdescent : baseEnd_659045 < baseStart_659045 := by decide
  rcases family_descends (prefixWord ++ tailWord_659045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659105 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 1, 4]
def baseStart_659105 : Nat := 118140960795 + 659105 * 2 ^ 59
def prefixEnd_659105 : Nat := 4983230072969 + 3 ^ 40 * 659105 * 2
def baseEnd_659105 : Nat := 225625111187832654904225

theorem tailTrace_659105 : CollatzResearch.WordTrace tailWord_659105 prefixEnd_659105 225625111187832654904225 := by
  unfold tailWord_659105
  simp only [CollatzResearch.WordTrace]
  refine ⟨24039534277182626017258769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16026356184788417344839179 24039534277182626017258769)
  ·
    refine ⟨18029650707886969512944077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24039534277182626017258769 18029650707886969512944077)
    ·
      refine ⟨6761119015457613567354029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18029650707886969512944077 6761119015457613567354029)
      ·
        refine ⟨2535419630796605087757761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6761119015457613567354029 2535419630796605087757761)
        ·
          refine ⟨1901564723097453815818321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2535419630796605087757761 1901564723097453815818321)
          ·
            refine ⟨1426173542323090361863741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1901564723097453815818321 1426173542323090361863741)
            ·
              refine ⟨534815078371158885698903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1426173542323090361863741 534815078371158885698903)
              ·
                refine ⟨802222617556738328548355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534815078371158885698903 802222617556738328548355)
                ·
                  refine ⟨1203333926335107492822533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802222617556738328548355 1203333926335107492822533)
                  ·
                    refine ⟨225625111187832654904225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203333926335107492822533 225625111187832654904225)
                    ·
                      rfl

theorem cell22_659105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_659105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659105 prefixEnd_659105 := by exact prefixLift 659105
  have htrace : WordTrace (prefixWord ++ tailWord_659105) baseStart_659105 baseEnd_659105 := by
    simpa [prefixWord, tailWord_659105, baseEnd_659105] using wordTrace_append hprefix tailTrace_659105
  have hstable : (prefixWord ++ tailWord_659105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659105).length < 2 ^ (prefixWord ++ tailWord_659105).sum := by decide
  have hdescent : baseEnd_659105 < baseStart_659105 := by decide
  rcases family_descends (prefixWord ++ tailWord_659105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659180 : List Nat := [2, 2, 1, 1, 2, 2, 4, 4, 1, 3]
def baseStart_659180 : Nat := 118140960795 + 659180 * 2 ^ 59
def prefixEnd_659180 : Nat := 4983230072969 + 3 ^ 40 * 659180 * 2
def baseEnd_659180 : Nat := 225650785220557459278995

theorem tailTrace_659180 : CollatzResearch.WordTrace tailWord_659180 prefixEnd_659180 225650785220557459278995 := by
  unfold tailWord_659180
  simp only [CollatzResearch.WordTrace]
  refine ⟨12021134875955456913119497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16028179834607275884159329 12021134875955456913119497)
  ·
    refine ⟨9015851156966592684839623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12021134875955456913119497 9015851156966592684839623)
    ·
      refine ⟨13523776735449889027259435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9015851156966592684839623 13523776735449889027259435)
      ·
        refine ⟨20285665103174833540889153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13523776735449889027259435 20285665103174833540889153)
        ·
          refine ⟨15214248827381125155666865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20285665103174833540889153 15214248827381125155666865)
          ·
            refine ⟨11410686620535843866750149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15214248827381125155666865 11410686620535843866750149)
            ·
              refine ⟨2139503741350470725015653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11410686620535843866750149 2139503741350470725015653)
              ·
                refine ⟨401156951503213260940435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2139503741350470725015653 401156951503213260940435)
                ·
                  refine ⟨601735427254819891410653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401156951503213260940435 601735427254819891410653)
                  ·
                    refine ⟨225650785220557459278995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601735427254819891410653 225650785220557459278995)
                    ·
                      rfl

theorem cell22_659180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_659180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659180 prefixEnd_659180 := by exact prefixLift 659180
  have htrace : WordTrace (prefixWord ++ tailWord_659180) baseStart_659180 baseEnd_659180 := by
    simpa [prefixWord, tailWord_659180, baseEnd_659180] using wordTrace_append hprefix tailTrace_659180
  have hstable : (prefixWord ++ tailWord_659180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659180).length < 2 ^ (prefixWord ++ tailWord_659180).sum := by decide
  have hdescent : baseEnd_659180 < baseStart_659180 := by decide
  rcases family_descends (prefixWord ++ tailWord_659180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659191 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 2, 5]
def baseStart_659191 : Nat := 118140960795 + 659191 * 2 ^ 59
def prefixEnd_659191 : Nat := 4983230072969 + 3 ^ 40 * 659191 * 2
def baseEnd_659191 : Nat := 225654550745357097253961

theorem tailTrace_659191 : CollatzResearch.WordTrace tailWord_659191 prefixEnd_659191 225654550745357097253961 := by
  unfold tailWord_659191
  simp only [CollatzResearch.WordTrace]
  refine ⟨24042670954871062704889427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16028447303247375136592951 24042670954871062704889427)
  ·
    refine ⟨36064006432306594057334141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24042670954871062704889427 36064006432306594057334141)
    ·
      refine ⟨13524002412114972771500303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36064006432306594057334141 13524002412114972771500303)
      ·
        refine ⟨20286003618172459157250455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13524002412114972771500303 20286003618172459157250455)
        ·
          refine ⟨30429005427258688735875683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20286003618172459157250455 30429005427258688735875683)
          ·
            refine ⟨45643508140888033103813525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30429005427258688735875683 45643508140888033103813525)
            ·
              refine ⟨2139539444104126551741259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45643508140888033103813525 2139539444104126551741259)
              ·
                refine ⟨3209309166156189827611889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139539444104126551741259 3209309166156189827611889)
                ·
                  refine ⟨2406981874617142370708917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3209309166156189827611889 2406981874617142370708917)
                  ·
                    refine ⟨225654550745357097253961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2406981874617142370708917 225654550745357097253961)
                    ·
                      rfl

theorem cell22_659191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_659191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659191 prefixEnd_659191 := by exact prefixLift 659191
  have htrace : WordTrace (prefixWord ++ tailWord_659191) baseStart_659191 baseEnd_659191 := by
    simpa [prefixWord, tailWord_659191, baseEnd_659191] using wordTrace_append hprefix tailTrace_659191
  have hstable : (prefixWord ++ tailWord_659191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659191).length < 2 ^ (prefixWord ++ tailWord_659191).sum := by decide
  have hdescent : baseEnd_659191 < baseStart_659191 := by decide
  rcases family_descends (prefixWord ++ tailWord_659191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659287 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 2, 3]
def baseStart_659287 : Nat := 118140960795 + 659287 * 2 ^ 59
def prefixEnd_659287 : Nat := 4983230072969 + 3 ^ 40 * 659287 * 2
def baseEnd_659287 : Nat := 225687413507244846853667

theorem tailTrace_659287 : CollatzResearch.WordTrace tailWord_659287 prefixEnd_659287 225687413507244846853667 := by
  unfold tailWord_659287
  simp only [CollatzResearch.WordTrace]
  refine ⟨24046172362523271100384115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16030781575015514066922743 24046172362523271100384115)
  ·
    refine ⟨36069258543784906650576173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24046172362523271100384115 36069258543784906650576173)
    ·
      refine ⟨13525971953919339993966065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36069258543784906650576173 13525971953919339993966065)
      ·
        refine ⟨10144478965439504995474549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13525971953919339993966065 10144478965439504995474549)
        ·
          refine ⟨951044903009953593325739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10144478965439504995474549 951044903009953593325739)
          ·
            refine ⟨1426567354514930389988609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951044903009953593325739 1426567354514930389988609)
            ·
              refine ⟨1069925515886197792491457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1426567354514930389988609 1069925515886197792491457)
              ·
                refine ⟨802444136914648344368593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1069925515886197792491457 802444136914648344368593)
                ·
                  refine ⟨601833102685986258276445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 802444136914648344368593 601833102685986258276445)
                  ·
                    refine ⟨225687413507244846853667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601833102685986258276445 225687413507244846853667)
                    ·
                      rfl

theorem cell22_659287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_659287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659287 prefixEnd_659287 := by exact prefixLift 659287
  have htrace : WordTrace (prefixWord ++ tailWord_659287) baseStart_659287 baseEnd_659287 := by
    simpa [prefixWord, tailWord_659287, baseEnd_659287] using wordTrace_append hprefix tailTrace_659287
  have hstable : (prefixWord ++ tailWord_659287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659287).length < 2 ^ (prefixWord ++ tailWord_659287).sum := by decide
  have hdescent : baseEnd_659287 < baseStart_659287 := by decide
  rcases family_descends (prefixWord ++ tailWord_659287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659300 : List Nat := [2, 3, 1, 1, 5, 2, 1, 7]
def baseStart_659300 : Nat := 118140960795 + 659300 * 2 ^ 59
def prefixEnd_659300 : Nat := 4983230072969 + 3 ^ 40 * 659300 * 2
def baseEnd_659300 : Nat := 25076873741435238475403

theorem tailTrace_659300 : CollatzResearch.WordTrace tailWord_659300 prefixEnd_659300 25076873741435238475403 := by
  unfold tailWord_659300
  simp only [CollatzResearch.WordTrace]
  refine ⟨12023323255738087160303677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16031097674317449547071569 12023323255738087160303677)
  ·
    refine ⟨4508746220901782685113879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12023323255738087160303677 4508746220901782685113879)
    ·
      refine ⟨6763119331352674027670819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4508746220901782685113879 6763119331352674027670819)
      ·
        refine ⟨10144678997029011041506229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6763119331352674027670819 10144678997029011041506229)
        ·
          refine ⟨951063655971469785141209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10144678997029011041506229 951063655971469785141209)
          ·
            refine ⟨713297741978602338855907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 951063655971469785141209 713297741978602338855907)
            ·
              refine ⟨1069946612967903508283861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713297741978602338855907 1069946612967903508283861)
              ·
                refine ⟨25076873741435238475403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1069946612967903508283861 25076873741435238475403)
                ·
                  rfl

theorem cell22_659300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 7].length) (baseStart_659300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659300 prefixEnd_659300 := by exact prefixLift 659300
  have htrace : WordTrace (prefixWord ++ tailWord_659300) baseStart_659300 baseEnd_659300 := by
    simpa [prefixWord, tailWord_659300, baseEnd_659300] using wordTrace_append hprefix tailTrace_659300
  have hstable : (prefixWord ++ tailWord_659300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659300).length < 2 ^ (prefixWord ++ tailWord_659300).sum := by decide
  have hdescent : baseEnd_659300 < baseStart_659300 := by decide
  rcases family_descends (prefixWord ++ tailWord_659300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659311 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 11]
def baseStart_659311 : Nat := 118140960795 + 659311 * 2 ^ 59
def prefixEnd_659311 : Nat := 4983230072969 + 3 ^ 40 * 659311 * 2
def baseEnd_659311 : Nat := 75231876399238928084531

theorem tailTrace_659311 : CollatzResearch.WordTrace tailWord_659311 prefixEnd_659311 75231876399238928084531 := by
  unfold tailWord_659311
  simp only [CollatzResearch.WordTrace]
  refine ⟨24047047714436323199257787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16031365142957548799505191 24047047714436323199257787)
  ·
    refine ⟨36070571571654484798886681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24047047714436323199257787 36070571571654484798886681)
    ·
      refine ⟨27052928678740863599165011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36070571571654484798886681 27052928678740863599165011)
      ·
        refine ⟨40579393018111295398747517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27052928678740863599165011 40579393018111295398747517)
        ·
          refine ⟨15217272381791735774530319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40579393018111295398747517 15217272381791735774530319)
          ·
            refine ⟨22825908572687603661795479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15217272381791735774530319 22825908572687603661795479)
            ·
              refine ⟨34238862859031405492693219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22825908572687603661795479 34238862859031405492693219)
              ·
                refine ⟨51358294288547108239039829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34238862859031405492693219 51358294288547108239039829)
                ·
                  refine ⟨75231876399238928084531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 51358294288547108239039829 75231876399238928084531)
                  ·
                    rfl

theorem cell22_659311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 11].length) (baseStart_659311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659311 prefixEnd_659311 := by exact prefixLift 659311
  have htrace : WordTrace (prefixWord ++ tailWord_659311) baseStart_659311 baseEnd_659311 := by
    simpa [prefixWord, tailWord_659311, baseEnd_659311] using wordTrace_append hprefix tailTrace_659311
  have hstable : (prefixWord ++ tailWord_659311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659311).length < 2 ^ (prefixWord ++ tailWord_659311).sum := by decide
  have hdescent : baseEnd_659311 < baseStart_659311 := by decide
  rcases family_descends (prefixWord ++ tailWord_659311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659332 : List Nat := [2, 3, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_659332 : Nat := 118140960795 + 659332 * 2 ^ 59
def prefixEnd_659332 : Nat := 4983230072969 + 3 ^ 40 * 659332 * 2
def baseEnd_659332 : Nat := 225702817926879729478529

theorem tailTrace_659332 : CollatzResearch.WordTrace tailWord_659332 prefixEnd_659332 225702817926879729478529 := by
  unfold tailWord_659332
  simp only [CollatzResearch.WordTrace]
  refine ⟨12023906823680121892886125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16031875764906829190514833 12023906823680121892886125)
  ·
    refine ⟨4508965058880045709832297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12023906823680121892886125 4508965058880045709832297)
    ·
      refine ⟨3381723794160034282374223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4508965058880045709832297 3381723794160034282374223)
      ·
        refine ⟨5072585691240051423561335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3381723794160034282374223 5072585691240051423561335)
        ·
          refine ⟨7608878536860077135342003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5072585691240051423561335 7608878536860077135342003)
          ·
            refine ⟨11413317805290115703013005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7608878536860077135342003 11413317805290115703013005)
            ·
              refine ⟨4279994176983793388629877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11413317805290115703013005 4279994176983793388629877)
              ·
                refine ⟨401249454092230630184051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4279994176983793388629877 401249454092230630184051)
                ·
                  refine ⟨601874181138345945276077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401249454092230630184051 601874181138345945276077)
                  ·
                    refine ⟨225702817926879729478529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601874181138345945276077 225702817926879729478529)
                    ·
                      rfl

theorem cell22_659332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_659332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659332 prefixEnd_659332 := by exact prefixLift 659332
  have htrace : WordTrace (prefixWord ++ tailWord_659332) baseStart_659332 baseEnd_659332 := by
    simpa [prefixWord, tailWord_659332, baseEnd_659332] using wordTrace_append hprefix tailTrace_659332
  have hstable : (prefixWord ++ tailWord_659332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659332).length < 2 ^ (prefixWord ++ tailWord_659332).sum := by decide
  have hdescent : baseEnd_659332 < baseStart_659332 := by decide
  rcases family_descends (prefixWord ++ tailWord_659332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659375 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 1, 4]
def baseStart_659375 : Nat := 118140960795 + 659375 * 2 ^ 59
def prefixEnd_659375 : Nat := 4983230072969 + 3 ^ 40 * 659375 * 2
def baseEnd_659375 : Nat := 225717537705641950653397

theorem tailTrace_659375 : CollatzResearch.WordTrace tailWord_659375 prefixEnd_659375 225717537705641950653397 := by
  unfold tailWord_659375
  simp only [CollatzResearch.WordTrace]
  refine ⟨24049381986204462129587579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16032921324136308086391719 24049381986204462129587579)
  ·
    refine ⟨36074072979306693194381369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24049381986204462129587579 36074072979306693194381369)
    ·
      refine ⟨27055554734480019895786027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36074072979306693194381369 27055554734480019895786027)
      ·
        refine ⟨40583332101720029843679041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27055554734480019895786027 40583332101720029843679041)
        ·
          refine ⟨30437499076290022382759281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40583332101720029843679041 30437499076290022382759281)
          ·
            refine ⟨22828124307217516787069461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30437499076290022382759281 22828124307217516787069461)
            ·
              refine ⟨1070068326900821099393881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22828124307217516787069461 1070068326900821099393881)
              ·
                refine ⟨802551245175615824545411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1070068326900821099393881 802551245175615824545411)
                ·
                  refine ⟨1203826867763423736818117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802551245175615824545411 1203826867763423736818117)
                  ·
                    refine ⟨225717537705641950653397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203826867763423736818117 225717537705641950653397)
                    ·
                      rfl

theorem cell22_659375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_659375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659375 prefixEnd_659375 := by exact prefixLift 659375
  have htrace : WordTrace (prefixWord ++ tailWord_659375) baseStart_659375 baseEnd_659375 := by
    simpa [prefixWord, tailWord_659375, baseEnd_659375] using wordTrace_append hprefix tailTrace_659375
  have hstable : (prefixWord ++ tailWord_659375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659375).length < 2 ^ (prefixWord ++ tailWord_659375).sum := by decide
  have hdescent : baseEnd_659375 < baseStart_659375 := by decide
  rcases family_descends (prefixWord ++ tailWord_659375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659407 : List Nat := [1, 1, 2, 1, 1, 5, 5, 2, 4]
def baseStart_659407 : Nat := 118140960795 + 659407 * 2 ^ 59
def prefixEnd_659407 : Nat := 4983230072969 + 3 ^ 40 * 659407 * 2
def baseEnd_659407 : Nat := 75242830653201511284433

theorem tailTrace_659407 : CollatzResearch.WordTrace tailWord_659407 prefixEnd_659407 75242830653201511284433 := by
  unfold tailWord_659407
  simp only [CollatzResearch.WordTrace]
  refine ⟨24050549122088531594752475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16033699414725687729834983 24050549122088531594752475)
  ·
    refine ⟨36075823683132797392128713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24050549122088531594752475 36075823683132797392128713)
    ·
      refine ⟨27056867762349598044096535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36075823683132797392128713 27056867762349598044096535)
      ·
        refine ⟨40585301643524397066144803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27056867762349598044096535 40585301643524397066144803)
        ·
          refine ⟨60877952465286595599217205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40585301643524397066144803 60877952465286595599217205)
          ·
            refine ⟨5707308043620618337426613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60877952465286595599217205 5707308043620618337426613)
            ·
              refine ⟨535060129089432969133745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5707308043620618337426613 535060129089432969133745)
              ·
                refine ⟨401295096817074726850309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535060129089432969133745 401295096817074726850309)
                ·
                  refine ⟨75242830653201511284433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 401295096817074726850309 75242830653201511284433)
                  ·
                    rfl

theorem cell22_659407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 4].length) (baseStart_659407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659407 prefixEnd_659407 := by exact prefixLift 659407
  have htrace : WordTrace (prefixWord ++ tailWord_659407) baseStart_659407 baseEnd_659407 := by
    simpa [prefixWord, tailWord_659407, baseEnd_659407] using wordTrace_append hprefix tailTrace_659407
  have hstable : (prefixWord ++ tailWord_659407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659407).length < 2 ^ (prefixWord ++ tailWord_659407).sum := by decide
  have hdescent : baseEnd_659407 < baseStart_659407 := by decide
  rcases family_descends (prefixWord ++ tailWord_659407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659426 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_659426 : Nat := 118140960795 + 659426 * 2 ^ 59
def prefixEnd_659426 : Nat := 4983230072969 + 3 ^ 40 * 659426 * 2
def baseEnd_659426 : Nat := 225734996047894817628241

theorem tailTrace_659426 : CollatzResearch.WordTrace tailWord_659426 prefixEnd_659426 225734996047894817628241 := by
  unfold tailWord_659426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012810527254924459923533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16034161406013131893129421 6012810527254924459923533)
  ·
    refine ⟨2254803947720596672471325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6012810527254924459923533 2254803947720596672471325)
    ·
      refine ⟨845551480395223752176747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2254803947720596672471325 845551480395223752176747)
      ·
        refine ⟨1268327220592835628265121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 845551480395223752176747 1268327220592835628265121)
        ·
          refine ⟨951245415444626721198841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1268327220592835628265121 951245415444626721198841)
          ·
            refine ⟨713434061583470040899131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 951245415444626721198841 713434061583470040899131)
            ·
              refine ⟨1070151092375205061348697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713434061583470040899131 1070151092375205061348697)
              ·
                refine ⟨802613319281403796011523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1070151092375205061348697 802613319281403796011523)
                ·
                  refine ⟨1203919978922105694017285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802613319281403796011523 1203919978922105694017285)
                  ·
                    refine ⟨225734996047894817628241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203919978922105694017285 225734996047894817628241)
                    ·
                      rfl

theorem cell22_659426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_659426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659426 prefixEnd_659426 := by exact prefixLift 659426
  have htrace : WordTrace (prefixWord ++ tailWord_659426) baseStart_659426 baseEnd_659426 := by
    simpa [prefixWord, tailWord_659426, baseEnd_659426] using wordTrace_append hprefix tailTrace_659426
  have hstable : (prefixWord ++ tailWord_659426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659426).length < 2 ^ (prefixWord ++ tailWord_659426).sum := by decide
  have hdescent : baseEnd_659426 < baseStart_659426 := by decide
  rcases family_descends (prefixWord ++ tailWord_659426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659480 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 5]
def baseStart_659480 : Nat := 118140960795 + 659480 * 2 ^ 59
def prefixEnd_659480 : Nat := 4983230072969 + 3 ^ 40 * 659480 * 2
def baseEnd_659480 : Nat := 75251160450485558926025

theorem tailTrace_659480 : CollatzResearch.WordTrace tailWord_659480 prefixEnd_659480 75251160450485558926025 := by
  unfold tailWord_659480
  simp only [CollatzResearch.WordTrace]
  refine ⟨12026605825412032531079947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16035474433882710041439929 12026605825412032531079947)
  ·
    refine ⟨18039908738118048796619921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12026605825412032531079947 18039908738118048796619921)
    ·
      refine ⟨13529931553588536597464941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18039908738118048796619921 13529931553588536597464941)
      ·
        refine ⟨5073724332595701224049353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13529931553588536597464941 5073724332595701224049353)
        ·
          refine ⟨3805293249446775918037015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5073724332595701224049353 3805293249446775918037015)
          ·
            refine ⟨5707939874170163877055523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3805293249446775918037015 5707939874170163877055523)
            ·
              refine ⟨8561909811255245815583285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5707939874170163877055523 8561909811255245815583285)
              ·
                refine ⟨802679044805179295210933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8561909811255245815583285 802679044805179295210933)
                ·
                  refine ⟨75251160450485558926025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 802679044805179295210933 75251160450485558926025)
                  ·
                    rfl

theorem cell22_659480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_659480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659480 prefixEnd_659480 := by exact prefixLift 659480
  have htrace : WordTrace (prefixWord ++ tailWord_659480) baseStart_659480 baseEnd_659480 := by
    simpa [prefixWord, tailWord_659480, baseEnd_659480] using wordTrace_append hprefix tailTrace_659480
  have hstable : (prefixWord ++ tailWord_659480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659480).length < 2 ^ (prefixWord ++ tailWord_659480).sum := by decide
  have hdescent : baseEnd_659480 < baseStart_659480 := by decide
  rcases family_descends (prefixWord ++ tailWord_659480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659555 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 1, 6]
def baseStart_659555 : Nat := 118140960795 + 659555 * 2 ^ 59
def prefixEnd_659555 : Nat := 4983230072969 + 3 ^ 40 * 659555 * 2
def baseEnd_659555 : Nat := 225779155384181481152845

theorem tailTrace_659555 : CollatzResearch.WordTrace tailWord_659555 prefixEnd_659555 225779155384181481152845 := by
  unfold tailWord_659555
  simp only [CollatzResearch.WordTrace]
  refine ⟨24055947125552352871140119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16037298083701568580760079 24055947125552352871140119)
  ·
    refine ⟨36083920688328529306710179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24055947125552352871140119 36083920688328529306710179)
    ·
      refine ⟨54125881032492793960065269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36083920688328529306710179 54125881032492793960065269)
      ·
        refine ⟨5074301346796199433756119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54125881032492793960065269 5074301346796199433756119)
        ·
          refine ⟨7611452020194299150634179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5074301346796199433756119 7611452020194299150634179)
          ·
            refine ⟨11417178030291448725951269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7611452020194299150634179 11417178030291448725951269)
            ·
              refine ⟨2140720880679646636115863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11417178030291448725951269 2140720880679646636115863)
              ·
                refine ⟨3211081321019469954173795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2140720880679646636115863 3211081321019469954173795)
                ·
                  refine ⟨4816621981529204931260693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211081321019469954173795 4816621981529204931260693)
                  ·
                    refine ⟨225779155384181481152845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4816621981529204931260693 225779155384181481152845)
                    ·
                      rfl

theorem cell22_659555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 6].length) (baseStart_659555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659555 prefixEnd_659555 := by exact prefixLift 659555
  have htrace : WordTrace (prefixWord ++ tailWord_659555) baseStart_659555 baseEnd_659555 := by
    simpa [prefixWord, tailWord_659555, baseEnd_659555] using wordTrace_append hprefix tailTrace_659555
  have hstable : (prefixWord ++ tailWord_659555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659555).length < 2 ^ (prefixWord ++ tailWord_659555).sum := by decide
  have hdescent : baseEnd_659555 < baseStart_659555 := by decide
  rcases family_descends (prefixWord ++ tailWord_659555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659557 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 4, 3]
def baseStart_659557 : Nat := 118140960795 + 659557 * 2 ^ 59
def prefixEnd_659557 : Nat := 4983230072969 + 3 ^ 40 * 659557 * 2
def baseEnd_659557 : Nat := 225779840025054142602839

theorem tailTrace_659557 : CollatzResearch.WordTrace tailWord_659557 prefixEnd_659557 225779840025054142602839 := by
  unfold tailWord_659557
  simp only [CollatzResearch.WordTrace]
  refine ⟨24056020071545107212712925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16037346714363404808475283 24056020071545107212712925)
  ·
    refine ⟨9021007526829415204767347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24056020071545107212712925 9021007526829415204767347)
    ·
      refine ⟨13531511290244122807151021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9021007526829415204767347 13531511290244122807151021)
      ·
        refine ⟨5074316733841546052681633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13531511290244122807151021 5074316733841546052681633)
        ·
          refine ⟨3805737550381159539511225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5074316733841546052681633 3805737550381159539511225)
          ·
            refine ⟨2854303162785869654633419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3805737550381159539511225 2854303162785869654633419)
            ·
              refine ⟨4281454744178804481950129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854303162785869654633419 4281454744178804481950129)
              ·
                refine ⟨3211091058134103361462597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4281454744178804481950129 3211091058134103361462597)
                ·
                  refine ⟨602079573400144380274237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3211091058134103361462597 602079573400144380274237)
                  ·
                    refine ⟨225779840025054142602839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 602079573400144380274237 225779840025054142602839)
                    ·
                      rfl

theorem cell22_659557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_659557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659557 prefixEnd_659557 := by exact prefixLift 659557
  have htrace : WordTrace (prefixWord ++ tailWord_659557) baseStart_659557 baseEnd_659557 := by
    simpa [prefixWord, tailWord_659557, baseEnd_659557] using wordTrace_append hprefix tailTrace_659557
  have hstable : (prefixWord ++ tailWord_659557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659557).length < 2 ^ (prefixWord ++ tailWord_659557).sum := by decide
  have hdescent : baseEnd_659557 < baseStart_659557 := by decide
  rcases family_descends (prefixWord ++ tailWord_659557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659570 : List Nat := [3, 2, 1, 2, 2, 2, 10]
def baseStart_659570 : Nat := 118140960795 + 659570 * 2 ^ 59
def prefixEnd_659570 : Nat := 4983230072969 + 3 ^ 40 * 659570 * 2
def baseEnd_659570 : Nat := 8362381118175053408437

theorem tailTrace_659570 : CollatzResearch.WordTrace tailWord_659570 prefixEnd_659570 8362381118175053408437 := by
  unfold tailWord_659570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6014123555124502608234041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16037662813665340288624109 6014123555124502608234041)
  ·
    refine ⟨4510592666343376956175531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6014123555124502608234041 4510592666343376956175531)
    ·
      refine ⟨6765888999515065434263297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4510592666343376956175531 6765888999515065434263297)
      ·
        refine ⟨5074416749636299075697473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6765888999515065434263297 5074416749636299075697473)
        ·
          refine ⟨3805812562227224306773105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5074416749636299075697473 3805812562227224306773105)
          ·
            refine ⟨2854359421670418230079829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3805812562227224306773105 2854359421670418230079829)
            ·
              refine ⟨8362381118175053408437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2854359421670418230079829 8362381118175053408437)
              ·
                rfl

theorem cell22_659570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 10].length) (baseStart_659570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659570 prefixEnd_659570 := by exact prefixLift 659570
  have htrace : WordTrace (prefixWord ++ tailWord_659570) baseStart_659570 baseEnd_659570 := by
    simpa [prefixWord, tailWord_659570, baseEnd_659570] using wordTrace_append hprefix tailTrace_659570
  have hstable : (prefixWord ++ tailWord_659570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659570).length < 2 ^ (prefixWord ++ tailWord_659570).sum := by decide
  have hdescent : baseEnd_659570 < baseStart_659570 := by decide
  rcases family_descends (prefixWord ++ tailWord_659570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659574 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_659574 : Nat := 118140960795 + 659574 * 2 ^ 59
def prefixEnd_659574 : Nat := 4983230072969 + 3 ^ 40 * 659574 * 2
def baseEnd_659574 : Nat := 225785659472471764927787

theorem tailTrace_659574 : CollatzResearch.WordTrace tailWord_659574 prefixEnd_659574 225785659472471764927787 := by
  unfold tailWord_659574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503540007030219944755111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16037760074989012744054517 1503540007030219944755111)
  ·
    refine ⟨2255310010545329917132667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1503540007030219944755111 2255310010545329917132667)
    ·
      refine ⟨3382965015817994875699001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255310010545329917132667 3382965015817994875699001)
      ·
        refine ⟨2537223761863496156774251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3382965015817994875699001 2537223761863496156774251)
        ·
          refine ⟨3805835642795244235161377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537223761863496156774251 3805835642795244235161377)
          ·
            refine ⟨2854376732096433176371033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3805835642795244235161377 2854376732096433176371033)
            ·
              refine ⟨2140782549072324882278275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2854376732096433176371033 2140782549072324882278275)
              ·
                refine ⟨3211173823608487323417413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2140782549072324882278275 3211173823608487323417413)
                ·
                  refine ⟨602095091926591373140765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3211173823608487323417413 602095091926591373140765)
                  ·
                    refine ⟨225785659472471764927787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 602095091926591373140765 225785659472471764927787)
                    ·
                      rfl

theorem cell22_659574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_659574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659574 prefixEnd_659574 := by exact prefixLift 659574
  have htrace : WordTrace (prefixWord ++ tailWord_659574) baseStart_659574 baseEnd_659574 := by
    simpa [prefixWord, tailWord_659574, baseEnd_659574] using wordTrace_append hprefix tailTrace_659574
  have hstable : (prefixWord ++ tailWord_659574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659574).length < 2 ^ (prefixWord ++ tailWord_659574).sum := by decide
  have hdescent : baseEnd_659574 < baseStart_659574 := by decide
  rcases family_descends (prefixWord ++ tailWord_659574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659670 : List Nat := [5, 2, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_659670 : Nat := 118140960795 + 659670 * 2 ^ 59
def prefixEnd_659670 : Nat := 4983230072969 + 3 ^ 40 * 659670 * 2
def baseEnd_659670 : Nat := 225818522234359514527493

theorem tailTrace_659670 : CollatzResearch.WordTrace tailWord_659670 prefixEnd_659670 225818522234359514527493 := by
  unfold tailWord_659670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503758845008482969473529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16040094346757151674384309 1503758845008482969473529)
  ·
    refine ⟨1127819133756362227105147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1503758845008482969473529 1127819133756362227105147)
    ·
      refine ⟨1691728700634543340657721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127819133756362227105147 1691728700634543340657721)
      ·
        refine ⟨1268796525475907505493291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1691728700634543340657721 1268796525475907505493291)
        ·
          refine ⟨1903194788213861258239937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268796525475907505493291 1903194788213861258239937)
          ·
            refine ⟨1427396091160395943679953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1903194788213861258239937 1427396091160395943679953)
            ·
              refine ⟨1070547068370296957759965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1427396091160395943679953 1070547068370296957759965)
              ·
                refine ⟨401455150638861359159987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1070547068370296957759965 401455150638861359159987)
                ·
                  refine ⟨602182725958292038739981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401455150638861359159987 602182725958292038739981)
                  ·
                    refine ⟨225818522234359514527493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 602182725958292038739981 225818522234359514527493)
                    ·
                      rfl

theorem cell22_659670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_659670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659670 prefixEnd_659670 := by exact prefixLift 659670
  have htrace : WordTrace (prefixWord ++ tailWord_659670) baseStart_659670 baseEnd_659670 := by
    simpa [prefixWord, tailWord_659670, baseEnd_659670] using wordTrace_append hprefix tailTrace_659670
  have hstable : (prefixWord ++ tailWord_659670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659670).length < 2 ^ (prefixWord ++ tailWord_659670).sum := by decide
  have hdescent : baseEnd_659670 < baseStart_659670 := by decide
  rcases family_descends (prefixWord ++ tailWord_659670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659683 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 5]
def baseStart_659683 : Nat := 118140960795 + 659683 * 2 ^ 59
def prefixEnd_659683 : Nat := 4983230072969 + 3 ^ 40 * 659683 * 2
def baseEnd_659683 : Nat := 75274324133343937984151

theorem tailTrace_659683 : CollatzResearch.WordTrace tailWord_659683 prefixEnd_659683 75274324133343937984151 := by
  unfold tailWord_659683
  simp only [CollatzResearch.WordTrace]
  refine ⟨24060615669088630731799703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16040410446059087154533135 24060615669088630731799703)
  ·
    refine ⟨36090923503632946097699555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24060615669088630731799703 36090923503632946097699555)
    ·
      refine ⟨54136385255449419146549333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36090923503632946097699555 54136385255449419146549333)
      ·
        refine ⟨634410764712297880623625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 54136385255449419146549333 634410764712297880623625)
        ·
          refine ⟨475808073534223410467719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634410764712297880623625 475808073534223410467719)
          ·
            refine ⟨713712110301335115701579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475808073534223410467719 713712110301335115701579)
            ·
              refine ⟨1070568165452002673552369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713712110301335115701579 1070568165452002673552369)
              ·
                refine ⟨802926124089002005164277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1070568165452002673552369 802926124089002005164277)
                ·
                  refine ⟨75274324133343937984151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 802926124089002005164277 75274324133343937984151)
                  ·
                    rfl

theorem cell22_659683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 5].length) (baseStart_659683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659683 prefixEnd_659683 := by exact prefixLift 659683
  have htrace : WordTrace (prefixWord ++ tailWord_659683) baseStart_659683 baseEnd_659683 := by
    simpa [prefixWord, tailWord_659683, baseEnd_659683] using wordTrace_append hprefix tailTrace_659683
  have hstable : (prefixWord ++ tailWord_659683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659683).length < 2 ^ (prefixWord ++ tailWord_659683).sum := by decide
  have hdescent : baseEnd_659683 < baseStart_659683 := by decide
  rcases family_descends (prefixWord ++ tailWord_659683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659709 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_659709 : Nat := 118140960795 + 659709 * 2 ^ 59
def prefixEnd_659709 : Nat := 4983230072969 + 3 ^ 40 * 659709 * 2
def baseEnd_659709 : Nat := 225831872731376412802373

theorem tailTrace_659709 : CollatzResearch.WordTrace tailWord_659709 prefixEnd_659709 225831872731376412802373 := by
  unfold tailWord_659709
  simp only [CollatzResearch.WordTrace]
  refine ⟨24061563966994437172246181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16041042644662958114830787 24061563966994437172246181)
  ·
    refine ⟨4511543243811456969796159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24061563966994437172246181 4511543243811456969796159)
    ·
      refine ⟨6767314865717185454694239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4511543243811456969796159 6767314865717185454694239)
      ·
        refine ⟨10150972298575778182041359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6767314865717185454694239 10150972298575778182041359)
        ·
          refine ⟨15226458447863667273062039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10150972298575778182041359 15226458447863667273062039)
          ·
            refine ⟨22839687671795500909593059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15226458447863667273062039 22839687671795500909593059)
            ·
              refine ⟨34259531507693251364389589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22839687671795500909593059 34259531507693251364389589)
              ·
                refine ⟨802957769711560578852881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34259531507693251364389589 802957769711560578852881)
                ·
                  refine ⟨602218327283670434139661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 802957769711560578852881 602218327283670434139661)
                  ·
                    refine ⟨225831872731376412802373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 602218327283670434139661 225831872731376412802373)
                    ·
                      rfl

theorem cell22_659709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_659709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659709 prefixEnd_659709 := by exact prefixLift 659709
  have htrace : WordTrace (prefixWord ++ tailWord_659709) baseStart_659709 baseEnd_659709 := by
    simpa [prefixWord, tailWord_659709, baseEnd_659709] using wordTrace_append hprefix tailTrace_659709
  have hstable : (prefixWord ++ tailWord_659709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659709).length < 2 ^ (prefixWord ++ tailWord_659709).sum := by decide
  have hdescent : baseEnd_659709 < baseStart_659709 := by decide
  rcases family_descends (prefixWord ++ tailWord_659709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659741 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_659741 : Nat := 118140960795 + 659741 * 2 ^ 59
def prefixEnd_659741 : Nat := 4983230072969 + 3 ^ 40 * 659741 * 2
def baseEnd_659741 : Nat := 225842826985338996002275

theorem tailTrace_659741 : CollatzResearch.WordTrace tailWord_659741 prefixEnd_659741 225842826985338996002275 := by
  unfold tailWord_659741
  simp only [CollatzResearch.WordTrace]
  refine ⟨24062731102878506637411077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16041820735252337758274051 24062731102878506637411077)
  ·
    refine ⟨4511762081789719994514577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24062731102878506637411077 4511762081789719994514577)
    ·
      refine ⟨3383821561342289995885933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4511762081789719994514577 3383821561342289995885933)
      ·
        refine ⟨1268933085503358748457225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3383821561342289995885933 1268933085503358748457225)
        ·
          refine ⟨951699814127519061342919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1268933085503358748457225 951699814127519061342919)
          ·
            refine ⟨1427549721191278592014379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951699814127519061342919 1427549721191278592014379)
            ·
              refine ⟨2141324581786917888021569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427549721191278592014379 2141324581786917888021569)
              ·
                refine ⟨1605993436340188416016177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2141324581786917888021569 1605993436340188416016177)
                ·
                  refine ⟨1204495077255141312012133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605993436340188416016177 1204495077255141312012133)
                  ·
                    refine ⟨225842826985338996002275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1204495077255141312012133 225842826985338996002275)
                    ·
                      rfl

theorem cell22_659741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_659741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659741 prefixEnd_659741 := by exact prefixLift 659741
  have htrace : WordTrace (prefixWord ++ tailWord_659741) baseStart_659741 baseEnd_659741 := by
    simpa [prefixWord, tailWord_659741, baseEnd_659741] using wordTrace_append hprefix tailTrace_659741
  have hstable : (prefixWord ++ tailWord_659741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659741).length < 2 ^ (prefixWord ++ tailWord_659741).sum := by decide
  have hdescent : baseEnd_659741 < baseStart_659741 := by decide
  rcases family_descends (prefixWord ++ tailWord_659741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659827 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 5, 5]
def baseStart_659827 : Nat := 118140960795 + 659827 * 2 ^ 59
def prefixEnd_659827 : Nat := 4983230072969 + 3 ^ 40 * 659827 * 2
def baseEnd_659827 : Nat := 225872266542863438352011

theorem tailTrace_659827 : CollatzResearch.WordTrace tailWord_659827 prefixEnd_659827 225872266542863438352011 := by
  unfold tailWord_659827
  simp only [CollatzResearch.WordTrace]
  refine ⟨24065867780566943325041735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16043911853711295550027823 24065867780566943325041735)
  ·
    refine ⟨36098801670850414987562603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24065867780566943325041735 36098801670850414987562603)
    ·
      refine ⟨54148202506275622481343905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36098801670850414987562603 54148202506275622481343905)
      ·
        refine ⟨40611151879706716861007929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54148202506275622481343905 40611151879706716861007929)
        ·
          refine ⟨30458363909780037645755947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40611151879706716861007929 30458363909780037645755947)
          ·
            refine ⟨45687545864670056468633921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30458363909780037645755947 45687545864670056468633921)
            ·
              refine ⟨34265659398502542351475441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45687545864670056468633921 34265659398502542351475441)
              ·
                refine ⟨25699244548876906763606581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34265659398502542351475441 25699244548876906763606581)
                ·
                  refine ⟨2409304176457210009088117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25699244548876906763606581 2409304176457210009088117)
                  ·
                    refine ⟨225872266542863438352011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2409304176457210009088117 225872266542863438352011)
                    ·
                      rfl

theorem cell22_659827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_659827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659827 prefixEnd_659827 := by exact prefixLift 659827
  have htrace : WordTrace (prefixWord ++ tailWord_659827) baseStart_659827 baseEnd_659827 := by
    simpa [prefixWord, tailWord_659827, baseEnd_659827] using wordTrace_append hprefix tailTrace_659827
  have hstable : (prefixWord ++ tailWord_659827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659827).length < 2 ^ (prefixWord ++ tailWord_659827).sum := by decide
  have hdescent : baseEnd_659827 < baseStart_659827 := by decide
  rcases family_descends (prefixWord ++ tailWord_659827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659829 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 8]
def baseStart_659829 : Nat := 118140960795 + 659829 * 2 ^ 59
def prefixEnd_659829 : Nat := 4983230072969 + 3 ^ 40 * 659829 * 2
def baseEnd_659829 : Nat := 75290983727912033267335

theorem tailTrace_659829 : CollatzResearch.WordTrace tailWord_659829 prefixEnd_659829 75290983727912033267335 := by
  unfold tailWord_659829
  simp only [CollatzResearch.WordTrace]
  refine ⟨24065940726559697666614541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16043960484373131777743027 24065940726559697666614541)
  ·
    refine ⟨9024727772459886624980453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24065940726559697666614541 9024727772459886624980453)
    ·
      refine ⟨1692136457336228742183835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9024727772459886624980453 1692136457336228742183835)
      ·
        refine ⟨2538204686004343113275753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692136457336228742183835 2538204686004343113275753)
        ·
          refine ⟨1903653514503257334956815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2538204686004343113275753 1903653514503257334956815)
          ·
            refine ⟨2855480271754886002435223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903653514503257334956815 2855480271754886002435223)
            ·
              refine ⟨4283220407632329003652835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2855480271754886002435223 4283220407632329003652835)
              ·
                refine ⟨6424830611448493505479253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283220407632329003652835 6424830611448493505479253)
                ·
                  refine ⟨75290983727912033267335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6424830611448493505479253 75290983727912033267335)
                  ·
                    rfl

theorem cell22_659829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_659829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659829 prefixEnd_659829 := by exact prefixLift 659829
  have htrace : WordTrace (prefixWord ++ tailWord_659829) baseStart_659829 baseEnd_659829 := by
    simpa [prefixWord, tailWord_659829, baseEnd_659829] using wordTrace_append hprefix tailTrace_659829
  have hstable : (prefixWord ++ tailWord_659829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659829).length < 2 ^ (prefixWord ++ tailWord_659829).sum := by decide
  have hdescent : baseEnd_659829 < baseStart_659829 := by decide
  rcases family_descends (prefixWord ++ tailWord_659829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659844 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_659844 : Nat := 118140960795 + 659844 * 2 ^ 59
def prefixEnd_659844 : Nat := 4983230072969 + 3 ^ 40 * 659844 * 2
def baseEnd_659844 : Nat := 225878085990281060676959

theorem tailTrace_659844 : CollatzResearch.WordTrace tailWord_659844 prefixEnd_659844 225878085990281060676959 := by
  unfold tailWord_659844
  simp only [CollatzResearch.WordTrace]
  refine ⟨12033243910752677614205293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16044325214336903485607057 12033243910752677614205293)
  ·
    refine ⟨4512466466532254105326985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12033243910752677614205293 4512466466532254105326985)
    ·
      refine ⟨3384349849899190578995239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4512466466532254105326985 3384349849899190578995239)
      ·
        refine ⟨5076524774848785868492859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3384349849899190578995239 5076524774848785868492859)
        ·
          refine ⟨7614787162273178802739289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5076524774848785868492859 7614787162273178802739289)
          ·
            refine ⟨5711090371704884102054467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7614787162273178802739289 5711090371704884102054467)
            ·
              refine ⟨8566635557557326153081701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5711090371704884102054467 8566635557557326153081701)
              ·
                refine ⟨1606244167041998653702819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8566635557557326153081701 1606244167041998653702819)
                ·
                  refine ⟨2409366250562997980554229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606244167041998653702819 2409366250562997980554229)
                  ·
                    refine ⟨225878085990281060676959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2409366250562997980554229 225878085990281060676959)
                    ·
                      rfl

theorem cell22_659844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_659844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659844 prefixEnd_659844 := by exact prefixLift 659844
  have htrace : WordTrace (prefixWord ++ tailWord_659844) baseStart_659844 baseEnd_659844 := by
    simpa [prefixWord, tailWord_659844, baseEnd_659844] using wordTrace_append hprefix tailTrace_659844
  have hstable : (prefixWord ++ tailWord_659844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659844).length < 2 ^ (prefixWord ++ tailWord_659844).sum := by decide
  have hdescent : baseEnd_659844 < baseStart_659844 := by decide
  rcases family_descends (prefixWord ++ tailWord_659844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659874 : List Nat := [3, 3, 1, 2, 1, 1, 2, 9]
def baseStart_659874 : Nat := 118140960795 + 659874 * 2 ^ 59
def prefixEnd_659874 : Nat := 4983230072969 + 3 ^ 40 * 659874 * 2
def baseEnd_659874 : Nat := 25098706178152331380763

theorem tailTrace_659874 : CollatzResearch.WordTrace tailWord_659874 prefixEnd_659874 25098706178152331380763 := by
  unfold tailWord_659874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6016895502849167588000669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16045054674264446901335117 6016895502849167588000669)
  ·
    refine ⟨2256335813568437845500251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6016895502849167588000669 2256335813568437845500251)
    ·
      refine ⟨3384503720352656768250377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2256335813568437845500251 3384503720352656768250377)
      ·
        refine ⟨2538377790264492576187783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3384503720352656768250377 2538377790264492576187783)
        ·
          refine ⟨3807566685396738864281675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538377790264492576187783 3807566685396738864281675)
          ·
            refine ⟨5711350028095108296422513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3807566685396738864281675 5711350028095108296422513)
            ·
              refine ⟨4283512521071331222316885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5711350028095108296422513 4283512521071331222316885)
              ·
                refine ⟨25098706178152331380763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4283512521071331222316885 25098706178152331380763)
                ·
                  rfl

theorem cell22_659874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_659874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659874 prefixEnd_659874 := by exact prefixLift 659874
  have htrace : WordTrace (prefixWord ++ tailWord_659874) baseStart_659874 baseEnd_659874 := by
    simpa [prefixWord, tailWord_659874, baseEnd_659874] using wordTrace_append hprefix tailTrace_659874
  have hstable : (prefixWord ++ tailWord_659874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659874).length < 2 ^ (prefixWord ++ tailWord_659874).sum := by decide
  have hdescent : baseEnd_659874 < baseStart_659874 := by decide
  rcases family_descends (prefixWord ++ tailWord_659874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659882 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 1, 4]
def baseStart_659882 : Nat := 118140960795 + 659882 * 2 ^ 59
def prefixEnd_659882 : Nat := 4983230072969 + 3 ^ 40 * 659882 * 2
def baseEnd_659882 : Nat := 225891094166861628226843

theorem tailTrace_659882 : CollatzResearch.WordTrace tailWord_659882 prefixEnd_659882 225891094166861628226843 := by
  unfold tailWord_659882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6016968448841921929573475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16045249196911791812195933 6016968448841921929573475)
  ·
    refine ⟨9025452673262882894360213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6016968448841921929573475 9025452673262882894360213)
    ·
      refine ⟨423068094059197635673135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9025452673262882894360213 423068094059197635673135)
      ·
        refine ⟨634602141088796453509703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423068094059197635673135 634602141088796453509703)
        ·
          refine ⟨951903211633194680264555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634602141088796453509703 951903211633194680264555)
          ·
            refine ⟨1427854817449792020396833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951903211633194680264555 1427854817449792020396833)
            ·
              refine ⟨1070891113087344015297625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1427854817449792020396833 1070891113087344015297625)
              ·
                refine ⟨803168334815508011473219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1070891113087344015297625 803168334815508011473219)
                ·
                  refine ⟨1204752502223262017209829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803168334815508011473219 1204752502223262017209829)
                  ·
                    refine ⟨225891094166861628226843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1204752502223262017209829 225891094166861628226843)
                    ·
                      rfl

theorem cell22_659882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_659882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659882 prefixEnd_659882 := by exact prefixLift 659882
  have htrace : WordTrace (prefixWord ++ tailWord_659882) baseStart_659882 baseEnd_659882 := by
    simpa [prefixWord, tailWord_659882, baseEnd_659882] using wordTrace_append hprefix tailTrace_659882
  have hstable : (prefixWord ++ tailWord_659882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659882).length < 2 ^ (prefixWord ++ tailWord_659882).sum := by decide
  have hdescent : baseEnd_659882 < baseStart_659882 := by decide
  rcases family_descends (prefixWord ++ tailWord_659882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659908 : List Nat := [2, 3, 3, 2, 3, 1, 8]
def baseStart_659908 : Nat := 118140960795 + 659908 * 2 ^ 59
def prefixEnd_659908 : Nat := 4983230072969 + 3 ^ 40 * 659908 * 2
def baseEnd_659908 : Nat := 8366666462896526928769

theorem tailTrace_659908 : CollatzResearch.WordTrace tailWord_659908 prefixEnd_659908 8366666462896526928769 := by
  unfold tailWord_659908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12034411046636747079370189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16045881395515662772493585 12034411046636747079370189)
  ·
    refine ⟨4512904142488780154763821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12034411046636747079370189 4512904142488780154763821)
    ·
      refine ⟨1692339053433292558036433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4512904142488780154763821 1692339053433292558036433)
      ·
        refine ⟨1269254290074969418527325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1692339053433292558036433 1269254290074969418527325)
        ·
          refine ⟨475970358778113531947747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1269254290074969418527325 475970358778113531947747)
          ·
            refine ⟨713955538167170297921621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475970358778113531947747 713955538167170297921621)
            ·
              refine ⟨8366666462896526928769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 713955538167170297921621 8366666462896526928769)
              ·
                rfl

theorem cell22_659908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 8].length) (baseStart_659908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659908 prefixEnd_659908 := by exact prefixLift 659908
  have htrace : WordTrace (prefixWord ++ tailWord_659908) baseStart_659908 baseEnd_659908 := by
    simpa [prefixWord, tailWord_659908, baseEnd_659908] using wordTrace_append hprefix tailTrace_659908
  have hstable : (prefixWord ++ tailWord_659908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659908).length < 2 ^ (prefixWord ++ tailWord_659908).sum := by decide
  have hdescent : baseEnd_659908 < baseStart_659908 := by decide
  rcases family_descends (prefixWord ++ tailWord_659908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659919 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 5]
def baseStart_659919 : Nat := 118140960795 + 659919 * 2 ^ 59
def prefixEnd_659919 : Nat := 4983230072969 + 3 ^ 40 * 659919 * 2
def baseEnd_659919 : Nat := 75301253341001955017243

theorem tailTrace_659919 : CollatzResearch.WordTrace tailWord_659919 prefixEnd_659919 75301253341001955017243 := by
  unfold tailWord_659919
  simp only [CollatzResearch.WordTrace]
  refine ⟨24069223296233643037390811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16046148864155762024927207 24069223296233643037390811)
  ·
    refine ⟨36103834944350464556086217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24069223296233643037390811 36103834944350464556086217)
    ·
      refine ⟨27077876208262848417064663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36103834944350464556086217 27077876208262848417064663)
      ·
        refine ⟨40616814312394272625596995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27077876208262848417064663 40616814312394272625596995)
        ·
          refine ⟨60925221468591408938395493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40616814312394272625596995 60925221468591408938395493)
          ·
            refine ⟨11423479025360889175949155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60925221468591408938395493 11423479025360889175949155)
            ·
              refine ⟨17135218538041333763923733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11423479025360889175949155 17135218538041333763923733)
              ·
                refine ⟨803213368970687520183925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17135218538041333763923733 803213368970687520183925)
                ·
                  refine ⟨75301253341001955017243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 803213368970687520183925 75301253341001955017243)
                  ·
                    rfl

theorem cell22_659919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 5].length) (baseStart_659919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659919 prefixEnd_659919 := by exact prefixLift 659919
  have htrace : WordTrace (prefixWord ++ tailWord_659919) baseStart_659919 baseEnd_659919 := by
    simpa [prefixWord, tailWord_659919, baseEnd_659919] using wordTrace_append hprefix tailTrace_659919
  have hstable : (prefixWord ++ tailWord_659919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659919).length < 2 ^ (prefixWord ++ tailWord_659919).sum := by decide
  have hdescent : baseEnd_659919 < baseStart_659919 := by decide
  rcases family_descends (prefixWord ++ tailWord_659919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659970 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_659970 : Nat := 118140960795 + 659970 * 2 ^ 59
def prefixEnd_659970 : Nat := 4983230072969 + 3 ^ 40 * 659970 * 2
def baseEnd_659970 : Nat := 75307072788419577342191

theorem tailTrace_659970 : CollatzResearch.WordTrace tailWord_659970 prefixEnd_659970 75307072788419577342191 := by
  unfold tailWord_659970
  simp only [CollatzResearch.WordTrace]
  refine ⟨6017770854762219686874341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16047388946032585831664909 6017770854762219686874341)
  ·
    refine ⟨1128332035267916191288939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6017770854762219686874341 1128332035267916191288939)
    ·
      refine ⟨1692498052901874286933409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1128332035267916191288939 1692498052901874286933409)
      ·
        refine ⟨1269373539676405715200057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1692498052901874286933409 1269373539676405715200057)
        ·
          refine ⟨952030154757304286400043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1269373539676405715200057 952030154757304286400043)
          ·
            refine ⟨1428045232135956429600065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952030154757304286400043 1428045232135956429600065)
            ·
              refine ⟨1071033924101967322200049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428045232135956429600065 1071033924101967322200049)
              ·
                refine ⟨803275443076475491650037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071033924101967322200049 803275443076475491650037)
                ·
                  refine ⟨75307072788419577342191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 803275443076475491650037 75307072788419577342191)
                  ·
                    rfl

theorem cell22_659970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_659970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659970 prefixEnd_659970 := by exact prefixLift 659970
  have htrace : WordTrace (prefixWord ++ tailWord_659970) baseStart_659970 baseEnd_659970 := by
    simpa [prefixWord, tailWord_659970, baseEnd_659970] using wordTrace_append hprefix tailTrace_659970
  have hstable : (prefixWord ++ tailWord_659970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659970).length < 2 ^ (prefixWord ++ tailWord_659970).sum := by decide
  have hdescent : baseEnd_659970 < baseStart_659970 := by decide
  rcases family_descends (prefixWord ++ tailWord_659970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659996 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_659996 : Nat := 118140960795 + 659996 * 2 ^ 59
def prefixEnd_659996 : Nat := 4983230072969 + 3 ^ 40 * 659996 * 2
def baseEnd_659996 : Nat := 225930118696603330876493

theorem tailTrace_659996 : CollatzResearch.WordTrace tailWord_659996 prefixEnd_659996 225930118696603330876493 := by
  unfold tailWord_659996
  simp only [CollatzResearch.WordTrace]
  refine ⟨12036015858477342593971921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16048021144636456791962561 12036015858477342593971921)
  ·
    refine ⟨9027011893858006945478941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12036015858477342593971921 9027011893858006945478941)
    ·
      refine ⟨3385129460196752604554603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9027011893858006945478941 3385129460196752604554603)
      ·
        refine ⟨5077694190295128906831905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3385129460196752604554603 5077694190295128906831905)
        ·
          refine ⟨3808270642721346680123929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5077694190295128906831905 3808270642721346680123929)
          ·
            refine ⟨2856202982041010010092947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3808270642721346680123929 2856202982041010010092947)
            ·
              refine ⟨4284304473061515015139421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856202982041010010092947 4284304473061515015139421)
              ·
                refine ⟨1606614177398068130677283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4284304473061515015139421 1606614177398068130677283)
                ·
                  refine ⟨2409921266097102196015925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606614177398068130677283 2409921266097102196015925)
                  ·
                    refine ⟨225930118696603330876493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2409921266097102196015925 225930118696603330876493)
                    ·
                      rfl

theorem cell22_659996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_659996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_659996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_659996 prefixEnd_659996 := by exact prefixLift 659996
  have htrace : WordTrace (prefixWord ++ tailWord_659996) baseStart_659996 baseEnd_659996 := by
    simpa [prefixWord, tailWord_659996, baseEnd_659996] using wordTrace_append hprefix tailTrace_659996
  have hstable : (prefixWord ++ tailWord_659996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659996).length < 2 ^ (prefixWord ++ tailWord_659996).sum := by decide
  have hdescent : baseEnd_659996 < baseStart_659996 := by decide
  rcases family_descends (prefixWord ++ tailWord_659996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660060 : List Nat := [2, 2, 4, 1, 3, 2, 2, 6]
def baseStart_660060 : Nat := 118140960795 + 660060 * 2 ^ 59
def prefixEnd_660060 : Nat := 4983230072969 + 3 ^ 40 * 660060 * 2
def baseEnd_660060 : Nat := 25105780800503166364033

theorem tailTrace_660060 : CollatzResearch.WordTrace tailWord_660060 prefixEnd_660060 25105780800503166364033 := by
  unfold tailWord_660060
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037182994361412059136817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16049577325815216078849089 12037182994361412059136817)
  ·
    refine ⟨9027887245771059044352613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12037182994361412059136817 9027887245771059044352613)
    ·
      refine ⟨1692728858582073570816115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9027887245771059044352613 1692728858582073570816115)
      ·
        refine ⟨2539093287873110356224173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692728858582073570816115 2539093287873110356224173)
        ·
          refine ⟨952159982952416383584065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2539093287873110356224173 952159982952416383584065)
          ·
            refine ⟨714119987214312287688049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952159982952416383584065 714119987214312287688049)
            ·
              refine ⟨535589990410734215766037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714119987214312287688049 535589990410734215766037)
              ·
                refine ⟨25105780800503166364033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 535589990410734215766037 25105780800503166364033)
                ·
                  rfl

theorem cell22_660060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 6].length) (baseStart_660060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660060 prefixEnd_660060 := by exact prefixLift 660060
  have htrace : WordTrace (prefixWord ++ tailWord_660060) baseStart_660060 baseEnd_660060 := by
    simpa [prefixWord, tailWord_660060, baseEnd_660060] using wordTrace_append hprefix tailTrace_660060
  have hstable : (prefixWord ++ tailWord_660060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660060).length < 2 ^ (prefixWord ++ tailWord_660060).sum := by decide
  have hdescent : baseEnd_660060 < baseStart_660060 := by decide
  rcases family_descends (prefixWord ++ tailWord_660060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660098 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_660098 : Nat := 118140960795 + 660098 * 2 ^ 59
def prefixEnd_660098 : Nat := 4983230072969 + 3 ^ 40 * 660098 * 2
def baseEnd_660098 : Nat := 225965035381109064826181

theorem tailTrace_660098 : CollatzResearch.WordTrace tailWord_660098 prefixEnd_660098 225965035381109064826181 := by
  unfold tailWord_660098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6018937990646289152039237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16050501308390104405437965 6018937990646289152039237)
  ·
    refine ⟨1128550873246179216007357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6018937990646289152039237 1128550873246179216007357)
    ·
      refine ⟨423206577467317206002759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1128550873246179216007357 423206577467317206002759)
      ·
        refine ⟨634809866200975809004139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423206577467317206002759 634809866200975809004139)
        ·
          refine ⟨952214799301463713506209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634809866200975809004139 952214799301463713506209)
          ·
            refine ⟨714161099476097785129657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952214799301463713506209 714161099476097785129657)
            ·
              refine ⟨535620824607073338847243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714161099476097785129657 535620824607073338847243)
              ·
                refine ⟨803431236910610008270865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535620824607073338847243 803431236910610008270865)
                ·
                  refine ⟨602573427682957506203149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 803431236910610008270865 602573427682957506203149)
                  ·
                    refine ⟨225965035381109064826181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 602573427682957506203149 225965035381109064826181)
                    ·
                      rfl

theorem cell22_660098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_660098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660098 prefixEnd_660098 := by exact prefixLift 660098
  have htrace : WordTrace (prefixWord ++ tailWord_660098) baseStart_660098 baseEnd_660098 := by
    simpa [prefixWord, tailWord_660098, baseEnd_660098] using wordTrace_append hprefix tailTrace_660098
  have hstable : (prefixWord ++ tailWord_660098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660098).length < 2 ^ (prefixWord ++ tailWord_660098).sum := by decide
  have hdescent : baseEnd_660098 < baseStart_660098 := by decide
  rcases family_descends (prefixWord ++ tailWord_660098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660133 : List Nat := [1, 3, 1, 2, 1, 2, 1, 7, 4]
def baseStart_660133 : Nat := 118140960795 + 660133 * 2 ^ 59
def prefixEnd_660133 : Nat := 4983230072969 + 3 ^ 40 * 660133 * 2
def baseEnd_660133 : Nat := 75325672198793546733691

theorem tailTrace_660133 : CollatzResearch.WordTrace tailWord_660133 prefixEnd_660133 75325672198793546733691 := by
  unfold tailWord_660133
  simp only [CollatzResearch.WordTrace]
  refine ⟨24077028517458357585681053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16051352344972238390454035 24077028517458357585681053)
  ·
    refine ⟨9028885694046884094630395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24077028517458357585681053 9028885694046884094630395)
    ·
      refine ⟨13543328541070326141945593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9028885694046884094630395 13543328541070326141945593)
      ·
        refine ⟨10157496405802744606459195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13543328541070326141945593 10157496405802744606459195)
        ·
          refine ⟨15236244608704116909688793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10157496405802744606459195 15236244608704116909688793)
          ·
            refine ⟨11427183456528087682266595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15236244608704116909688793 11427183456528087682266595)
            ·
              refine ⟨17140775184792131523399893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11427183456528087682266595 17140775184792131523399893)
              ·
                refine ⟨401736918393565582579685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17140775184792131523399893 401736918393565582579685)
                ·
                  refine ⟨75325672198793546733691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 401736918393565582579685 75325672198793546733691)
                  ·
                    rfl

theorem cell22_660133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_660133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660133 prefixEnd_660133 := by exact prefixLift 660133
  have htrace : WordTrace (prefixWord ++ tailWord_660133) baseStart_660133 baseEnd_660133 := by
    simpa [prefixWord, tailWord_660133, baseEnd_660133] using wordTrace_append hprefix tailTrace_660133
  have hstable : (prefixWord ++ tailWord_660133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660133).length < 2 ^ (prefixWord ++ tailWord_660133).sum := by decide
  have hdescent : baseEnd_660133 < baseStart_660133 := by decide
  rcases family_descends (prefixWord ++ tailWord_660133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660146 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_660146 : Nat := 118140960795 + 660146 * 2 ^ 59
def prefixEnd_660146 : Nat := 4983230072969 + 3 ^ 40 * 660146 * 2
def baseEnd_660146 : Nat := 225981466762052939626033

theorem tailTrace_660146 : CollatzResearch.WordTrace tailWord_660146 prefixEnd_660146 225981466762052939626033 := by
  unfold tailWord_660146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6019375666602815201476073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16051668444274173870602861 6019375666602815201476073)
  ·
    refine ⟨4514531749952111401107055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6019375666602815201476073 4514531749952111401107055)
    ·
      refine ⟨6771797624928167101660583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4514531749952111401107055 6771797624928167101660583)
      ·
        refine ⟨10157696437392250652490875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6771797624928167101660583 10157696437392250652490875)
        ·
          refine ⟨15236544656088375978736313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10157696437392250652490875 15236544656088375978736313)
          ·
            refine ⟨11427408492066281984052235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15236544656088375978736313 11427408492066281984052235)
            ·
              refine ⟨17141112738099422976078353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11427408492066281984052235 17141112738099422976078353)
              ·
                refine ⟨12855834553574567232058765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17141112738099422976078353 12855834553574567232058765)
                ·
                  refine ⟨4820937957590462712022037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12855834553574567232058765 4820937957590462712022037)
                  ·
                    refine ⟨225981466762052939626033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4820937957590462712022037 225981466762052939626033)
                    ·
                      rfl

theorem cell22_660146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_660146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660146 prefixEnd_660146 := by exact prefixLift 660146
  have htrace : WordTrace (prefixWord ++ tailWord_660146) baseStart_660146 baseEnd_660146 := by
    simpa [prefixWord, tailWord_660146, baseEnd_660146] using wordTrace_append hprefix tailTrace_660146
  have hstable : (prefixWord ++ tailWord_660146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660146).length < 2 ^ (prefixWord ++ tailWord_660146).sum := by decide
  have hdescent : baseEnd_660146 < baseStart_660146 := by decide
  rcases family_descends (prefixWord ++ tailWord_660146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660180 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_660180 : Nat := 118140960795 + 660180 * 2 ^ 59
def prefixEnd_660180 : Nat := 4983230072969 + 3 ^ 40 * 660180 * 2
def baseEnd_660180 : Nat := 225993105656888184275929

theorem tailTrace_660180 : CollatzResearch.WordTrace tailWord_660180 prefixEnd_660180 225993105656888184275929 := by
  unfold tailWord_660180
  simp only [CollatzResearch.WordTrace]
  refine ⟨12039371374144042306320997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16052495165525389741761329 12039371374144042306320997)
  ·
    refine ⟨2257382132652007932435187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12039371374144042306320997 2257382132652007932435187)
    ·
      refine ⟨3386073198978011898652781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2257382132652007932435187 3386073198978011898652781)
      ·
        refine ⟨1269777449616754461994793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3386073198978011898652781 1269777449616754461994793)
        ·
          refine ⟨952333087212565846496095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1269777449616754461994793 952333087212565846496095)
          ·
            refine ⟨1428499630818848769744143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952333087212565846496095 1428499630818848769744143)
            ·
              refine ⟨2142749446228273154616215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428499630818848769744143 2142749446228273154616215)
              ·
                refine ⟨3214124169342409731924323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142749446228273154616215 3214124169342409731924323)
                ·
                  refine ⟨4821186254013614597886485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214124169342409731924323 4821186254013614597886485)
                  ·
                    refine ⟨225993105656888184275929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4821186254013614597886485 225993105656888184275929)
                    ·
                      rfl

theorem cell22_660180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_660180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660180 prefixEnd_660180 := by exact prefixLift 660180
  have htrace : WordTrace (prefixWord ++ tailWord_660180) baseStart_660180 baseEnd_660180 := by
    simpa [prefixWord, tailWord_660180, baseEnd_660180] using wordTrace_append hprefix tailTrace_660180
  have hstable : (prefixWord ++ tailWord_660180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660180).length < 2 ^ (prefixWord ++ tailWord_660180).sum := by decide
  have hdescent : baseEnd_660180 < baseStart_660180 := by decide
  rcases family_descends (prefixWord ++ tailWord_660180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660210 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_660210 : Nat := 118140960795 + 660210 * 2 ^ 59
def prefixEnd_660210 : Nat := 4983230072969 + 3 ^ 40 * 660210 * 2
def baseEnd_660210 : Nat := 226003375269978106025837

theorem tailTrace_660210 : CollatzResearch.WordTrace tailWord_660210 prefixEnd_660210 226003375269978106025837 := by
  unfold tailWord_660210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6019959234544849934058521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16053224625452933157489389 6019959234544849934058521)
  ·
    refine ⟨4514969425908637450543891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6019959234544849934058521 4514969425908637450543891)
    ·
      refine ⟨6772454138862956175815837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4514969425908637450543891 6772454138862956175815837)
      ·
        refine ⟨2539670302073608565930939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6772454138862956175815837 2539670302073608565930939)
        ·
          refine ⟨3809505453110412848896409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539670302073608565930939 3809505453110412848896409)
          ·
            refine ⟨2857129089832809636672307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3809505453110412848896409 2857129089832809636672307)
            ·
              refine ⟨4285693634749214455008461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857129089832809636672307 4285693634749214455008461)
              ·
                refine ⟨1607135113030955420628173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4285693634749214455008461 1607135113030955420628173)
                ·
                  refine ⟨602675667386608282735565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1607135113030955420628173 602675667386608282735565)
                  ·
                    refine ⟨226003375269978106025837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 602675667386608282735565 226003375269978106025837)
                    ·
                      rfl

theorem cell22_660210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_660210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660210 prefixEnd_660210 := by exact prefixLift 660210
  have htrace : WordTrace (prefixWord ++ tailWord_660210) baseStart_660210 baseEnd_660210 := by
    simpa [prefixWord, tailWord_660210, baseEnd_660210] using wordTrace_append hprefix tailTrace_660210
  have hstable : (prefixWord ++ tailWord_660210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660210).length < 2 ^ (prefixWord ++ tailWord_660210).sum := by decide
  have hdescent : baseEnd_660210 < baseStart_660210 := by decide
  rcases family_descends (prefixWord ++ tailWord_660210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660287 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 1, 4]
def baseStart_660287 : Nat := 118140960795 + 660287 * 2 ^ 59
def prefixEnd_660287 : Nat := 4983230072969 + 3 ^ 40 * 660287 * 2
def baseEnd_660287 : Nat := 226029733943575571850601

theorem tailTrace_660287 : CollatzResearch.WordTrace tailWord_660287 prefixEnd_660287 226029733943575571850601 := by
  unfold tailWord_660287
  simp only [CollatzResearch.WordTrace]
  refine ⟨24082645358900441886787115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16055096905933627924524743 24082645358900441886787115)
  ·
    refine ⟨36123968038350662830180673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24082645358900441886787115 36123968038350662830180673)
    ·
      refine ⟨27092976028762997122635505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36123968038350662830180673 27092976028762997122635505)
      ·
        refine ⟨20319732021572247841976629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27092976028762997122635505 20319732021572247841976629)
        ·
          refine ⟨1904974877022398235185309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20319732021572247841976629 1904974877022398235185309)
          ·
            refine ⟨714365578883399338194491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1904974877022398235185309 714365578883399338194491)
            ·
              refine ⟨1071548368325099007291737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714365578883399338194491 1071548368325099007291737)
              ·
                refine ⟨803661276243824255468803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071548368325099007291737 803661276243824255468803)
                ·
                  refine ⟨1205491914365736383203205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803661276243824255468803 1205491914365736383203205)
                  ·
                    refine ⟨226029733943575571850601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1205491914365736383203205 226029733943575571850601)
                    ·
                      rfl

theorem cell22_660287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 4].length) (baseStart_660287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660287 prefixEnd_660287 := by exact prefixLift 660287
  have htrace : WordTrace (prefixWord ++ tailWord_660287) baseStart_660287 baseEnd_660287 := by
    simpa [prefixWord, tailWord_660287, baseEnd_660287] using wordTrace_append hprefix tailTrace_660287
  have hstable : (prefixWord ++ tailWord_660287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660287).length < 2 ^ (prefixWord ++ tailWord_660287).sum := by decide
  have hdescent : baseEnd_660287 < baseStart_660287 := by decide
  rcases family_descends (prefixWord ++ tailWord_660287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660300 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_660300 : Nat := 118140960795 + 660300 * 2 ^ 59
def prefixEnd_660300 : Nat := 4983230072969 + 3 ^ 40 * 660300 * 2
def baseEnd_660300 : Nat := 226034184109247871275561

theorem tailTrace_660300 : CollatzResearch.WordTrace tailWord_660300 prefixEnd_660300 226034184109247871275561 := by
  unfold tailWord_660300
  simp only [CollatzResearch.WordTrace]
  refine ⟨12041559753926672553505177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16055413005235563404673569 12041559753926672553505177)
  ·
    refine ⟨9031169815445004415128883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12041559753926672553505177 9031169815445004415128883)
    ·
      refine ⟨13546754723167506622693325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9031169815445004415128883 13546754723167506622693325)
      ·
        refine ⟨5080033021187814983509997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13546754723167506622693325 5080033021187814983509997)
        ·
          refine ⟨1905012382945430618816249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5080033021187814983509997 1905012382945430618816249)
          ·
            refine ⟨1428759287209072964112187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1905012382945430618816249 1428759287209072964112187)
            ·
              refine ⟨2143138930813609446168281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428759287209072964112187 2143138930813609446168281)
              ·
                refine ⟨1607354198110207084626211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2143138930813609446168281 1607354198110207084626211)
                ·
                  refine ⟨2411031297165310626939317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607354198110207084626211 2411031297165310626939317)
                  ·
                    refine ⟨226034184109247871275561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2411031297165310626939317 226034184109247871275561)
                    ·
                      rfl

theorem cell22_660300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_660300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660300 prefixEnd_660300 := by exact prefixLift 660300
  have htrace : WordTrace (prefixWord ++ tailWord_660300) baseStart_660300 baseEnd_660300 := by
    simpa [prefixWord, tailWord_660300, baseEnd_660300] using wordTrace_append hprefix tailTrace_660300
  have hstable : (prefixWord ++ tailWord_660300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660300).length < 2 ^ (prefixWord ++ tailWord_660300).sum := by decide
  have hdescent : baseEnd_660300 < baseStart_660300 := by decide
  rcases family_descends (prefixWord ++ tailWord_660300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660345 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 5, 3]
def baseStart_660345 : Nat := 118140960795 + 660345 * 2 ^ 59
def prefixEnd_660345 : Nat := 4983230072969 + 3 ^ 40 * 660345 * 2
def baseEnd_660345 : Nat := 226049588528882753900423

theorem tailTrace_660345 : CollatzResearch.WordTrace tailWord_660345 prefixEnd_660345 226049588528882753900423 := by
  unfold tailWord_660345
  simp only [CollatzResearch.WordTrace]
  refine ⟨24084760792690317792398489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16056507195126878528265659 24084760792690317792398489)
  ·
    refine ⟨18063570594517738344298867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24084760792690317792398489 18063570594517738344298867)
    ·
      refine ⟨27095355891776607516448301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18063570594517738344298867 27095355891776607516448301)
      ·
        refine ⟨10160758459416227818668113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27095355891776607516448301 10160758459416227818668113)
        ·
          refine ⟨7620568844562170864001085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10160758459416227818668113 7620568844562170864001085)
          ·
            refine ⟨2857713316710814074000407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7620568844562170864001085 2857713316710814074000407)
            ·
              refine ⟨4286569975066221111000611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857713316710814074000407 4286569975066221111000611)
              ·
                refine ⟨6429854962599331666500917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286569975066221111000611 6429854962599331666500917)
                ·
                  refine ⟨602798902743687343734461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6429854962599331666500917 602798902743687343734461)
                  ·
                    refine ⟨226049588528882753900423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 602798902743687343734461 226049588528882753900423)
                    ·
                      rfl

theorem cell22_660345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 3].length) (baseStart_660345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660345 prefixEnd_660345 := by exact prefixLift 660345
  have htrace : WordTrace (prefixWord ++ tailWord_660345) baseStart_660345 baseEnd_660345 := by
    simpa [prefixWord, tailWord_660345, baseEnd_660345] using wordTrace_append hprefix tailTrace_660345
  have hstable : (prefixWord ++ tailWord_660345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660345).length < 2 ^ (prefixWord ++ tailWord_660345).sum := by decide
  have hdescent : baseEnd_660345 < baseStart_660345 := by decide
  rcases family_descends (prefixWord ++ tailWord_660345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660403 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 8]
def baseStart_660403 : Nat := 118140960795 + 660403 * 2 ^ 59
def prefixEnd_660403 : Nat := 4983230072969 + 3 ^ 40 * 660403 * 2
def baseEnd_660403 : Nat := 75356481038063311983415

theorem tailTrace_660403 : CollatzResearch.WordTrace tailWord_660403 prefixEnd_660403 75356481038063311983415 := by
  unfold tailWord_660403
  simp only [CollatzResearch.WordTrace]
  refine ⟨24086876226480193698009863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16057917484320129132006575 24086876226480193698009863)
  ·
    refine ⟨36130314339720290547014795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24086876226480193698009863 36130314339720290547014795)
    ·
      refine ⟨54195471509580435820522193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36130314339720290547014795 54195471509580435820522193)
      ·
        refine ⟨40646603632185326865391645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54195471509580435820522193 40646603632185326865391645)
        ·
          refine ⟨15242476362069497574521867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40646603632185326865391645 15242476362069497574521867)
          ·
            refine ⟨22863714543104246361782801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15242476362069497574521867 22863714543104246361782801)
            ·
              refine ⟨17147785907328184771337101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22863714543104246361782801 17147785907328184771337101)
              ·
                refine ⟨6430419715248069289251413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17147785907328184771337101 6430419715248069289251413)
                ·
                  refine ⟨75356481038063311983415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6430419715248069289251413 75356481038063311983415)
                  ·
                    rfl

theorem cell22_660403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 8].length) (baseStart_660403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660403 prefixEnd_660403 := by exact prefixLift 660403
  have htrace : WordTrace (prefixWord ++ tailWord_660403) baseStart_660403 baseEnd_660403 := by
    simpa [prefixWord, tailWord_660403, baseEnd_660403] using wordTrace_append hprefix tailTrace_660403
  have hstable : (prefixWord ++ tailWord_660403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660403).length < 2 ^ (prefixWord ++ tailWord_660403).sum := by decide
  have hdescent : baseEnd_660403 < baseStart_660403 := by decide
  rcases family_descends (prefixWord ++ tailWord_660403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660413 : List Nat := [1, 4, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_660413 : Nat := 118140960795 + 660413 * 2 ^ 59
def prefixEnd_660413 : Nat := 4983230072969 + 3 ^ 40 * 660413 * 2
def baseEnd_660413 : Nat := 226072866318553243200215

theorem tailTrace_660413 : CollatzResearch.WordTrace tailWord_660413 prefixEnd_660413 226072866318553243200215 := by
  unfold tailWord_660413
  simp only [CollatzResearch.WordTrace]
  refine ⟨24087240956443965405873893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16058160637629310270582595 24087240956443965405873893)
  ·
    refine ⟨4516357679333243513601355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24087240956443965405873893 4516357679333243513601355)
    ·
      refine ⟨6774536518999865270402033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4516357679333243513601355 6774536518999865270402033)
      ·
        refine ⟨5080902389249898952801525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6774536518999865270402033 5080902389249898952801525)
        ·
          refine ⟨476334598992178026825143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5080902389249898952801525 476334598992178026825143)
          ·
            refine ⟨714501898488267040237715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476334598992178026825143 714501898488267040237715)
            ·
              refine ⟨1071752847732400560356573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714501898488267040237715 1071752847732400560356573)
              ·
                refine ⟨401907317899650210133715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1071752847732400560356573 401907317899650210133715)
                ·
                  refine ⟨602860976849475315200573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401907317899650210133715 602860976849475315200573)
                  ·
                    refine ⟨226072866318553243200215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 602860976849475315200573 226072866318553243200215)
                    ·
                      rfl

theorem cell22_660413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_660413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660413 prefixEnd_660413 := by exact prefixLift 660413
  have htrace : WordTrace (prefixWord ++ tailWord_660413) baseStart_660413 baseEnd_660413 := by
    simpa [prefixWord, tailWord_660413, baseEnd_660413] using wordTrace_append hprefix tailTrace_660413
  have hstable : (prefixWord ++ tailWord_660413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660413).length < 2 ^ (prefixWord ++ tailWord_660413).sum := by decide
  have hdescent : baseEnd_660413 < baseStart_660413 := by decide
  rcases family_descends (prefixWord ++ tailWord_660413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660465 : List Nat := [1, 2, 2, 2, 4, 1, 2, 8]
def baseStart_660465 : Nat := 118140960795 + 660465 * 2 ^ 59
def prefixEnd_660465 : Nat := 4983230072969 + 3 ^ 40 * 660465 * 2
def baseEnd_660465 : Nat := 25121185220138048988895

theorem tailTrace_660465 : CollatzResearch.WordTrace tailWord_660465 prefixEnd_660465 25121185220138048988895 := by
  unfold tailWord_660465
  simp only [CollatzResearch.WordTrace]
  refine ⟨24089137552255578286766849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16059425034837052191177899 24089137552255578286766849)
  ·
    refine ⟨18066853164191683715075137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24089137552255578286766849 18066853164191683715075137)
    ·
      refine ⟨13550139873143762786306353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18066853164191683715075137 13550139873143762786306353)
      ·
        refine ⟨10162604904857822089729765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13550139873143762786306353 10162604904857822089729765)
        ·
          refine ⟨1905488419660841641824331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10162604904857822089729765 1905488419660841641824331)
          ·
            refine ⟨2858232629491262462736497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905488419660841641824331 2858232629491262462736497)
            ·
              refine ⟨2143674472118446847052373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2858232629491262462736497 2143674472118446847052373)
              ·
                refine ⟨25121185220138048988895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2143674472118446847052373 25121185220138048988895)
                ·
                  rfl

theorem cell22_660465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 8].length) (baseStart_660465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660465 prefixEnd_660465 := by exact prefixLift 660465
  have htrace : WordTrace (prefixWord ++ tailWord_660465) baseStart_660465 baseEnd_660465 := by
    simpa [prefixWord, tailWord_660465, baseEnd_660465] using wordTrace_append hprefix tailTrace_660465
  have hstable : (prefixWord ++ tailWord_660465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660465).length < 2 ^ (prefixWord ++ tailWord_660465).sum := by decide
  have hdescent : baseEnd_660465 < baseStart_660465 := by decide
  rcases family_descends (prefixWord ++ tailWord_660465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660482 : List Nat := [3, 4, 1, 3, 11]
def baseStart_660482 : Nat := 118140960795 + 660482 * 2 ^ 59
def prefixEnd_660482 : Nat := 4983230072969 + 3 ^ 40 * 660482 * 2
def baseEnd_660482 : Nat := 930438215755802729321

theorem tailTrace_660482 : CollatzResearch.WordTrace tailWord_660482 prefixEnd_660482 930438215755802729321 := by
  unfold tailWord_660482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6022439398298497547533925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16059838395462660126757133 6022439398298497547533925)
  ·
    refine ⟨1129207387180968290162611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6022439398298497547533925 1129207387180968290162611)
    ·
      refine ⟨1693811080771452435243917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1129207387180968290162611 1693811080771452435243917)
      ·
        refine ⟨635179155289294663216469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1693811080771452435243917 635179155289294663216469)
        ·
          refine ⟨930438215755802729321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 635179155289294663216469 930438215755802729321)
          ·
            rfl

theorem cell22_660482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 11].length) (baseStart_660482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660482 prefixEnd_660482 := by exact prefixLift 660482
  have htrace : WordTrace (prefixWord ++ tailWord_660482) baseStart_660482 baseEnd_660482 := by
    simpa [prefixWord, tailWord_660482, baseEnd_660482] using wordTrace_append hprefix tailTrace_660482
  have hstable : (prefixWord ++ tailWord_660482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660482).length < 2 ^ (prefixWord ++ tailWord_660482).sum := by decide
  have hdescent : baseEnd_660482 < baseStart_660482 := by decide
  rcases family_descends (prefixWord ++ tailWord_660482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660514 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_660514 : Nat := 118140960795 + 660514 * 2 ^ 59
def prefixEnd_660514 : Nat := 4983230072969 + 3 ^ 40 * 660514 * 2
def baseEnd_660514 : Nat := 226107440682622646424905

theorem tailTrace_660514 : CollatzResearch.WordTrace tailWord_660514 prefixEnd_660514 226107440682622646424905 := by
  unfold tailWord_660514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6022731182269514913825149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16060616486052039770200397 6022731182269514913825149)
  ·
    refine ⟨2258524193351068092684431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6022731182269514913825149 2258524193351068092684431)
    ·
      refine ⟨3387786290026602139026647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258524193351068092684431 3387786290026602139026647)
      ·
        refine ⟨5081679435039903208539971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3387786290026602139026647 5081679435039903208539971)
        ·
          refine ⟨7622519152559854812809957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081679435039903208539971 7622519152559854812809957)
          ·
            refine ⟨1429222341104972777401867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7622519152559854812809957 1429222341104972777401867)
            ·
              refine ⟨2143833511657459166102801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429222341104972777401867 2143833511657459166102801)
              ·
                refine ⟨1607875133743094374577101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2143833511657459166102801 1607875133743094374577101)
                ·
                  refine ⟨602953175153660390466413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1607875133743094374577101 602953175153660390466413)
                  ·
                    refine ⟨226107440682622646424905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 602953175153660390466413 226107440682622646424905)
                    ·
                      rfl

theorem cell22_660514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_660514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660514 prefixEnd_660514 := by exact prefixLift 660514
  have htrace : WordTrace (prefixWord ++ tailWord_660514) baseStart_660514 baseEnd_660514 := by
    simpa [prefixWord, tailWord_660514, baseEnd_660514] using wordTrace_append hprefix tailTrace_660514
  have hstable : (prefixWord ++ tailWord_660514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660514).length < 2 ^ (prefixWord ++ tailWord_660514).sum := by decide
  have hdescent : baseEnd_660514 < baseStart_660514 := by decide
  rcases family_descends (prefixWord ++ tailWord_660514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660572 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 6]
def baseStart_660572 : Nat := 118140960795 + 660572 * 2 ^ 59
def prefixEnd_660572 : Nat := 4983230072969 + 3 ^ 40 * 660572 * 2
def baseEnd_660572 : Nat := 75375765089309942824909

theorem tailTrace_660572 : CollatzResearch.WordTrace tailWord_660572 prefixEnd_660572 75375765089309942824909 := by
  unfold tailWord_660572
  simp only [CollatzResearch.WordTrace]
  refine ⟨12046520081433967780455985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16062026775245290373941313 12046520081433967780455985)
  ·
    refine ⟨9034890061075475835341989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12046520081433967780455985 9034890061075475835341989)
    ·
      refine ⟨1694041886451651719126623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9034890061075475835341989 1694041886451651719126623)
      ·
        refine ⟨2541062829677477578689935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1694041886451651719126623 2541062829677477578689935)
        ·
          refine ⟨3811594244516216368034903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541062829677477578689935 3811594244516216368034903)
          ·
            refine ⟨5717391366774324552052355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811594244516216368034903 5717391366774324552052355)
            ·
              refine ⟨8576087050161486828078533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717391366774324552052355 8576087050161486828078533)
              ·
                refine ⟨1608016321905278780264725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8576087050161486828078533 1608016321905278780264725)
                ·
                  refine ⟨75375765089309942824909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1608016321905278780264725 75375765089309942824909)
                  ·
                    rfl

theorem cell22_660572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_660572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660572 prefixEnd_660572 := by exact prefixLift 660572
  have htrace : WordTrace (prefixWord ++ tailWord_660572) baseStart_660572 baseEnd_660572 := by
    simpa [prefixWord, tailWord_660572, baseEnd_660572] using wordTrace_append hprefix tailTrace_660572
  have hstable : (prefixWord ++ tailWord_660572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660572).length < 2 ^ (prefixWord ++ tailWord_660572).sum := by decide
  have hdescent : baseEnd_660572 < baseStart_660572 := by decide
  rcases family_descends (prefixWord ++ tailWord_660572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660600 : List Nat := [2, 1, 2, 1, 1, 1, 14]
def baseStart_660600 : Nat := 118140960795 + 660600 * 2 ^ 59
def prefixEnd_660600 : Nat := 4983230072969 + 3 ^ 40 * 660600 * 2
def baseEnd_660600 : Nat := 8375440008894336621283

theorem tailTrace_660600 : CollatzResearch.WordTrace tailWord_660600 prefixEnd_660600 8375440008894336621283 := by
  unfold tailWord_660600
  simp only [CollatzResearch.WordTrace]
  refine ⟨12047030703383248171465627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16062707604510997561954169 12047030703383248171465627)
  ·
    refine ⟨18070546055074872257198441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12047030703383248171465627 18070546055074872257198441)
    ·
      refine ⟨13552909541306154192898831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18070546055074872257198441 13552909541306154192898831)
      ·
        refine ⟨20329364311959231289348247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13552909541306154192898831 20329364311959231289348247)
        ·
          refine ⟨30494046467938846934022371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20329364311959231289348247 30494046467938846934022371)
          ·
            refine ⟨45741069701908270401033557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30494046467938846934022371 45741069701908270401033557)
            ·
              refine ⟨8375440008894336621283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 45741069701908270401033557 8375440008894336621283)
              ·
                rfl

theorem cell22_660600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 14].length) (baseStart_660600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660600 prefixEnd_660600 := by exact prefixLift 660600
  have htrace : WordTrace (prefixWord ++ tailWord_660600) baseStart_660600 baseEnd_660600 := by
    simpa [prefixWord, tailWord_660600, baseEnd_660600] using wordTrace_append hprefix tailTrace_660600
  have hstable : (prefixWord ++ tailWord_660600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660600).length < 2 ^ (prefixWord ++ tailWord_660600).sum := by decide
  have hdescent : baseEnd_660600 < baseStart_660600 := by decide
  rcases family_descends (prefixWord ++ tailWord_660600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660604 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 2, 3]
def baseStart_660604 : Nat := 118140960795 + 660604 * 2 ^ 59
def prefixEnd_660604 : Nat := 4983230072969 + 3 ^ 40 * 660604 * 2
def baseEnd_660604 : Nat := 226138249521892411674629

theorem tailTrace_660604 : CollatzResearch.WordTrace tailWord_660604 prefixEnd_660604 226138249521892411674629 := by
  unfold tailWord_660604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12047103649376002513038433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16062804865834670017384577 12047103649376002513038433)
  ·
    refine ⟨9035327737032001884778825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12047103649376002513038433 9035327737032001884778825)
    ·
      refine ⟨6776495802774001413584119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9035327737032001884778825 6776495802774001413584119)
      ·
        refine ⟨10164743704161002120376179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6776495802774001413584119 10164743704161002120376179)
        ·
          refine ⟨15247115556241503180564269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10164743704161002120376179 15247115556241503180564269)
          ·
            refine ⟨5717668333590563692711601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15247115556241503180564269 5717668333590563692711601)
            ·
              refine ⟨4288251250192922769533701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5717668333590563692711601 4288251250192922769533701)
              ·
                refine ⟨804047109411173019287569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4288251250192922769533701 804047109411173019287569)
                ·
                  refine ⟨603035332058379764465677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 804047109411173019287569 603035332058379764465677)
                  ·
                    refine ⟨226138249521892411674629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603035332058379764465677 226138249521892411674629)
                    ·
                      rfl

theorem cell22_660604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_660604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660604 prefixEnd_660604 := by exact prefixLift 660604
  have htrace : WordTrace (prefixWord ++ tailWord_660604) baseStart_660604 baseEnd_660604 := by
    simpa [prefixWord, tailWord_660604, baseEnd_660604] using wordTrace_append hprefix tailTrace_660604
  have hstable : (prefixWord ++ tailWord_660604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660604).length < 2 ^ (prefixWord ++ tailWord_660604).sum := by decide
  have hdescent : baseEnd_660604 < baseStart_660604 := by decide
  rcases family_descends (prefixWord ++ tailWord_660604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660617 : List Nat := [1, 2, 1, 1, 4, 4, 2, 7]
def baseStart_660617 : Nat := 118140960795 + 660617 * 2 ^ 59
def prefixEnd_660617 : Nat := 4983230072969 + 3 ^ 40 * 660617 * 2
def baseEnd_660617 : Nat := 25126966631951634566621

theorem tailTrace_660617 : CollatzResearch.WordTrace tailWord_660617 prefixEnd_660617 25126966631951634566621 := by
  unfold tailWord_660617
  simp only [CollatzResearch.WordTrace]
  refine ⟨24094681447704908246300105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16063120965136605497533403 24094681447704908246300105)
  ·
    refine ⟨18071011085778681184725079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24094681447704908246300105 18071011085778681184725079)
    ·
      refine ⟨27106516628668021777087619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18071011085778681184725079 27106516628668021777087619)
      ·
        refine ⟨40659774943002032665631429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27106516628668021777087619 40659774943002032665631429)
        ·
          refine ⟨7623707801812881124805893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40659774943002032665631429 7623707801812881124805893)
          ·
            refine ⟨1429445212839915210901105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7623707801812881124805893 1429445212839915210901105)
            ·
              refine ⟨1072083909629936408175829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1429445212839915210901105 1072083909629936408175829)
              ·
                refine ⟨25126966631951634566621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1072083909629936408175829 25126966631951634566621)
                ·
                  rfl

theorem cell22_660617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 7].length) (baseStart_660617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660617 prefixEnd_660617 := by exact prefixLift 660617
  have htrace : WordTrace (prefixWord ++ tailWord_660617) baseStart_660617 baseEnd_660617 := by
    simpa [prefixWord, tailWord_660617, baseEnd_660617] using wordTrace_append hprefix tailTrace_660617
  have hstable : (prefixWord ++ tailWord_660617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660617).length < 2 ^ (prefixWord ++ tailWord_660617).sum := by decide
  have hdescent : baseEnd_660617 < baseStart_660617 := by decide
  rcases family_descends (prefixWord ++ tailWord_660617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660739 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 1, 5]
def baseStart_660739 : Nat := 118140960795 + 660739 * 2 ^ 59
def prefixEnd_660739 : Nat := 4983230072969 + 3 ^ 40 * 660739 * 2
def baseEnd_660739 : Nat := 226184462780797059549215

theorem tailTrace_660739 : CollatzResearch.WordTrace tailWord_660739 prefixEnd_660739 226184462780797059549215 := by
  unfold tailWord_660739
  simp only [CollatzResearch.WordTrace]
  refine ⟨24099131153262923082241271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16066087435508615388160847 24099131153262923082241271)
  ·
    refine ⟨36148696729894384623361907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24099131153262923082241271 36148696729894384623361907)
    ·
      refine ⟨54223045094841576935042861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36148696729894384623361907 54223045094841576935042861)
      ·
        refine ⟨20333641910565591350641073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54223045094841576935042861 20333641910565591350641073)
        ·
          refine ⟨15250231432924193512980805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20333641910565591350641073 15250231432924193512980805)
          ·
            refine ⟨2859418393673286283683901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15250231432924193512980805 2859418393673286283683901)
            ·
              refine ⟨1072281897627482356381463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2859418393673286283683901 1072281897627482356381463)
              ·
                refine ⟨1608422846441223534572195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072281897627482356381463 1608422846441223534572195)
                ·
                  refine ⟨2412634269661835301858293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608422846441223534572195 2412634269661835301858293)
                  ·
                    refine ⟨226184462780797059549215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2412634269661835301858293 226184462780797059549215)
                    ·
                      rfl

theorem cell22_660739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 5].length) (baseStart_660739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660739 prefixEnd_660739 := by exact prefixLift 660739
  have htrace : WordTrace (prefixWord ++ tailWord_660739) baseStart_660739 baseEnd_660739 := by
    simpa [prefixWord, tailWord_660739, baseEnd_660739] using wordTrace_append hprefix tailTrace_660739
  have hstable : (prefixWord ++ tailWord_660739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660739).length < 2 ^ (prefixWord ++ tailWord_660739).sum := by decide
  have hdescent : baseEnd_660739 < baseStart_660739 := by decide
  rcases family_descends (prefixWord ++ tailWord_660739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660818 : List Nat := [3, 2, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_660818 : Nat := 118140960795 + 660818 * 2 ^ 59
def prefixEnd_660818 : Nat := 4983230072969 + 3 ^ 40 * 660818 * 2
def baseEnd_660818 : Nat := 226211506095267186823973

theorem tailTrace_660818 : CollatzResearch.WordTrace tailWord_660818 prefixEnd_660818 226211506095267186823973 := by
  unfold tailWord_660818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025503129994179893591777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16068008346651146382911405 6025503129994179893591777)
  ·
    refine ⟨4519127347495634920193833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6025503129994179893591777 4519127347495634920193833)
    ·
      refine ⟨3389345510621726190145375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4519127347495634920193833 3389345510621726190145375)
      ·
        refine ⟨5084018265932589285218063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3389345510621726190145375 5084018265932589285218063)
        ·
          refine ⟨7626027398898883927827095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5084018265932589285218063 7626027398898883927827095)
          ·
            refine ⟨11439041098348325891740643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7626027398898883927827095 11439041098348325891740643)
            ·
              refine ⟨17158561647522488837610965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11439041098348325891740643 17158561647522488837610965)
              ·
                refine ⟨402153788613808332131507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17158561647522488837610965 402153788613808332131507)
                ·
                  refine ⟨603230682920712498197261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402153788613808332131507 603230682920712498197261)
                  ·
                    refine ⟨226211506095267186823973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603230682920712498197261 226211506095267186823973)
                    ·
                      rfl

theorem cell22_660818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_660818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660818 prefixEnd_660818 := by exact prefixLift 660818
  have htrace : WordTrace (prefixWord ++ tailWord_660818) baseStart_660818 baseEnd_660818 := by
    simpa [prefixWord, tailWord_660818, baseEnd_660818] using wordTrace_append hprefix tailTrace_660818
  have hstable : (prefixWord ++ tailWord_660818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660818).length < 2 ^ (prefixWord ++ tailWord_660818).sum := by decide
  have hdescent : baseEnd_660818 < baseStart_660818 := by decide
  rcases family_descends (prefixWord ++ tailWord_660818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660835 : List Nat := [1, 1, 1, 5, 2, 2, 4, 2, 1, 3]
def baseStart_660835 : Nat := 118140960795 + 660835 * 2 ^ 59
def prefixEnd_660835 : Nat := 4983230072969 + 3 ^ 40 * 660835 * 2
def baseEnd_660835 : Nat := 226217325542684809148921

theorem tailTrace_660835 : CollatzResearch.WordTrace tailWord_660835 prefixEnd_660835 226217325542684809148921 := by
  unfold tailWord_660835
  simp only [CollatzResearch.WordTrace]
  refine ⟨24102632560915131477735959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16068421707276754318490639 24102632560915131477735959)
  ·
    refine ⟨36153948841372697216603939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24102632560915131477735959 36153948841372697216603939)
    ·
      refine ⟨54230923262059045824905909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36153948841372697216603939 54230923262059045824905909)
      ·
        refine ⟨5084149055818035546084929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54230923262059045824905909 5084149055818035546084929)
        ·
          refine ⟨3813111791863526659563697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5084149055818035546084929 3813111791863526659563697)
          ·
            refine ⟨2859833843897644994672773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813111791863526659563697 2859833843897644994672773)
            ·
              refine ⟨536218845730808436501145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2859833843897644994672773 536218845730808436501145)
              ·
                refine ⟨402164134298106327375859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536218845730808436501145 402164134298106327375859)
                ·
                  refine ⟨603246201447159491063789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402164134298106327375859 603246201447159491063789)
                  ·
                    refine ⟨226217325542684809148921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603246201447159491063789 226217325542684809148921)
                    ·
                      rfl

theorem cell22_660835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 1, 3].length) (baseStart_660835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660835 prefixEnd_660835 := by exact prefixLift 660835
  have htrace : WordTrace (prefixWord ++ tailWord_660835) baseStart_660835 baseEnd_660835 := by
    simpa [prefixWord, tailWord_660835, baseEnd_660835] using wordTrace_append hprefix tailTrace_660835
  have hstable : (prefixWord ++ tailWord_660835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660835).length < 2 ^ (prefixWord ++ tailWord_660835).sum := by decide
  have hdescent : baseEnd_660835 < baseStart_660835 := by decide
  rcases family_descends (prefixWord ++ tailWord_660835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660859 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 6]
def baseStart_660859 : Nat := 118140960795 + 660859 * 2 ^ 59
def prefixEnd_660859 : Nat := 4983230072969 + 3 ^ 40 * 660859 * 2
def baseEnd_660859 : Nat := 75408513744385582182949

theorem tailTrace_660859 : CollatzResearch.WordTrace tailWord_660859 prefixEnd_660859 75408513744385582182949 := by
  unfold tailWord_660859
  simp only [CollatzResearch.WordTrace]
  refine ⟨24103507912828183576609631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16069005275218789051073087 24103507912828183576609631)
  ·
    refine ⟨36155261869242275364914447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24103507912828183576609631 36155261869242275364914447)
    ·
      refine ⟨54232892803863413047371671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36155261869242275364914447 54232892803863413047371671)
      ·
        refine ⟨81349339205795119571057507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54232892803863413047371671 81349339205795119571057507)
        ·
          refine ⟨122024008808692679356586261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81349339205795119571057507 122024008808692679356586261)
          ·
            refine ⟨5719875412907469344839981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122024008808692679356586261 5719875412907469344839981)
            ·
              refine ⟨2144953279840301004314993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5719875412907469344839981 2144953279840301004314993)
              ·
                refine ⟨1608714959880225753236245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2144953279840301004314993 1608714959880225753236245)
                ·
                  refine ⟨75408513744385582182949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1608714959880225753236245 75408513744385582182949)
                  ·
                    rfl

theorem cell22_660859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 6].length) (baseStart_660859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660859 prefixEnd_660859 := by exact prefixLift 660859
  have htrace : WordTrace (prefixWord ++ tailWord_660859) baseStart_660859 baseEnd_660859 := by
    simpa [prefixWord, tailWord_660859, baseEnd_660859] using wordTrace_append hprefix tailTrace_660859
  have hstable : (prefixWord ++ tailWord_660859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660859).length < 2 ^ (prefixWord ++ tailWord_660859).sum := by decide
  have hdescent : baseEnd_660859 < baseStart_660859 := by decide
  rcases family_descends (prefixWord ++ tailWord_660859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660861 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_660861 : Nat := 118140960795 + 660861 * 2 ^ 59
def prefixEnd_660861 : Nat := 4983230072969 + 3 ^ 40 * 660861 * 2
def baseEnd_660861 : Nat := 226226225874029407998841

theorem tailTrace_660861 : CollatzResearch.WordTrace tailWord_660861 prefixEnd_660861 226226225874029407998841 := by
  unfold tailWord_660861
  simp only [CollatzResearch.WordTrace]
  refine ⟨24103580858820937918182437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16069053905880625278788291 24103580858820937918182437)
  ·
    refine ⟨4519421411028925859659207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24103580858820937918182437 4519421411028925859659207)
    ·
      refine ⟨6779132116543388789488811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4519421411028925859659207 6779132116543388789488811)
      ·
        refine ⟨10168698174815083184233217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6779132116543388789488811 10168698174815083184233217)
        ·
          refine ⟨7626523631111312388174913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10168698174815083184233217 7626523631111312388174913)
          ·
            refine ⟨5719892723333484291131185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7626523631111312388174913 5719892723333484291131185)
            ·
              refine ⟨4289919542500113218348389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5719892723333484291131185 4289919542500113218348389)
              ·
                refine ⟨804359914218771228440323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4289919542500113218348389 804359914218771228440323)
                ·
                  refine ⟨1206539871328156842660485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804359914218771228440323 1206539871328156842660485)
                  ·
                    refine ⟨226226225874029407998841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1206539871328156842660485 226226225874029407998841)
                    ·
                      rfl

theorem cell22_660861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_660861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660861 prefixEnd_660861 := by exact prefixLift 660861
  have htrace : WordTrace (prefixWord ++ tailWord_660861) baseStart_660861 baseEnd_660861 := by
    simpa [prefixWord, tailWord_660861, baseEnd_660861] using wordTrace_append hprefix tailTrace_660861
  have hstable : (prefixWord ++ tailWord_660861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660861).length < 2 ^ (prefixWord ++ tailWord_660861).sum := by decide
  have hdescent : baseEnd_660861 < baseStart_660861 := by decide
  rcases family_descends (prefixWord ++ tailWord_660861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660882 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_660882 : Nat := 118140960795 + 660882 * 2 ^ 59
def prefixEnd_660882 : Nat := 4983230072969 + 3 ^ 40 * 660882 * 2
def baseEnd_660882 : Nat := 75411138201064117741259

theorem tailTrace_660882 : CollatzResearch.WordTrace tailWord_660882 prefixEnd_660882 75411138201064117741259 := by
  unfold tailWord_660882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6026086697936214626174225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16069564527829905669797933 6026086697936214626174225)
  ·
    refine ⟨4519565023452160969630669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6026086697936214626174225 4519565023452160969630669)
    ·
      refine ⟨1694836883794560363611501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4519565023452160969630669 1694836883794560363611501)
      ·
        refine ⟨635563831422960136354313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1694836883794560363611501 635563831422960136354313)
        ·
          refine ⟨476672873567220102265735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 635563831422960136354313 476672873567220102265735)
          ·
            refine ⟨715009310350830153398603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476672873567220102265735 715009310350830153398603)
            ·
              refine ⟨1072513965526245230097905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715009310350830153398603 1072513965526245230097905)
              ·
                refine ⟨804385474144683922573429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072513965526245230097905 804385474144683922573429)
                ·
                  refine ⟨75411138201064117741259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 804385474144683922573429 75411138201064117741259)
                  ·
                    rfl

theorem cell22_660882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_660882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660882 prefixEnd_660882 := by exact prefixLift 660882
  have htrace : WordTrace (prefixWord ++ tailWord_660882) baseStart_660882 baseEnd_660882 := by
    simpa [prefixWord, tailWord_660882, baseEnd_660882] using wordTrace_append hprefix tailTrace_660882
  have hstable : (prefixWord ++ tailWord_660882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660882).length < 2 ^ (prefixWord ++ tailWord_660882).sum := by decide
  have hdescent : baseEnd_660882 < baseStart_660882 := by decide
  rcases family_descends (prefixWord ++ tailWord_660882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660893 : List Nat := [1, 4, 2, 1, 3, 1, 2, 4, 4]
def baseStart_660893 : Nat := 118140960795 + 660893 * 2 ^ 59
def prefixEnd_660893 : Nat := 4983230072969 + 3 ^ 40 * 660893 * 2
def baseEnd_660893 : Nat := 75412393375997330399581

theorem tailTrace_660893 : CollatzResearch.WordTrace tailWord_660893 prefixEnd_660893 75412393375997330399581 := by
  unfold tailWord_660893
  simp only [CollatzResearch.WordTrace]
  refine ⟨24104747994705007383347333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16069831996470004922231555 24104747994705007383347333)
  ·
    refine ⟨4519640249007188884377625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24104747994705007383347333 4519640249007188884377625)
    ·
      refine ⟨3389730186755391663283219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4519640249007188884377625 3389730186755391663283219)
      ·
        refine ⟨5084595280133087494924829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3389730186755391663283219 5084595280133087494924829)
        ·
          refine ⟨1906723230049907810596811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5084595280133087494924829 1906723230049907810596811)
          ·
            refine ⟨2860084845074861715895217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906723230049907810596811 2860084845074861715895217)
            ·
              refine ⟨2145063633806146286921413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860084845074861715895217 2145063633806146286921413)
              ·
                refine ⟨402199431338652428797765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2145063633806146286921413 402199431338652428797765)
                ·
                  refine ⟨75412393375997330399581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 402199431338652428797765 75412393375997330399581)
                  ·
                    rfl

theorem cell22_660893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_660893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660893 prefixEnd_660893 := by exact prefixLift 660893
  have htrace : WordTrace (prefixWord ++ tailWord_660893) baseStart_660893 baseEnd_660893 := by
    simpa [prefixWord, tailWord_660893, baseEnd_660893] using wordTrace_append hprefix tailTrace_660893
  have hstable : (prefixWord ++ tailWord_660893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660893).length < 2 ^ (prefixWord ++ tailWord_660893).sum := by decide
  have hdescent : baseEnd_660893 < baseStart_660893 := by decide
  rcases family_descends (prefixWord ++ tailWord_660893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660919 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 2, 7]
def baseStart_660919 : Nat := 118140960795 + 660919 * 2 ^ 59
def prefixEnd_660919 : Nat := 4983230072969 + 3 ^ 40 * 660919 * 2
def baseEnd_660919 : Nat := 226246080459336590048663

theorem tailTrace_660919 : CollatzResearch.WordTrace tailWord_660919 prefixEnd_660919 226246080459336590048663 := by
  unfold tailWord_660919
  simp only [CollatzResearch.WordTrace]
  refine ⟨24105696292610813823793811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16070464195073875882529207 24105696292610813823793811)
  ·
    refine ⟨36158544438916220735690717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24105696292610813823793811 36158544438916220735690717)
    ·
      refine ⟨13559454164593582775884019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36158544438916220735690717 13559454164593582775884019)
      ·
        refine ⟨20339181246890374163826029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13559454164593582775884019 20339181246890374163826029)
        ·
          refine ⟨7627192967583890311434761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20339181246890374163826029 7627192967583890311434761)
          ·
            refine ⟨5720394725687917733576071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7627192967583890311434761 5720394725687917733576071)
            ·
              refine ⟨8580592088531876600364107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5720394725687917733576071 8580592088531876600364107)
              ·
                refine ⟨12870888132797814900546161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8580592088531876600364107 12870888132797814900546161)
                ·
                  refine ⟨9653166099598361175409621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12870888132797814900546161 9653166099598361175409621)
                  ·
                    refine ⟨226246080459336590048663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9653166099598361175409621 226246080459336590048663)
                    ·
                      rfl

theorem cell22_660919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_660919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660919 prefixEnd_660919 := by exact prefixLift 660919
  have htrace : WordTrace (prefixWord ++ tailWord_660919) baseStart_660919 baseEnd_660919 := by
    simpa [prefixWord, tailWord_660919, baseEnd_660919] using wordTrace_append hprefix tailTrace_660919
  have hstable : (prefixWord ++ tailWord_660919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660919).length < 2 ^ (prefixWord ++ tailWord_660919).sum := by decide
  have hdescent : baseEnd_660919 < baseStart_660919 := by decide
  rcases family_descends (prefixWord ++ tailWord_660919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660921 : List Nat := [1, 2, 1, 4, 4, 1, 1, 8]
def baseStart_660921 : Nat := 118140960795 + 660921 * 2 ^ 59
def prefixEnd_660921 : Nat := 4983230072969 + 3 ^ 40 * 660921 * 2
def baseEnd_660921 : Nat := 25138529455578805722073

theorem tailTrace_660921 : CollatzResearch.WordTrace tailWord_660921 prefixEnd_660921 25138529455578805722073 := by
  unfold tailWord_660921
  simp only [CollatzResearch.WordTrace]
  refine ⟨24105769238603568165366617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16070512825735712110244411 24105769238603568165366617)
  ·
    refine ⟨18079326928952676124024963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24105769238603568165366617 18079326928952676124024963)
    ·
      refine ⟨27118990393429014186037445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18079326928952676124024963 27118990393429014186037445)
      ·
        refine ⟨5084810698767940159882021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27118990393429014186037445 5084810698767940159882021)
        ·
          refine ⟨953402006018988779977879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5084810698767940159882021 953402006018988779977879)
          ·
            refine ⟨1430103009028483169966819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953402006018988779977879 1430103009028483169966819)
            ·
              refine ⟨2145154513542724754950229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430103009028483169966819 2145154513542724754950229)
              ·
                refine ⟨25138529455578805722073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2145154513542724754950229 25138529455578805722073)
                ·
                  rfl

theorem cell22_660921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 8].length) (baseStart_660921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660921 prefixEnd_660921 := by exact prefixLift 660921
  have htrace : WordTrace (prefixWord ++ tailWord_660921) baseStart_660921 baseEnd_660921 := by
    simpa [prefixWord, tailWord_660921, baseEnd_660921] using wordTrace_append hprefix tailTrace_660921
  have hstable : (prefixWord ++ tailWord_660921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660921).length < 2 ^ (prefixWord ++ tailWord_660921).sum := by decide
  have hdescent : baseEnd_660921 < baseStart_660921 := by decide
  rcases family_descends (prefixWord ++ tailWord_660921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660953 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 3, 3]
def baseStart_660953 : Nat := 118140960795 + 660953 * 2 ^ 59
def prefixEnd_660953 : Nat := 4983230072969 + 3 ^ 40 * 660953 * 2
def baseEnd_660953 : Nat := 226257719354171834698559

theorem tailTrace_660953 : CollatzResearch.WordTrace tailWord_660953 prefixEnd_660953 226257719354171834698559 := by
  unfold tailWord_660953
  simp only [CollatzResearch.WordTrace]
  refine ⟨24106936374487637630531513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16071290916325091753687675 24106936374487637630531513)
  ·
    refine ⟨18080202280865728222898635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24106936374487637630531513 18080202280865728222898635)
    ·
      refine ⟨27120303421298592334347953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18080202280865728222898635 27120303421298592334347953)
      ·
        refine ⟨20340227565973944250760965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27120303421298592334347953 20340227565973944250760965)
        ·
          refine ⟨3813792668620114547017681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20340227565973944250760965 3813792668620114547017681)
          ·
            refine ⟨2860344501465085910263261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813792668620114547017681 2860344501465085910263261)
            ·
              refine ⟨1072629188049407216348723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2860344501465085910263261 1072629188049407216348723)
              ·
                refine ⟨1608943782074110824523085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072629188049407216348723 1608943782074110824523085)
                ·
                  refine ⟨603353918277791559196157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1608943782074110824523085 603353918277791559196157)
                  ·
                    refine ⟨226257719354171834698559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603353918277791559196157 226257719354171834698559)
                    ·
                      rfl

theorem cell22_660953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 3].length) (baseStart_660953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_660953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_660953 prefixEnd_660953 := by exact prefixLift 660953
  have htrace : WordTrace (prefixWord ++ tailWord_660953) baseStart_660953 baseEnd_660953 := by
    simpa [prefixWord, tailWord_660953, baseEnd_660953] using wordTrace_append hprefix tailTrace_660953
  have hstable : (prefixWord ++ tailWord_660953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660953).length < 2 ^ (prefixWord ++ tailWord_660953).sum := by decide
  have hdescent : baseEnd_660953 < baseStart_660953 := by decide
  rcases family_descends (prefixWord ++ tailWord_660953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661004 : List Nat := [2, 2, 1, 2, 5, 2, 2, 2, 1, 3]
def baseStart_661004 : Nat := 118140960795 + 661004 * 2 ^ 59
def prefixEnd_661004 : Nat := 4983230072969 + 3 ^ 40 * 661004 * 2
def baseEnd_661004 : Nat := 226275177696424701673403

theorem tailTrace_661004 : CollatzResearch.WordTrace tailWord_661004 prefixEnd_661004 226275177696424701673403 := by
  unfold tailWord_661004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054398248651436670319033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16072530998201915560425377 12054398248651436670319033)
  ·
    refine ⟨9040798686488577502739275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12054398248651436670319033 9040798686488577502739275)
    ·
      refine ⟨13561198029732866254108913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9040798686488577502739275 13561198029732866254108913)
      ·
        refine ⟨10170898522299649690581685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13561198029732866254108913 10170898522299649690581685)
        ·
          refine ⟨953521736465592158492033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10170898522299649690581685 953521736465592158492033)
          ·
            refine ⟨715141302349194118869025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 953521736465592158492033 715141302349194118869025)
            ·
              refine ⟨536355976761895589151769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715141302349194118869025 536355976761895589151769)
              ·
                refine ⟨402266982571421691863827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536355976761895589151769 402266982571421691863827)
                ·
                  refine ⟨603400473857132537795741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402266982571421691863827 603400473857132537795741)
                  ·
                    refine ⟨226275177696424701673403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603400473857132537795741 226275177696424701673403)
                    ·
                      rfl

theorem cell22_661004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_661004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661004 prefixEnd_661004 := by exact prefixLift 661004
  have htrace : WordTrace (prefixWord ++ tailWord_661004) baseStart_661004 baseEnd_661004 := by
    simpa [prefixWord, tailWord_661004, baseEnd_661004] using wordTrace_append hprefix tailTrace_661004
  have hstable : (prefixWord ++ tailWord_661004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661004).length < 2 ^ (prefixWord ++ tailWord_661004).sum := by decide
  have hdescent : baseEnd_661004 < baseStart_661004 := by decide
  rcases family_descends (prefixWord ++ tailWord_661004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661045 : List Nat := [1, 3, 3, 1, 1, 4, 2, 3, 4]
def baseStart_661045 : Nat := 118140960795 + 661045 * 2 ^ 59
def prefixEnd_661045 : Nat := 4983230072969 + 3 ^ 40 * 661045 * 2
def baseEnd_661045 : Nat := 75429737611438087132759

theorem tailTrace_661045 : CollatzResearch.WordTrace tailWord_661045 prefixEnd_661045 75429737611438087132759 := by
  unfold tailWord_661045
  simp only [CollatzResearch.WordTrace]
  refine ⟨24110291890154337342880589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16073527926769558228587059 24110291890154337342880589)
  ·
    refine ⟨9041359458807876503580221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24110291890154337342880589 9041359458807876503580221)
    ·
      refine ⟨3390509797052953688842583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9041359458807876503580221 3390509797052953688842583)
      ·
        refine ⟨5085764695579430533263875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3390509797052953688842583 5085764695579430533263875)
        ·
          refine ⟨7628647043369145799895813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5085764695579430533263875 7628647043369145799895813)
          ·
            refine ⟨1430371320631714837480465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7628647043369145799895813 1430371320631714837480465)
            ·
              refine ⟨1072778490473786128110349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1430371320631714837480465 1072778490473786128110349)
              ·
                refine ⟨402291933927669798041381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1072778490473786128110349 402291933927669798041381)
                ·
                  refine ⟨75429737611438087132759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 402291933927669798041381 75429737611438087132759)
                  ·
                    rfl

theorem cell22_661045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_661045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661045 prefixEnd_661045 := by exact prefixLift 661045
  have htrace : WordTrace (prefixWord ++ tailWord_661045) baseStart_661045 baseEnd_661045 := by
    simpa [prefixWord, tailWord_661045, baseEnd_661045] using wordTrace_append hprefix tailTrace_661045
  have hstable : (prefixWord ++ tailWord_661045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661045).length < 2 ^ (prefixWord ++ tailWord_661045).sum := by decide
  have hdescent : baseEnd_661045 < baseStart_661045 := by decide
  rcases family_descends (prefixWord ++ tailWord_661045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661062 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_661062 : Nat := 118140960795 + 661062 * 2 ^ 59
def prefixEnd_661062 : Nat := 4983230072969 + 3 ^ 40 * 661062 * 2
def baseEnd_661062 : Nat := 75431677427243961241075

theorem tailTrace_661062 : CollatzResearch.WordTrace tailWord_661062 prefixEnd_661062 75431677427243961241075 := by
  unfold tailWord_661062
  simp only [CollatzResearch.WordTrace]
  refine ⟨753465997846648413945295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16073941287395166164166293 753465997846648413945295)
  ·
    refine ⟨1130198996769972620917943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 753465997846648413945295 1130198996769972620917943)
    ·
      refine ⟨1695298495154958931376915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130198996769972620917943 1695298495154958931376915)
      ·
        refine ⟨2542947742732438397065373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695298495154958931376915 2542947742732438397065373)
        ·
          refine ⟨953605403524664398899515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2542947742732438397065373 953605403524664398899515)
          ·
            refine ⟨1430408105286996598349273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953605403524664398899515 1430408105286996598349273)
            ·
              refine ⟨1072806078965247448761955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1430408105286996598349273 1072806078965247448761955)
              ·
                refine ⟨1609209118447871173142933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072806078965247448761955 1609209118447871173142933)
                ·
                  refine ⟨75431677427243961241075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1609209118447871173142933 75431677427243961241075)
                  ·
                    rfl

theorem cell22_661062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_661062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661062 prefixEnd_661062 := by exact prefixLift 661062
  have htrace : WordTrace (prefixWord ++ tailWord_661062) baseStart_661062 baseEnd_661062 := by
    simpa [prefixWord, tailWord_661062, baseEnd_661062] using wordTrace_append hprefix tailTrace_661062
  have hstable : (prefixWord ++ tailWord_661062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661062).length < 2 ^ (prefixWord ++ tailWord_661062).sum := by decide
  have hdescent : baseEnd_661062 < baseStart_661062 := by decide
  rcases family_descends (prefixWord ++ tailWord_661062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661161 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_661161 : Nat := 118140960795 + 661161 * 2 ^ 59
def prefixEnd_661161 : Nat := 4983230072969 + 3 ^ 40 * 661161 * 2
def baseEnd_661161 : Nat := 226328922004928625497921

theorem tailTrace_661161 : CollatzResearch.WordTrace tailWord_661161 prefixEnd_661161 226328922004928625497921 := by
  unfold tailWord_661161
  simp only [CollatzResearch.WordTrace]
  refine ⟨24114522757734089154103337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16076348505156059436068891 24114522757734089154103337)
  ·
    refine ⟨18085892068300566865577503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24114522757734089154103337 18085892068300566865577503)
    ·
      refine ⟨27128838102450850298366255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18085892068300566865577503 27128838102450850298366255)
      ·
        refine ⟨40693257153676275447549383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27128838102450850298366255 40693257153676275447549383)
        ·
          refine ⟨61039885730514413171324075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40693257153676275447549383 61039885730514413171324075)
          ·
            refine ⟨91559828595771619756986113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61039885730514413171324075 91559828595771619756986113)
            ·
              refine ⟨68669871446828714817739585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91559828595771619756986113 68669871446828714817739585)
              ·
                refine ⟨51502403585121536113304689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68669871446828714817739585 51502403585121536113304689)
                ·
                  refine ⟨38626802688841152084978517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51502403585121536113304689 38626802688841152084978517)
                  ·
                    refine ⟨226328922004928625497921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 38626802688841152084978517 226328922004928625497921)
                    ·
                      rfl

theorem cell22_661161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_661161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661161 prefixEnd_661161 := by exact prefixLift 661161
  have htrace : WordTrace (prefixWord ++ tailWord_661161) baseStart_661161 baseEnd_661161 := by
    simpa [prefixWord, tailWord_661161, baseEnd_661161] using wordTrace_append hprefix tailTrace_661161
  have hstable : (prefixWord ++ tailWord_661161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661161).length < 2 ^ (prefixWord ++ tailWord_661161).sum := by decide
  have hdescent : baseEnd_661161 < baseStart_661161 := by decide
  rcases family_descends (prefixWord ++ tailWord_661161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661173 : List Nat := [1, 3, 3, 3, 3, 1, 2, 2, 1, 3]
def baseStart_661173 : Nat := 118140960795 + 661173 * 2 ^ 59
def prefixEnd_661173 : Nat := 4983230072969 + 3 ^ 40 * 661173 * 2
def baseEnd_661173 : Nat := 226333029850164594197885

theorem tailTrace_661173 : CollatzResearch.WordTrace tailWord_661173 prefixEnd_661173 226333029850164594197885 := by
  unfold tailWord_661173
  simp only [CollatzResearch.WordTrace]
  refine ⟨24114960433690615203540173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16076640289127076802360115 24114960433690615203540173)
  ·
    refine ⟨9043110162633980701327565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24114960433690615203540173 9043110162633980701327565)
    ·
      refine ⟨3391166310987742762997837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9043110162633980701327565 3391166310987742762997837)
      ·
        refine ⟨1271687366620403536124189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3391166310987742762997837 1271687366620403536124189)
        ·
          refine ⟨476882762482651326046571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1271687366620403536124189 476882762482651326046571)
          ·
            refine ⟨715324143723976989069857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476882762482651326046571 715324143723976989069857)
            ·
              refine ⟨536493107792982741802393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715324143723976989069857 536493107792982741802393)
              ·
                refine ⟨402369830844737056351795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536493107792982741802393 402369830844737056351795)
                ·
                  refine ⟨603554746267105584527693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402369830844737056351795 603554746267105584527693)
                  ·
                    refine ⟨226333029850164594197885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603554746267105584527693 226333029850164594197885)
                    ·
                      rfl

theorem cell22_661173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_661173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661173 prefixEnd_661173 := by exact prefixLift 661173
  have htrace : WordTrace (prefixWord ++ tailWord_661173) baseStart_661173 baseEnd_661173 := by
    simpa [prefixWord, tailWord_661173, baseEnd_661173] using wordTrace_append hprefix tailTrace_661173
  have hstable : (prefixWord ++ tailWord_661173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661173).length < 2 ^ (prefixWord ++ tailWord_661173).sum := by decide
  have hdescent : baseEnd_661173 < baseStart_661173 := by decide
  rcases family_descends (prefixWord ++ tailWord_661173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661197 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 6]
def baseStart_661197 : Nat := 118140960795 + 661197 * 2 ^ 59
def prefixEnd_661197 : Nat := 4983230072969 + 3 ^ 40 * 661197 * 2
def baseEnd_661197 : Nat := 75447081846878843865937

theorem tailTrace_661197 : CollatzResearch.WordTrace tailWord_661197 prefixEnd_661197 75447081846878843865937 := by
  unfold tailWord_661197
  simp only [CollatzResearch.WordTrace]
  refine ⟨24115835785603667302413845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16077223857069111534942563 24115835785603667302413845)
  ·
    refine ⟨1130429802450171904800649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24115835785603667302413845 1130429802450171904800649)
    ·
      refine ⟨847822351837628928600487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1130429802450171904800649 847822351837628928600487)
      ·
        refine ⟨1271733527756443392900731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847822351837628928600487 1271733527756443392900731)
        ·
          refine ⟨1907600291634665089351097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271733527756443392900731 1907600291634665089351097)
          ·
            refine ⟨1430700218725998817013323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1907600291634665089351097 1430700218725998817013323)
            ·
              refine ⟨2146050328088998225519985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430700218725998817013323 2146050328088998225519985)
              ·
                refine ⟨1609537746066748669139989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146050328088998225519985 1609537746066748669139989)
                ·
                  refine ⟨75447081846878843865937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1609537746066748669139989 75447081846878843865937)
                  ·
                    rfl

theorem cell22_661197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_661197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661197 prefixEnd_661197 := by exact prefixLift 661197
  have htrace : WordTrace (prefixWord ++ tailWord_661197) baseStart_661197 baseEnd_661197 := by
    simpa [prefixWord, tailWord_661197, baseEnd_661197] using wordTrace_append hprefix tailTrace_661197
  have hstable : (prefixWord ++ tailWord_661197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661197).length < 2 ^ (prefixWord ++ tailWord_661197).sum := by decide
  have hdescent : baseEnd_661197 < baseStart_661197 := by decide
  rcases family_descends (prefixWord ++ tailWord_661197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661210 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_661210 : Nat := 118140960795 + 661210 * 2 ^ 59
def prefixEnd_661210 : Nat := 4983230072969 + 3 ^ 40 * 661210 * 2
def baseEnd_661210 : Nat := 226345695706308831022771

theorem tailTrace_661210 : CollatzResearch.WordTrace tailWord_661210 prefixEnd_661210 226345695706308831022771 := by
  unfold tailWord_661210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6029077483639142630659271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16077539956371047015091389 6029077483639142630659271)
  ·
    refine ⟨9043616225458713945988907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6029077483639142630659271 9043616225458713945988907)
    ·
      refine ⟨13565424338188070918983361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9043616225458713945988907 13565424338188070918983361)
      ·
        refine ⟨10174068253641053189237521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13565424338188070918983361 10174068253641053189237521)
        ·
          refine ⟨7630551190230789891928141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10174068253641053189237521 7630551190230789891928141)
          ·
            refine ⟨2861456696336546209473053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7630551190230789891928141 2861456696336546209473053)
            ·
              refine ⟨1073046261126204828552395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2861456696336546209473053 1073046261126204828552395)
              ·
                refine ⟨1609569391689307242828593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073046261126204828552395 1609569391689307242828593)
                ·
                  refine ⟨1207177043766980432121445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1609569391689307242828593 1207177043766980432121445)
                  ·
                    refine ⟨226345695706308831022771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1207177043766980432121445 226345695706308831022771)
                    ·
                      rfl

theorem cell22_661210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_661210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661210 prefixEnd_661210 := by exact prefixLift 661210
  have htrace : WordTrace (prefixWord ++ tailWord_661210) baseStart_661210 baseEnd_661210 := by
    simpa [prefixWord, tailWord_661210, baseEnd_661210] using wordTrace_append hprefix tailTrace_661210
  have hstable : (prefixWord ++ tailWord_661210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661210).length < 2 ^ (prefixWord ++ tailWord_661210).sum := by decide
  have hdescent : baseEnd_661210 < baseStart_661210 := by decide
  rcases family_descends (prefixWord ++ tailWord_661210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661229 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_661229 : Nat := 118140960795 + 661229 * 2 ^ 59
def prefixEnd_661229 : Nat := 4983230072969 + 3 ^ 40 * 661229 * 2
def baseEnd_661229 : Nat := 226352199794599114797713

theorem tailTrace_661229 : CollatzResearch.WordTrace tailWord_661229 prefixEnd_661229 226352199794599114797713 := by
  unfold tailWord_661229
  simp only [CollatzResearch.WordTrace]
  refine ⟨24117002921487736767578741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16078001947658491178385827 24117002921487736767578741)
  ·
    refine ⟨2260969023889475321960507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24117002921487736767578741 2260969023889475321960507)
    ·
      refine ⟨3391453535834212982940761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2260969023889475321960507 3391453535834212982940761)
      ·
        refine ⟨2543590151875659737205571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3391453535834212982940761 2543590151875659737205571)
        ·
          refine ⟨3815385227813489605808357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2543590151875659737205571 3815385227813489605808357)
          ·
            refine ⟨715384730215029301089067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3815385227813489605808357 715384730215029301089067)
            ·
              refine ⟨1073077095322543951633601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715384730215029301089067 1073077095322543951633601)
              ·
                refine ⟨804807821491907963725201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1073077095322543951633601 804807821491907963725201)
                ·
                  refine ⟨603605866118930972793901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 804807821491907963725201 603605866118930972793901)
                  ·
                    refine ⟨226352199794599114797713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603605866118930972793901 226352199794599114797713)
                    ·
                      rfl

theorem cell22_661229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_661229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661229 prefixEnd_661229 := by exact prefixLift 661229
  have htrace : WordTrace (prefixWord ++ tailWord_661229) baseStart_661229 baseEnd_661229 := by
    simpa [prefixWord, tailWord_661229, baseEnd_661229] using wordTrace_append hprefix tailTrace_661229
  have hstable : (prefixWord ++ tailWord_661229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661229).length < 2 ^ (prefixWord ++ tailWord_661229).sum := by decide
  have hdescent : baseEnd_661229 < baseStart_661229 := by decide
  rcases family_descends (prefixWord ++ tailWord_661229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661246 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_661246 : Nat := 118140960795 + 661246 * 2 ^ 59
def prefixEnd_661246 : Nat := 4983230072969 + 3 ^ 40 * 661246 * 2
def baseEnd_661246 : Nat := 226358019242016737122661

theorem tailTrace_661246 : CollatzResearch.WordTrace tailWord_661246 prefixEnd_661246 226358019242016737122661 := by
  unfold tailWord_661246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3014702870303268583868449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16078415308284099113965061 3014702870303268583868449)
  ·
    refine ⟨2261027152727451437901337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3014702870303268583868449 2261027152727451437901337)
    ·
      refine ⟨1695770364545588578426003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2261027152727451437901337 1695770364545588578426003)
      ·
        refine ⟨2543655546818382867639005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695770364545588578426003 2543655546818382867639005)
        ·
          refine ⟨953870830056893575364627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2543655546818382867639005 953870830056893575364627)
          ·
            refine ⟨1430806245085340363046941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953870830056893575364627 1430806245085340363046941)
            ·
              refine ⟨536552341907002636142603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1430806245085340363046941 536552341907002636142603)
              ·
                refine ⟨804828512860503954213905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536552341907002636142603 804828512860503954213905)
                ·
                  refine ⟨603621384645377965660429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 804828512860503954213905 603621384645377965660429)
                  ·
                    refine ⟨226358019242016737122661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603621384645377965660429 226358019242016737122661)
                    ·
                      rfl

theorem cell22_661246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_661246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661246 prefixEnd_661246 := by exact prefixLift 661246
  have htrace : WordTrace (prefixWord ++ tailWord_661246) baseStart_661246 baseEnd_661246 := by
    simpa [prefixWord, tailWord_661246, baseEnd_661246] using wordTrace_append hprefix tailTrace_661246
  have hstable : (prefixWord ++ tailWord_661246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661246).length < 2 ^ (prefixWord ++ tailWord_661246).sum := by decide
  have hdescent : baseEnd_661246 < baseStart_661246 := by decide
  rcases family_descends (prefixWord ++ tailWord_661246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661274 : List Nat := [3, 1, 1, 3, 2, 2, 3, 3, 1, 3]
def baseStart_661274 : Nat := 118140960795 + 661274 * 2 ^ 59
def prefixEnd_661274 : Nat := 4983230072969 + 3 ^ 40 * 661274 * 2
def baseEnd_661274 : Nat := 226367604214233997422575

theorem tailTrace_661274 : CollatzResearch.WordTrace tailWord_661274 prefixEnd_661274 226367604214233997422575 := by
  unfold tailWord_661274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6029661051581177363241719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16079096137549806301977917 6029661051581177363241719)
  ·
    refine ⟨9044491577371766044862579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6029661051581177363241719 9044491577371766044862579)
    ·
      refine ⟨13566737366057649067293869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9044491577371766044862579 13566737366057649067293869)
      ·
        refine ⟨5087526512271618400235201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13566737366057649067293869 5087526512271618400235201)
        ·
          refine ⟨3815644884203713800176401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5087526512271618400235201 3815644884203713800176401)
          ·
            refine ⟨2861733663152785350132301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3815644884203713800176401 2861733663152785350132301)
            ·
              refine ⟨1073150123682294506299613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2861733663152785350132301 1073150123682294506299613)
              ·
                refine ⟨402431296380860439862355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1073150123682294506299613 402431296380860439862355)
                ·
                  refine ⟨603646944571290659793533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402431296380860439862355 603646944571290659793533)
                  ·
                    refine ⟨226367604214233997422575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603646944571290659793533 226367604214233997422575)
                    ·
                      rfl

theorem cell22_661274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_661274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661274 prefixEnd_661274 := by exact prefixLift 661274
  have htrace : WordTrace (prefixWord ++ tailWord_661274) baseStart_661274 baseEnd_661274 := by
    simpa [prefixWord, tailWord_661274, baseEnd_661274] using wordTrace_append hprefix tailTrace_661274
  have hstable : (prefixWord ++ tailWord_661274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661274).length < 2 ^ (prefixWord ++ tailWord_661274).sum := by decide
  have hdescent : baseEnd_661274 < baseStart_661274 := by decide
  rcases family_descends (prefixWord ++ tailWord_661274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661330 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_661330 : Nat := 118140960795 + 661330 * 2 ^ 59
def prefixEnd_661330 : Nat := 4983230072969 + 3 ^ 40 * 661330 * 2
def baseEnd_661330 : Nat := 226386774158668518022403

theorem tailTrace_661330 : CollatzResearch.WordTrace tailWord_661330 prefixEnd_661330 226386774158668518022403 := by
  unfold tailWord_661330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6030171673530457754251361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16080457796081220678003629 6030171673530457754251361)
  ·
    refine ⟨4522628755147843315688521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6030171673530457754251361 4522628755147843315688521)
    ·
      refine ⟨3391971566360882486766391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4522628755147843315688521 3391971566360882486766391)
      ·
        refine ⟨5087957349541323730149587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3391971566360882486766391 5087957349541323730149587)
        ·
          refine ⟨7631936024311985595224381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5087957349541323730149587 7631936024311985595224381)
          ·
            refine ⟨2861976009116994598209143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7631936024311985595224381 2861976009116994598209143)
            ·
              refine ⟨4292964013675491897313715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2861976009116994598209143 4292964013675491897313715)
              ·
                refine ⟨6439446020513237845970573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292964013675491897313715 6439446020513237845970573)
                ·
                  refine ⟨2414792257692464192238965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6439446020513237845970573 2414792257692464192238965)
                  ·
                    refine ⟨226386774158668518022403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2414792257692464192238965 226386774158668518022403)
                    ·
                      rfl

theorem cell22_661330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_661330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661330 prefixEnd_661330 := by exact prefixLift 661330
  have htrace : WordTrace (prefixWord ++ tailWord_661330) baseStart_661330 baseEnd_661330 := by
    simpa [prefixWord, tailWord_661330, baseEnd_661330] using wordTrace_append hprefix tailTrace_661330
  have hstable : (prefixWord ++ tailWord_661330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661330).length < 2 ^ (prefixWord ++ tailWord_661330).sum := by decide
  have hdescent : baseEnd_661330 < baseStart_661330 := by decide
  rcases family_descends (prefixWord ++ tailWord_661330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661343 : List Nat := [1, 1, 2, 3, 1, 14]
def baseStart_661343 : Nat := 118140960795 + 661343 * 2 ^ 59
def prefixEnd_661343 : Nat := 4983230072969 + 3 ^ 40 * 661343 * 2
def baseEnd_661343 : Nat := 2794953386720257005523

theorem tailTrace_661343 : CollatzResearch.WordTrace tailWord_661343 prefixEnd_661343 2794953386720257005523 := by
  unfold tailWord_661343
  simp only [CollatzResearch.WordTrace]
  refine ⟨24121160843074734237228683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16080773895383156158152455 24121160843074734237228683)
  ·
    refine ⟨36181741264612101355843025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24121160843074734237228683 36181741264612101355843025)
    ·
      refine ⟨27136305948459076016882269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36181741264612101355843025 27136305948459076016882269)
      ·
        refine ⟨10176114730672153506330851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27136305948459076016882269 10176114730672153506330851)
        ·
          refine ⟨15264172096008230259496277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10176114730672153506330851 15264172096008230259496277)
          ·
            refine ⟨2794953386720257005523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 15264172096008230259496277 2794953386720257005523)
            ·
              rfl

theorem cell22_661343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 14].length) (baseStart_661343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661343 prefixEnd_661343 := by exact prefixLift 661343
  have htrace : WordTrace (prefixWord ++ tailWord_661343) baseStart_661343 baseEnd_661343 := by
    simpa [prefixWord, tailWord_661343, baseEnd_661343] using wordTrace_append hprefix tailTrace_661343
  have hstable : (prefixWord ++ tailWord_661343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661343).length < 2 ^ (prefixWord ++ tailWord_661343).sum := by decide
  have hdescent : baseEnd_661343 < baseStart_661343 := by decide
  rcases family_descends (prefixWord ++ tailWord_661343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661345 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_661345 : Nat := 118140960795 + 661345 * 2 ^ 59
def prefixEnd_661345 : Nat := 4983230072969 + 3 ^ 40 * 661345 * 2
def baseEnd_661345 : Nat := 226391908965213478897357

theorem tailTrace_661345 : CollatzResearch.WordTrace tailWord_661345 prefixEnd_661345 226391908965213478897357 := by
  unfold tailWord_661345
  simp only [CollatzResearch.WordTrace]
  refine ⟨24121233789067488578801489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16080822526044992385867659 24121233789067488578801489)
  ·
    refine ⟨18090925341800616434101117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24121233789067488578801489 18090925341800616434101117)
    ·
      refine ⟨6784097003175231162787919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18090925341800616434101117 6784097003175231162787919)
      ·
        refine ⟨10176145504762846744181879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6784097003175231162787919 10176145504762846744181879)
        ·
          refine ⟨15264218257144270116272819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10176145504762846744181879 15264218257144270116272819)
          ·
            refine ⟨22896327385716405174409229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15264218257144270116272819 22896327385716405174409229)
            ·
              refine ⟨8586122769643651940403461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22896327385716405174409229 8586122769643651940403461)
              ·
                refine ⟨1609898019308184738825649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8586122769643651940403461 1609898019308184738825649)
                ·
                  refine ⟨1207423514481138554119237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1609898019308184738825649 1207423514481138554119237)
                  ·
                    refine ⟨226391908965213478897357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1207423514481138554119237 226391908965213478897357)
                    ·
                      rfl

theorem cell22_661345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_661345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661345 prefixEnd_661345 := by exact prefixLift 661345
  have htrace : WordTrace (prefixWord ++ tailWord_661345) baseStart_661345 baseEnd_661345 := by
    simpa [prefixWord, tailWord_661345, baseEnd_661345] using wordTrace_append hprefix tailTrace_661345
  have hstable : (prefixWord ++ tailWord_661345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661345).length < 2 ^ (prefixWord ++ tailWord_661345).sum := by decide
  have hdescent : baseEnd_661345 < baseStart_661345 := by decide
  rcases family_descends (prefixWord ++ tailWord_661345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661398 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_661398 : Nat := 118140960795 + 661398 * 2 ^ 59
def prefixEnd_661398 : Nat := 4983230072969 + 3 ^ 40 * 661398 * 2
def baseEnd_661398 : Nat := 226410051948339007322195

theorem tailTrace_661398 : CollatzResearch.WordTrace tailWord_661398 prefixEnd_661398 226410051948339007322195 := by
  unfold tailWord_661398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507697928617217414405053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16082111238583652420320565 1507697928617217414405053)
  ·
    refine ⟨565386723231456530401895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1507697928617217414405053 565386723231456530401895)
    ·
      refine ⟨848080084847184795602843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565386723231456530401895 848080084847184795602843)
      ·
        refine ⟨1272120127270777193404265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848080084847184795602843 1272120127270777193404265)
        ·
          refine ⟨954090095453082895053199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272120127270777193404265 954090095453082895053199)
          ·
            refine ⟨1431135143179624342579799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954090095453082895053199 1431135143179624342579799)
            ·
              refine ⟨2146702714769436513869699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1431135143179624342579799 2146702714769436513869699)
              ·
                refine ⟨3220054072154154770804549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146702714769436513869699 3220054072154154770804549)
                ·
                  refine ⟨603760138528904019525853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3220054072154154770804549 603760138528904019525853)
                  ·
                    refine ⟨226410051948339007322195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603760138528904019525853 226410051948339007322195)
                    ·
                      rfl

theorem cell22_661398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_661398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661398 prefixEnd_661398 := by exact prefixLift 661398
  have htrace : WordTrace (prefixWord ++ tailWord_661398) baseStart_661398 baseEnd_661398 := by
    simpa [prefixWord, tailWord_661398, baseEnd_661398] using wordTrace_append hprefix tailTrace_661398
  have hstable : (prefixWord ++ tailWord_661398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661398).length < 2 ^ (prefixWord ++ tailWord_661398).sum := by decide
  have hdescent : baseEnd_661398 < baseStart_661398 := by decide
  rcases family_descends (prefixWord ++ tailWord_661398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661428 : List Nat := [2, 5, 2, 1, 3, 1, 2, 6]
def baseStart_661428 : Nat := 118140960795 + 661428 * 2 ^ 59
def prefixEnd_661428 : Nat := 4983230072969 + 3 ^ 40 * 661428 * 2
def baseEnd_661428 : Nat := 25157813506825436563567

theorem tailTrace_661428 : CollatzResearch.WordTrace tailWord_661428 prefixEnd_661428 25157813506825436563567 := by
  unfold tailWord_661428
  simp only [CollatzResearch.WordTrace]
  refine ⟨12062130523883396877036469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16082840698511195836048625 12062130523883396877036469)
  ·
    refine ⟨1130824736614068457222169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12062130523883396877036469 1130824736614068457222169)
    ·
      refine ⟨848118552460551342916627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1130824736614068457222169 848118552460551342916627)
      ·
        refine ⟨1272177828690827014374941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848118552460551342916627 1272177828690827014374941)
        ·
          refine ⟨477066685759060130390603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1272177828690827014374941 477066685759060130390603)
          ·
            refine ⟨715600028638590195585905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477066685759060130390603 715600028638590195585905)
            ·
              refine ⟨536700021478942646689429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715600028638590195585905 536700021478942646689429)
              ·
                refine ⟨25157813506825436563567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 536700021478942646689429 25157813506825436563567)
                ·
                  rfl

theorem cell22_661428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 6].length) (baseStart_661428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661428 prefixEnd_661428 := by exact prefixLift 661428
  have htrace : WordTrace (prefixWord ++ tailWord_661428) baseStart_661428 baseEnd_661428 := by
    simpa [prefixWord, tailWord_661428, baseEnd_661428] using wordTrace_append hprefix tailTrace_661428
  have hstable : (prefixWord ++ tailWord_661428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661428).length < 2 ^ (prefixWord ++ tailWord_661428).sum := by decide
  have hdescent : baseEnd_661428 < baseStart_661428 := by decide
  rcases family_descends (prefixWord ++ tailWord_661428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661450 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_661450 : Nat := 118140960795 + 661450 * 2 ^ 59
def prefixEnd_661450 : Nat := 4983230072969 + 3 ^ 40 * 661450 * 2
def baseEnd_661450 : Nat := 75475950870342735007345

theorem tailTrace_661450 : CollatzResearch.WordTrace tailWord_661450 prefixEnd_661450 75475950870342735007345 := by
  unfold tailWord_661450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031265863421772877843451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16083375635791394340915869 6031265863421772877843451)
  ·
    refine ⟨9046898795132659316765177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6031265863421772877843451 9046898795132659316765177)
    ·
      refine ⟨6785174096349494487573883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9046898795132659316765177 6785174096349494487573883)
      ·
        refine ⟨10177761144524241731360825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6785174096349494487573883 10177761144524241731360825)
        ·
          refine ⟨7633320858393181298520619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10177761144524241731360825 7633320858393181298520619)
          ·
            refine ⟨11449981287589771947780929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7633320858393181298520619 11449981287589771947780929)
            ·
              refine ⟨8587485965692328960835697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11449981287589771947780929 8587485965692328960835697)
              ·
                refine ⟨6440614474269246720626773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8587485965692328960835697 6440614474269246720626773)
                ·
                  refine ⟨75475950870342735007345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6440614474269246720626773 75475950870342735007345)
                  ·
                    rfl

theorem cell22_661450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_661450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661450 prefixEnd_661450 := by exact prefixLift 661450
  have htrace : WordTrace (prefixWord ++ tailWord_661450) baseStart_661450 baseEnd_661450 := by
    simpa [prefixWord, tailWord_661450, baseEnd_661450] using wordTrace_append hprefix tailTrace_661450
  have hstable : (prefixWord ++ tailWord_661450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661450).length < 2 ^ (prefixWord ++ tailWord_661450).sum := by decide
  have hdescent : baseEnd_661450 < baseStart_661450 := by decide
  rcases family_descends (prefixWord ++ tailWord_661450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661482 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_661482 : Nat := 118140960795 + 661482 * 2 ^ 59
def prefixEnd_661482 : Nat := 4983230072969 + 3 ^ 40 * 661482 * 2
def baseEnd_661482 : Nat := 226438806864990788221937

theorem tailTrace_661482 : CollatzResearch.WordTrace tailWord_661482 prefixEnd_661482 226438806864990788221937 := by
  unfold tailWord_661482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031557647392790244134675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16084153726380773984359133 6031557647392790244134675)
  ·
    refine ⟨9047336471089185366202013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6031557647392790244134675 9047336471089185366202013)
    ·
      refine ⟨3392751176658444512325755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9047336471089185366202013 3392751176658444512325755)
      ·
        refine ⟨5089126764987666768488633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3392751176658444512325755 5089126764987666768488633)
        ·
          refine ⟨3816845073740750076366475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5089126764987666768488633 3816845073740750076366475)
          ·
            refine ⟨5725267610611125114549713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816845073740750076366475 5725267610611125114549713)
            ·
              refine ⟨4293950707958343835912285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5725267610611125114549713 4293950707958343835912285)
              ·
                refine ⟨1610231515484378938467107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4293950707958343835912285 1610231515484378938467107)
                ·
                  refine ⟨2415347273226568407700661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610231515484378938467107 2415347273226568407700661)
                  ·
                    refine ⟨226438806864990788221937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2415347273226568407700661 226438806864990788221937)
                    ·
                      rfl

theorem cell22_661482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_661482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661482 prefixEnd_661482 := by exact prefixLift 661482
  have htrace : WordTrace (prefixWord ++ tailWord_661482) baseStart_661482 baseEnd_661482 := by
    simpa [prefixWord, tailWord_661482, baseEnd_661482] using wordTrace_append hprefix tailTrace_661482
  have hstable : (prefixWord ++ tailWord_661482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661482).length < 2 ^ (prefixWord ++ tailWord_661482).sum := by decide
  have hdescent : baseEnd_661482 < baseStart_661482 := by decide
  rcases family_descends (prefixWord ++ tailWord_661482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661486 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_661486 : Nat := 118140960795 + 661486 * 2 ^ 59
def prefixEnd_661486 : Nat := 4983230072969 + 3 ^ 40 * 661486 * 2
def baseEnd_661486 : Nat := 226440176146736111121925

theorem tailTrace_661486 : CollatzResearch.WordTrace tailWord_661486 prefixEnd_661486 226440176146736111121925 := by
  unfold tailWord_661486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3015797060194583707460539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16084250987704446439789541 3015797060194583707460539)
  ·
    refine ⟨4523695590291875561190809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3015797060194583707460539 4523695590291875561190809)
    ·
      refine ⟨3392771692718906670893107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4523695590291875561190809 3392771692718906670893107)
      ·
        refine ⟨5089157539078360006339661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3392771692718906670893107 5089157539078360006339661)
        ·
          refine ⟨1908434077154385002377373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5089157539078360006339661 1908434077154385002377373)
          ·
            refine ⟨715662778932894375891515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1908434077154385002377373 715662778932894375891515)
            ·
              refine ⟨1073494168399341563837273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715662778932894375891515 1073494168399341563837273)
              ·
                refine ⟨805120626299506172877955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1073494168399341563837273 805120626299506172877955)
                ·
                  refine ⟨1207680939449259259316933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805120626299506172877955 1207680939449259259316933)
                  ·
                    refine ⟨226440176146736111121925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1207680939449259259316933 226440176146736111121925)
                    ·
                      rfl

theorem cell22_661486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_661486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661486 prefixEnd_661486 := by exact prefixLift 661486
  have htrace : WordTrace (prefixWord ++ tailWord_661486) baseStart_661486 baseEnd_661486 := by
    simpa [prefixWord, tailWord_661486, baseEnd_661486] using wordTrace_append hprefix tailTrace_661486
  have hstable : (prefixWord ++ tailWord_661486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661486).length < 2 ^ (prefixWord ++ tailWord_661486).sum := by decide
  have hdescent : baseEnd_661486 < baseStart_661486 := by decide
  rcases family_descends (prefixWord ++ tailWord_661486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661497 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_661497 : Nat := 118140960795 + 661497 * 2 ^ 59
def prefixEnd_661497 : Nat := 4983230072969 + 3 ^ 40 * 661497 * 2
def baseEnd_661497 : Nat := 226443941671535749096891

theorem tailTrace_661497 : CollatzResearch.WordTrace tailWord_661497 prefixEnd_661497 226443941671535749096891 := by
  unfold tailWord_661497
  simp only [CollatzResearch.WordTrace]
  refine ⟨24126777684516818538334745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16084518456344545692223163 24126777684516818538334745)
  ·
    refine ⟨18095083263387613903751059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24126777684516818538334745 18095083263387613903751059)
    ·
      refine ⟨27142624895081420855626589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18095083263387613903751059 27142624895081420855626589)
      ·
        refine ⟨10178484335655532820859971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27142624895081420855626589 10178484335655532820859971)
        ·
          refine ⟨15267726503483299231289957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10178484335655532820859971 15267726503483299231289957)
          ·
            refine ⟨2862698719403118605866867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15267726503483299231289957 2862698719403118605866867)
            ·
              refine ⟨4294048079104677908800301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2862698719403118605866867 4294048079104677908800301)
              ·
                refine ⟨1610268029664254215800113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4294048079104677908800301 1610268029664254215800113)
                ·
                  refine ⟨1207701022248190661850085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1610268029664254215800113 1207701022248190661850085)
                  ·
                    refine ⟨226443941671535749096891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1207701022248190661850085 226443941671535749096891)
                    ·
                      rfl

theorem cell22_661497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_661497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661497 prefixEnd_661497 := by exact prefixLift 661497
  have htrace : WordTrace (prefixWord ++ tailWord_661497) baseStart_661497 baseEnd_661497 := by
    simpa [prefixWord, tailWord_661497, baseEnd_661497] using wordTrace_append hprefix tailTrace_661497
  have hstable : (prefixWord ++ tailWord_661497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661497).length < 2 ^ (prefixWord ++ tailWord_661497).sum := by decide
  have hdescent : baseEnd_661497 < baseStart_661497 := by decide
  rcases family_descends (prefixWord ++ tailWord_661497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661604 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_661604 : Nat := 118140960795 + 661604 * 2 ^ 59
def prefixEnd_661604 : Nat := 4983230072969 + 3 ^ 40 * 661604 * 2
def baseEnd_661604 : Nat := 226480569958223136671563

theorem tailTrace_661604 : CollatzResearch.WordTrace tailWord_661604 prefixEnd_661604 226480569958223136671563 := by
  unfold tailWord_661604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12065340147564587906239933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16087120196752783874986577 12065340147564587906239933)
  ·
    refine ⟨4524502555336720464839975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12065340147564587906239933 4524502555336720464839975)
    ·
      refine ⟨6786753833005080697259963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4524502555336720464839975 6786753833005080697259963)
      ·
        refine ⟨10180130749507621045889945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6786753833005080697259963 10180130749507621045889945)
        ·
          refine ⟨7635098062130715784417459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10180130749507621045889945 7635098062130715784417459)
          ·
            refine ⟨11452647093196073676626189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7635098062130715784417459 11452647093196073676626189)
            ·
              refine ⟨4294742659948527628734821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11452647093196073676626189 4294742659948527628734821)
              ·
                refine ⟨805264248740348930387779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4294742659948527628734821 805264248740348930387779)
                ·
                  refine ⟨1207896373110523395581669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805264248740348930387779 1207896373110523395581669)
                  ·
                    refine ⟨226480569958223136671563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1207896373110523395581669 226480569958223136671563)
                    ·
                      rfl

theorem cell22_661604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_661604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661604 prefixEnd_661604 := by exact prefixLift 661604
  have htrace : WordTrace (prefixWord ++ tailWord_661604) baseStart_661604 baseEnd_661604 := by
    simpa [prefixWord, tailWord_661604, baseEnd_661604] using wordTrace_append hprefix tailTrace_661604
  have hstable : (prefixWord ++ tailWord_661604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661604).length < 2 ^ (prefixWord ++ tailWord_661604).sum := by decide
  have hdescent : baseEnd_661604 < baseStart_661604 := by decide
  rcases family_descends (prefixWord ++ tailWord_661604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661617 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_661617 : Nat := 118140960795 + 661617 * 2 ^ 59
def prefixEnd_661617 : Nat := 4983230072969 + 3 ^ 40 * 661617 * 2
def baseEnd_661617 : Nat := 226485020123895436096523

theorem tailTrace_661617 : CollatzResearch.WordTrace tailWord_661617 prefixEnd_661617 226485020123895436096523 := by
  unfold tailWord_661617
  simp only [CollatzResearch.WordTrace]
  refine ⟨24131154444082079032703105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16087436296054719355135403 24131154444082079032703105)
  ·
    refine ⟨18098365833061559274527329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24131154444082079032703105 18098365833061559274527329)
    ·
      refine ⟨13573774374796169455895497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18098365833061559274527329 13573774374796169455895497)
      ·
        refine ⟨10180330781097127091921623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13573774374796169455895497 10180330781097127091921623)
        ·
          refine ⟨15270496171645690637882435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10180330781097127091921623 15270496171645690637882435)
          ·
            refine ⟨22905744257468535956823653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15270496171645690637882435 22905744257468535956823653)
            ·
              refine ⟨4294827048275350491904435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22905744257468535956823653 4294827048275350491904435)
              ·
                refine ⟨6442240572413025737856653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294827048275350491904435 6442240572413025737856653)
                ·
                  refine ⟨2415840214654884651696245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6442240572413025737856653 2415840214654884651696245)
                  ·
                    refine ⟨226485020123895436096523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2415840214654884651696245 226485020123895436096523)
                    ·
                      rfl

theorem cell22_661617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_661617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661617 prefixEnd_661617 := by exact prefixLift 661617
  have htrace : WordTrace (prefixWord ++ tailWord_661617) baseStart_661617 baseEnd_661617 := by
    simpa [prefixWord, tailWord_661617, baseEnd_661617] using wordTrace_append hprefix tailTrace_661617
  have hstable : (prefixWord ++ tailWord_661617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661617).length < 2 ^ (prefixWord ++ tailWord_661617).sum := by decide
  have hdescent : baseEnd_661617 < baseStart_661617 := by decide
  rcases family_descends (prefixWord ++ tailWord_661617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661666 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_661666 : Nat := 118140960795 + 661666 * 2 ^ 59
def prefixEnd_661666 : Nat := 4983230072969 + 3 ^ 40 * 661666 * 2
def baseEnd_661666 : Nat := 226501793825275641621373

theorem tailTrace_661666 : CollatzResearch.WordTrace tailWord_661666 prefixEnd_661666 226501793825275641621373 := by
  unfold tailWord_661666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6033235405226140100309213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16088627747269706934157901 6033235405226140100309213)
  ·
    refine ⟨2262463276959802537615955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6033235405226140100309213 2262463276959802537615955)
    ·
      refine ⟨3393694915439703806423933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262463276959802537615955 3393694915439703806423933)
      ·
        refine ⟨1272635593289888927408975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3393694915439703806423933 1272635593289888927408975)
        ·
          refine ⟨1908953389934833391113463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272635593289888927408975 1908953389934833391113463)
          ·
            refine ⟨2863430084902250086670195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908953389934833391113463 2863430084902250086670195)
            ·
              refine ⟨4295145127353375130005293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2863430084902250086670195 4295145127353375130005293)
              ·
                refine ⟨1610679422757515673751985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4295145127353375130005293 1610679422757515673751985)
                ·
                  refine ⟨1208009567068136755313989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1610679422757515673751985 1208009567068136755313989)
                  ·
                    refine ⟨226501793825275641621373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1208009567068136755313989 226501793825275641621373)
                    ·
                      rfl

theorem cell22_661666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_661666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661666 prefixEnd_661666 := by exact prefixLift 661666
  have htrace : WordTrace (prefixWord ++ tailWord_661666) baseStart_661666 baseEnd_661666 := by
    simpa [prefixWord, tailWord_661666, baseEnd_661666] using wordTrace_append hprefix tailTrace_661666
  have hstable : (prefixWord ++ tailWord_661666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661666).length < 2 ^ (prefixWord ++ tailWord_661666).sum := by decide
  have hdescent : baseEnd_661666 < baseStart_661666 := by decide
  rcases family_descends (prefixWord ++ tailWord_661666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661685 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 2, 3]
def baseStart_661685 : Nat := 118140960795 + 661685 * 2 ^ 59
def prefixEnd_661685 : Nat := 4983230072969 + 3 ^ 40 * 661685 * 2
def baseEnd_661685 : Nat := 226508297913565925396315

theorem tailTrace_661685 : CollatzResearch.WordTrace tailWord_661685 prefixEnd_661685 226508297913565925396315 := by
  unfold tailWord_661685
  simp only [CollatzResearch.WordTrace]
  refine ⟨24133634607835726646178509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16089089738557151097452339 24133634607835726646178509)
  ·
    refine ⟨9050112977938397492316941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24133634607835726646178509 9050112977938397492316941)
    ·
      refine ⟨3393792366726899059618853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9050112977938397492316941 3393792366726899059618853)
      ·
        refine ⟨636336068761293573678535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3393792366726899059618853 636336068761293573678535)
        ·
          refine ⟨954504103141940360517803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636336068761293573678535 954504103141940360517803)
          ·
            refine ⟨1431756154712910540776705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954504103141940360517803 1431756154712910540776705)
            ·
              refine ⟨1073817116034682905582529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1431756154712910540776705 1073817116034682905582529)
              ·
                refine ⟨805362837026012179186897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1073817116034682905582529 805362837026012179186897)
                ·
                  refine ⟨604022127769509134390173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 805362837026012179186897 604022127769509134390173)
                  ·
                    refine ⟨226508297913565925396315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 604022127769509134390173 226508297913565925396315)
                    ·
                      rfl

theorem cell22_661685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_661685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661685 prefixEnd_661685 := by exact prefixLift 661685
  have htrace : WordTrace (prefixWord ++ tailWord_661685) baseStart_661685 baseEnd_661685 := by
    simpa [prefixWord, tailWord_661685, baseEnd_661685] using wordTrace_append hprefix tailTrace_661685
  have hstable : (prefixWord ++ tailWord_661685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661685).length < 2 ^ (prefixWord ++ tailWord_661685).sum := by decide
  have hdescent : baseEnd_661685 < baseStart_661685 := by decide
  rcases family_descends (prefixWord ++ tailWord_661685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661698 : List Nat := [3, 5, 1, 1, 1, 1, 3, 7]
def baseStart_661698 : Nat := 118140960795 + 661698 * 2 ^ 59
def prefixEnd_661698 : Nat := 4983230072969 + 3 ^ 40 * 661698 * 2
def baseEnd_661698 : Nat := 25168083119915358313475

theorem tailTrace_661698 : CollatzResearch.WordTrace tailWord_661698 prefixEnd_661698 25168083119915358313475 := by
  unfold tailWord_661698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6033527189197157466600437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16089405837859086577601165 6033527189197157466600437)
  ·
    refine ⟨565643173987233512493791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6033527189197157466600437 565643173987233512493791)
    ·
      refine ⟨848464760980850268740687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565643173987233512493791 848464760980850268740687)
      ·
        refine ⟨1272697141471275403111031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848464760980850268740687 1272697141471275403111031)
        ·
          refine ⟨1909045712206913104666547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272697141471275403111031 1909045712206913104666547)
          ·
            refine ⟨2863568568310369656999821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909045712206913104666547 2863568568310369656999821)
            ·
              refine ⟨1073838213116388621374933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2863568568310369656999821 1073838213116388621374933)
              ·
                refine ⟨25168083119915358313475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1073838213116388621374933 25168083119915358313475)
                ·
                  rfl

theorem cell22_661698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_661698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661698 prefixEnd_661698 := by exact prefixLift 661698
  have htrace : WordTrace (prefixWord ++ tailWord_661698) baseStart_661698 baseEnd_661698 := by
    simpa [prefixWord, tailWord_661698, baseEnd_661698] using wordTrace_append hprefix tailTrace_661698
  have hstable : (prefixWord ++ tailWord_661698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661698).length < 2 ^ (prefixWord ++ tailWord_661698).sum := by decide
  have hdescent : baseEnd_661698 < baseStart_661698 := by decide
  rcases family_descends (prefixWord ++ tailWord_661698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661754 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_661754 : Nat := 118140960795 + 661754 * 2 ^ 59
def prefixEnd_661754 : Nat := 4983230072969 + 3 ^ 40 * 661754 * 2
def baseEnd_661754 : Nat := 75510639341224248473701

theorem tailTrace_661754 : CollatzResearch.WordTrace tailWord_661754 prefixEnd_661754 75510639341224248473701 := by
  unfold tailWord_661754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6034037811146437857610079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16090767496390500953626877 6034037811146437857610079)
  ·
    refine ⟨9051056716719656786415119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6034037811146437857610079 9051056716719656786415119)
    ·
      refine ⟨13576585075079485179622679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9051056716719656786415119 13576585075079485179622679)
      ·
        refine ⟨20364877612619227769434019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13576585075079485179622679 20364877612619227769434019)
        ·
          refine ⟨30547316418928841654151029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20364877612619227769434019 30547316418928841654151029)
          ·
            refine ⟨2863810914274578905076659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30547316418928841654151029 2863810914274578905076659)
            ·
              refine ⟨4295716371411868357614989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2863810914274578905076659 4295716371411868357614989)
              ·
                refine ⟨1610893639279450634105621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4295716371411868357614989 1610893639279450634105621)
                ·
                  refine ⟨75510639341224248473701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1610893639279450634105621 75510639341224248473701)
                  ·
                    rfl

theorem cell22_661754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_661754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661754 prefixEnd_661754 := by exact prefixLift 661754
  have htrace : WordTrace (prefixWord ++ tailWord_661754) baseStart_661754 baseEnd_661754 := by
    simpa [prefixWord, tailWord_661754, baseEnd_661754] using wordTrace_append hprefix tailTrace_661754
  have hstable : (prefixWord ++ tailWord_661754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661754).length < 2 ^ (prefixWord ++ tailWord_661754).sum := by decide
  have hdescent : baseEnd_661754 < baseStart_661754 := by decide
  rcases family_descends (prefixWord ++ tailWord_661754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661784 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_661784 : Nat := 118140960795 + 661784 * 2 ^ 59
def prefixEnd_661784 : Nat := 4983230072969 + 3 ^ 40 * 661784 * 2
def baseEnd_661784 : Nat := 226542187636762667171011

theorem tailTrace_661784 : CollatzResearch.WordTrace tailWord_661784 prefixEnd_661784 226542187636762667171011 := by
  unfold tailWord_661784
  simp only [CollatzResearch.WordTrace]
  refine ⟨12068622717238533277016203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16091496956318044369354937 12068622717238533277016203)
  ·
    refine ⟨18102934075857799915524305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12068622717238533277016203 18102934075857799915524305)
    ·
      refine ⟨13577200556893349936643229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18102934075857799915524305 13577200556893349936643229)
      ·
        refine ⟨5091450208835006226241211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13577200556893349936643229 5091450208835006226241211)
        ·
          refine ⟨7637175313252509339361817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5091450208835006226241211 7637175313252509339361817)
          ·
            refine ⟨5727881484939382004521363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7637175313252509339361817 5727881484939382004521363)
            ·
              refine ⟨8591822227409073006782045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727881484939382004521363 8591822227409073006782045)
              ·
                refine ⟨3221933335278402377543267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8591822227409073006782045 3221933335278402377543267)
                ·
                  refine ⟨4832900002917603566314901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221933335278402377543267 4832900002917603566314901)
                  ·
                    refine ⟨226542187636762667171011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4832900002917603566314901 226542187636762667171011)
                    ·
                      rfl

theorem cell22_661784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_661784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661784 prefixEnd_661784 := by exact prefixLift 661784
  have htrace : WordTrace (prefixWord ++ tailWord_661784) baseStart_661784 baseEnd_661784 := by
    simpa [prefixWord, tailWord_661784, baseEnd_661784] using wordTrace_append hprefix tailTrace_661784
  have hstable : (prefixWord ++ tailWord_661784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661784).length < 2 ^ (prefixWord ++ tailWord_661784).sum := by decide
  have hdescent : baseEnd_661784 < baseStart_661784 := by decide
  rcases family_descends (prefixWord ++ tailWord_661784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661790 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_661790 : Nat := 118140960795 + 661790 * 2 ^ 59
def prefixEnd_661790 : Nat := 4983230072969 + 3 ^ 40 * 661790 * 2
def baseEnd_661790 : Nat := 226544241559380651520993

theorem tailTrace_661790 : CollatzResearch.WordTrace tailWord_661790 prefixEnd_661790 226544241559380651520993 := by
  unfold tailWord_661790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3017183034056916197343853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16091642848303553052500549 3017183034056916197343853)
  ·
    refine ⟨1131443637771343574003945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3017183034056916197343853 1131443637771343574003945)
    ·
      refine ⟨848582728328507680502959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1131443637771343574003945 848582728328507680502959)
      ·
        refine ⟨1272874092492761520754439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848582728328507680502959 1272874092492761520754439)
        ·
          refine ⟨1909311138739142281131659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272874092492761520754439 1909311138739142281131659)
          ·
            refine ⟨2863966708108713421697489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909311138739142281131659 2863966708108713421697489)
            ·
              refine ⟨2147975031081535066273117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2863966708108713421697489 2147975031081535066273117)
              ·
                refine ⟨805490636655575649852419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2147975031081535066273117 805490636655575649852419)
                ·
                  refine ⟨1208235954983363474778629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805490636655575649852419 1208235954983363474778629)
                  ·
                    refine ⟨226544241559380651520993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1208235954983363474778629 226544241559380651520993)
                    ·
                      rfl

theorem cell22_661790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_661790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661790 prefixEnd_661790 := by exact prefixLift 661790
  have htrace : WordTrace (prefixWord ++ tailWord_661790) baseStart_661790 baseEnd_661790 := by
    simpa [prefixWord, tailWord_661790, baseEnd_661790] using wordTrace_append hprefix tailTrace_661790
  have hstable : (prefixWord ++ tailWord_661790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661790).length < 2 ^ (prefixWord ++ tailWord_661790).sum := by decide
  have hdescent : baseEnd_661790 < baseStart_661790 := by decide
  rcases family_descends (prefixWord ++ tailWord_661790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661805 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 6]
def baseStart_661805 : Nat := 118140960795 + 661805 * 2 ^ 59
def prefixEnd_661805 : Nat := 4983230072969 + 3 ^ 40 * 661805 * 2
def baseEnd_661805 : Nat := 75516458788641870798649

theorem tailTrace_661805 : CollatzResearch.WordTrace tailWord_661805 prefixEnd_661805 75516458788641870798649 := by
  unfold tailWord_661805
  simp only [CollatzResearch.WordTrace]
  refine ⟨24138011367400987140546869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16092007578267324760364579 24138011367400987140546869)
  ·
    refine ⟨2262938565693842544426269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24138011367400987140546869 2262938565693842544426269)
    ·
      refine ⟨848601962135190954159851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2262938565693842544426269 848601962135190954159851)
      ·
        refine ⟨1272902943202786431239777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848601962135190954159851 1272902943202786431239777)
        ·
          refine ⟨954677207402089823429833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272902943202786431239777 954677207402089823429833)
          ·
            refine ⟨716007905551567367572375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954677207402089823429833 716007905551567367572375)
            ·
              refine ⟨1074011858327351051358563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716007905551567367572375 1074011858327351051358563)
              ·
                refine ⟨1611017787491026577037845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074011858327351051358563 1611017787491026577037845)
                ·
                  refine ⟨75516458788641870798649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1611017787491026577037845 75516458788641870798649)
                  ·
                    rfl

theorem cell22_661805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_661805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661805 prefixEnd_661805 := by exact prefixLift 661805
  have htrace : WordTrace (prefixWord ++ tailWord_661805) baseStart_661805 baseEnd_661805 := by
    simpa [prefixWord, tailWord_661805, baseEnd_661805] using wordTrace_append hprefix tailTrace_661805
  have hstable : (prefixWord ++ tailWord_661805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661805).length < 2 ^ (prefixWord ++ tailWord_661805).sum := by decide
  have hdescent : baseEnd_661805 < baseStart_661805 := by decide
  rcases family_descends (prefixWord ++ tailWord_661805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661831 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 5, 3]
def baseStart_661831 : Nat := 118140960795 + 661831 * 2 ^ 59
def prefixEnd_661831 : Nat := 4983230072969 + 3 ^ 40 * 661831 * 2
def baseEnd_661831 : Nat := 226558276697270211245867

theorem tailTrace_661831 : CollatzResearch.WordTrace tailWord_661831 prefixEnd_661831 226558276697270211245867 := by
  unfold tailWord_661831
  simp only [CollatzResearch.WordTrace]
  refine ⟨24138959665306793580993347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16092639776871195720662231 24138959665306793580993347)
  ·
    refine ⟨36208439497960190371490021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24138959665306793580993347 36208439497960190371490021)
    ·
      refine ⟨6789082405867535694654379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36208439497960190371490021 6789082405867535694654379)
      ·
        refine ⟨10183623608801303541981569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6789082405867535694654379 10183623608801303541981569)
        ·
          refine ⟨7637717706600977656486177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10183623608801303541981569 7637717706600977656486177)
          ·
            refine ⟨5728288279950733242364633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7637717706600977656486177 5728288279950733242364633)
            ·
              refine ⟨4296216209963049931773475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5728288279950733242364633 4296216209963049931773475)
              ·
                refine ⟨6444324314944574897660213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4296216209963049931773475 6444324314944574897660213)
                ·
                  refine ⟨604155404526053896655645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6444324314944574897660213 604155404526053896655645)
                  ·
                    refine ⟨226558276697270211245867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 604155404526053896655645 226558276697270211245867)
                    ·
                      rfl

theorem cell22_661831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_661831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661831 prefixEnd_661831 := by exact prefixLift 661831
  have htrace : WordTrace (prefixWord ++ tailWord_661831) baseStart_661831 baseEnd_661831 := by
    simpa [prefixWord, tailWord_661831, baseEnd_661831] using wordTrace_append hprefix tailTrace_661831
  have hstable : (prefixWord ++ tailWord_661831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661831).length < 2 ^ (prefixWord ++ tailWord_661831).sum := by decide
  have hdescent : baseEnd_661831 < baseStart_661831 := by decide
  rcases family_descends (prefixWord ++ tailWord_661831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661861 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 5]
def baseStart_661861 : Nat := 118140960795 + 661861 * 2 ^ 59
def prefixEnd_661861 : Nat := 4983230072969 + 3 ^ 40 * 661861 * 2
def baseEnd_661861 : Nat := 75522848770120044331925

theorem tailTrace_661861 : CollatzResearch.WordTrace tailWord_661861 prefixEnd_661861 75522848770120044331925 := by
  unfold tailWord_661861
  simp only [CollatzResearch.WordTrace]
  refine ⟨24140053855198108704585437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16093369236798739136390291 24140053855198108704585437)
  ·
    refine ⟨9052520195699290764219539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24140053855198108704585437 9052520195699290764219539)
    ·
      refine ⟨13578780293548936146329309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9052520195699290764219539 13578780293548936146329309)
      ·
        refine ⟨5092042610080851054873491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13578780293548936146329309 5092042610080851054873491)
        ·
          refine ⟨7638063915121276582310237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5092042610080851054873491 7638063915121276582310237)
          ·
            refine ⟨2864273968170478718366339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7638063915121276582310237 2864273968170478718366339)
            ·
              refine ⟨4296410952255718077549509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864273968170478718366339 4296410952255718077549509)
              ·
                refine ⟨805577053547947139540533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4296410952255718077549509 805577053547947139540533)
                ·
                  refine ⟨75522848770120044331925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 805577053547947139540533 75522848770120044331925)
                  ·
                    rfl

theorem cell22_661861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_661861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661861 prefixEnd_661861 := by exact prefixLift 661861
  have htrace : WordTrace (prefixWord ++ tailWord_661861) baseStart_661861 baseEnd_661861 := by
    simpa [prefixWord, tailWord_661861, baseEnd_661861] using wordTrace_append hprefix tailTrace_661861
  have hstable : (prefixWord ++ tailWord_661861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661861).length < 2 ^ (prefixWord ++ tailWord_661861).sum := by decide
  have hdescent : baseEnd_661861 < baseStart_661861 := by decide
  rcases family_descends (prefixWord ++ tailWord_661861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661923 : List Nat := [1, 1, 1, 4, 1, 4, 2, 4, 4]
def baseStart_661923 : Nat := 118140960795 + 661923 * 2 ^ 59
def prefixEnd_661923 : Nat := 4983230072969 + 3 ^ 40 * 661923 * 2
def baseEnd_661923 : Nat := 75529923392470879315195

theorem tailTrace_661923 : CollatzResearch.WordTrace tailWord_661923 prefixEnd_661923 75529923392470879315195 := by
  unfold tailWord_661923
  simp only [CollatzResearch.WordTrace]
  refine ⟨24142315180973493293342423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16094876787315662195561615 24142315180973493293342423)
  ·
    refine ⟨36213472771460239940013635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24142315180973493293342423 36213472771460239940013635)
    ·
      refine ⟨54320209157190359910020453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36213472771460239940013635 54320209157190359910020453)
      ·
        refine ⟨10185039216973192483128835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54320209157190359910020453 10185039216973192483128835)
        ·
          refine ⟨15277558825459788724693253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10185039216973192483128835 15277558825459788724693253)
          ·
            refine ⟨2864542279773710385879985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15277558825459788724693253 2864542279773710385879985)
            ·
              refine ⟨2148406709830282789409989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2864542279773710385879985 2148406709830282789409989)
              ·
                refine ⟨402826258093178023014373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2148406709830282789409989 402826258093178023014373)
                ·
                  refine ⟨75529923392470879315195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 402826258093178023014373 75529923392470879315195)
                  ·
                    rfl

theorem cell22_661923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 4].length) (baseStart_661923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661923 prefixEnd_661923 := by exact prefixLift 661923
  have htrace : WordTrace (prefixWord ++ tailWord_661923) baseStart_661923 baseEnd_661923 := by
    simpa [prefixWord, tailWord_661923, baseEnd_661923] using wordTrace_append hprefix tailTrace_661923
  have hstable : (prefixWord ++ tailWord_661923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661923).length < 2 ^ (prefixWord ++ tailWord_661923).sum := by decide
  have hdescent : baseEnd_661923 < baseStart_661923 := by decide
  rcases family_descends (prefixWord ++ tailWord_661923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661989 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 2, 3]
def baseStart_661989 : Nat := 118140960795 + 661989 * 2 ^ 59
def prefixEnd_661989 : Nat := 4983230072969 + 3 ^ 40 * 661989 * 2
def baseEnd_661989 : Nat := 226612363326210465795383

theorem tailTrace_661989 : CollatzResearch.WordTrace tailWord_661989 prefixEnd_661989 226612363326210465795383 := by
  unfold tailWord_661989
  simp only [CollatzResearch.WordTrace]
  refine ⟨24144722398734386565245021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16096481599156257710163347 24144722398734386565245021)
  ·
    refine ⟨9054270899525394961966883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24144722398734386565245021 9054270899525394961966883)
    ·
      refine ⟨13581406349288092442950325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9054270899525394961966883 13581406349288092442950325)
      ·
        refine ⟨1273256845245758666526593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13581406349288092442950325 1273256845245758666526593)
        ·
          refine ⟨954942633934318999894945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1273256845245758666526593 954942633934318999894945)
          ·
            refine ⟨716206975450739249921209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954942633934318999894945 716206975450739249921209)
            ·
              refine ⟨537155231588054437440907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716206975450739249921209 537155231588054437440907)
              ·
                refine ⟨805732847382081656161361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537155231588054437440907 805732847382081656161361)
                ·
                  refine ⟨604299635536561242121021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 805732847382081656161361 604299635536561242121021)
                  ·
                    refine ⟨226612363326210465795383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 604299635536561242121021 226612363326210465795383)
                    ·
                      rfl

theorem cell22_661989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_661989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_661989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_661989 prefixEnd_661989 := by exact prefixLift 661989
  have htrace : WordTrace (prefixWord ++ tailWord_661989) baseStart_661989 baseEnd_661989 := by
    simpa [prefixWord, tailWord_661989, baseEnd_661989] using wordTrace_append hprefix tailTrace_661989
  have hstable : (prefixWord ++ tailWord_661989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661989).length < 2 ^ (prefixWord ++ tailWord_661989).sum := by decide
  have hdescent : baseEnd_661989 < baseStart_661989 := by decide
  rcases family_descends (prefixWord ++ tailWord_661989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662030 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_662030 : Nat := 118140960795 + 662030 * 2 ^ 59
def prefixEnd_662030 : Nat := 4983230072969 + 3 ^ 40 * 662030 * 2
def baseEnd_662030 : Nat := 75542132821366675173419

theorem tailTrace_662030 : CollatzResearch.WordTrace tailWord_662030 prefixEnd_662030 75542132821366675173419 := by
  unfold tailWord_662030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018277223948231320935943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16097478527723900378325029 3018277223948231320935943)
  ·
    refine ⟨4527415835922346981403915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3018277223948231320935943 4527415835922346981403915)
    ·
      refine ⟨6791123753883520472105873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4527415835922346981403915 6791123753883520472105873)
      ·
        refine ⟨5093342815412640354079405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6791123753883520472105873 5093342815412640354079405)
        ·
          refine ⟨1910003555779740132779777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5093342815412640354079405 1910003555779740132779777)
          ·
            refine ⟨1432502666834805099584833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1910003555779740132779777 1432502666834805099584833)
            ·
              refine ⟨1074377000126103824688625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432502666834805099584833 1074377000126103824688625)
              ·
                refine ⟨805782750094577868516469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074377000126103824688625 805782750094577868516469)
                ·
                  refine ⟨75542132821366675173419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 805782750094577868516469 75542132821366675173419)
                  ·
                    rfl

theorem cell22_662030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_662030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662030 prefixEnd_662030 := by exact prefixLift 662030
  have htrace : WordTrace (prefixWord ++ tailWord_662030) baseStart_662030 baseEnd_662030 := by
    simpa [prefixWord, tailWord_662030, baseEnd_662030] using wordTrace_append hprefix tailTrace_662030
  have hstable : (prefixWord ++ tailWord_662030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662030).length < 2 ^ (prefixWord ++ tailWord_662030).sum := by decide
  have hdescent : baseEnd_662030 < baseStart_662030 := by decide
  rcases family_descends (prefixWord ++ tailWord_662030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662058 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_662058 : Nat := 118140960795 + 662058 * 2 ^ 59
def prefixEnd_662058 : Nat := 4983230072969 + 3 ^ 40 * 662058 * 2
def baseEnd_662058 : Nat := 75545327812105761940057

theorem tailTrace_662058 : CollatzResearch.WordTrace tailWord_662058 prefixEnd_662058 75545327812105761940057 := by
  unfold tailWord_662058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6036809758871102837376707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16098159356989607566337885 6036809758871102837376707)
  ·
    refine ⟨9055214638306654256065061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6036809758871102837376707 9055214638306654256065061)
    ·
      refine ⟨1697852744682497673012199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9055214638306654256065061 1697852744682497673012199)
      ·
        refine ⟨2546779117023746509518299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1697852744682497673012199 2546779117023746509518299)
        ·
          refine ⟨3820168675535619764277449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2546779117023746509518299 3820168675535619764277449)
          ·
            refine ⟨2865126506651714823208087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3820168675535619764277449 2865126506651714823208087)
            ·
              refine ⟨4297689759977572234812131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2865126506651714823208087 4297689759977572234812131)
              ·
                refine ⟨6446534639966358352218197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4297689759977572234812131 6446534639966358352218197)
                ·
                  refine ⟨75545327812105761940057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6446534639966358352218197 75545327812105761940057)
                  ·
                    rfl

theorem cell22_662058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_662058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662058 prefixEnd_662058 := by exact prefixLift 662058
  have htrace : WordTrace (prefixWord ++ tailWord_662058) baseStart_662058 baseEnd_662058 := by
    simpa [prefixWord, tailWord_662058, baseEnd_662058] using wordTrace_append hprefix tailTrace_662058
  have hstable : (prefixWord ++ tailWord_662058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662058).length < 2 ^ (prefixWord ++ tailWord_662058).sum := by decide
  have hdescent : baseEnd_662058 < baseStart_662058 := by decide
  rcases family_descends (prefixWord ++ tailWord_662058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662073 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_662073 : Nat := 118140960795 + 662073 * 2 ^ 59
def prefixEnd_662073 : Nat := 4983230072969 + 3 ^ 40 * 662073 * 2
def baseEnd_662073 : Nat := 226641118242862246695125

theorem tailTrace_662073 : CollatzResearch.WordTrace tailWord_662073 prefixEnd_662073 226641118242862246695125 := by
  unfold tailWord_662073
  simp only [CollatzResearch.WordTrace]
  refine ⟨24147786130430068911302873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16098524086953379274201915 24147786130430068911302873)
  ·
    refine ⟨18110839597822551683477155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24147786130430068911302873 18110839597822551683477155)
    ·
      refine ⟨27166259396733827525215733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18110839597822551683477155 27166259396733827525215733)
      ·
        refine ⟨2546836818443796330488975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27166259396733827525215733 2546836818443796330488975)
        ·
          refine ⟨3820255227665694495733463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2546836818443796330488975 3820255227665694495733463)
          ·
            refine ⟨5730382841498541743600195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820255227665694495733463 5730382841498541743600195)
            ·
              refine ⟨8595574262247812615400293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5730382841498541743600195 8595574262247812615400293)
              ·
                refine ⟨1611670174171464865387555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8595574262247812615400293 1611670174171464865387555)
                ·
                  refine ⟨2417505261257197298081333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611670174171464865387555 2417505261257197298081333)
                  ·
                    refine ⟨226641118242862246695125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2417505261257197298081333 226641118242862246695125)
                    ·
                      rfl

theorem cell22_662073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_662073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662073 prefixEnd_662073 := by exact prefixLift 662073
  have htrace : WordTrace (prefixWord ++ tailWord_662073) baseStart_662073 baseEnd_662073 := by
    simpa [prefixWord, tailWord_662073, baseEnd_662073] using wordTrace_append hprefix tailTrace_662073
  have hstable : (prefixWord ++ tailWord_662073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662073).length < 2 ^ (prefixWord ++ tailWord_662073).sum := by decide
  have hdescent : baseEnd_662073 < baseStart_662073 := by decide
  rcases family_descends (prefixWord ++ tailWord_662073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662077 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_662077 : Nat := 118140960795 + 662077 * 2 ^ 59
def prefixEnd_662077 : Nat := 4983230072969 + 3 ^ 40 * 662077 * 2
def baseEnd_662077 : Nat := 226642487524607569595113

theorem tailTrace_662077 : CollatzResearch.WordTrace tailWord_662077 prefixEnd_662077 226642487524607569595113 := by
  unfold tailWord_662077
  simp only [CollatzResearch.WordTrace]
  refine ⟨24147932022415577594448485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16098621348277051729632323 24147932022415577594448485)
  ·
    refine ⟨4527737254202920798959091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24147932022415577594448485 4527737254202920798959091)
    ·
      refine ⟨6791605881304381198438637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4527737254202920798959091 6791605881304381198438637)
      ·
        refine ⟨2546852205489142949414489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6791605881304381198438637 2546852205489142949414489)
        ·
          refine ⟨1910139154116857212060867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2546852205489142949414489 1910139154116857212060867)
          ·
            refine ⟨2865208731175285818091301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910139154116857212060867 2865208731175285818091301)
            ·
              refine ⟨537226637095366090892119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2865208731175285818091301 537226637095366090892119)
              ·
                refine ⟨805839955643049136338179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537226637095366090892119 805839955643049136338179)
                ·
                  refine ⟨1208759933464573704507269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805839955643049136338179 1208759933464573704507269)
                  ·
                    refine ⟨226642487524607569595113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1208759933464573704507269 226642487524607569595113)
                    ·
                      rfl

theorem cell22_662077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_662077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662077 prefixEnd_662077 := by exact prefixLift 662077
  have htrace : WordTrace (prefixWord ++ tailWord_662077) baseStart_662077 baseEnd_662077 := by
    simpa [prefixWord, tailWord_662077, baseEnd_662077] using wordTrace_append hprefix tailTrace_662077
  have hstable : (prefixWord ++ tailWord_662077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662077).length < 2 ^ (prefixWord ++ tailWord_662077).sum := by decide
  have hdescent : baseEnd_662077 < baseStart_662077 := by decide
  rcases family_descends (prefixWord ++ tailWord_662077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662088 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_662088 : Nat := 118140960795 + 662088 * 2 ^ 59
def prefixEnd_662088 : Nat := 4983230072969 + 3 ^ 40 * 662088 * 2
def baseEnd_662088 : Nat := 226646253049407207570079

theorem tailTrace_662088 : CollatzResearch.WordTrace tailWord_662088 prefixEnd_662088 226646253049407207570079 := by
  unfold tailWord_662088
  simp only [CollatzResearch.WordTrace]
  refine ⟨12074166612687863236549459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16098888816917150982065945 12074166612687863236549459)
  ·
    refine ⟨18111249919031794854824189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12074166612687863236549459 18111249919031794854824189)
    ·
      refine ⟨6791718719636923070559071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18111249919031794854824189 6791718719636923070559071)
      ·
        refine ⟨10187578079455384605838607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6791718719636923070559071 10187578079455384605838607)
        ·
          refine ⟨15281367119183076908757911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10187578079455384605838607 15281367119183076908757911)
          ·
            refine ⟨22922050678774615363136867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15281367119183076908757911 22922050678774615363136867)
            ·
              refine ⟨34383076018161923044705301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22922050678774615363136867 34383076018161923044705301)
              ·
                refine ⟨1611706688351340142720561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34383076018161923044705301 1611706688351340142720561)
                ·
                  refine ⟨1208780016263505107040421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1611706688351340142720561 1208780016263505107040421)
                  ·
                    refine ⟨226646253049407207570079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1208780016263505107040421 226646253049407207570079)
                    ·
                      rfl

theorem cell22_662088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_662088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662088 prefixEnd_662088 := by exact prefixLift 662088
  have htrace : WordTrace (prefixWord ++ tailWord_662088) baseStart_662088 baseEnd_662088 := by
    simpa [prefixWord, tailWord_662088, baseEnd_662088] using wordTrace_append hprefix tailTrace_662088
  have hstable : (prefixWord ++ tailWord_662088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662088).length < 2 ^ (prefixWord ++ tailWord_662088).sum := by decide
  have hdescent : baseEnd_662088 < baseStart_662088 := by decide
  rcases family_descends (prefixWord ++ tailWord_662088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662090 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 4, 3]
def baseStart_662090 : Nat := 118140960795 + 662090 * 2 ^ 59
def prefixEnd_662090 : Nat := 4983230072969 + 3 ^ 40 * 662090 * 2
def baseEnd_662090 : Nat := 226646937690279869020073

theorem tailTrace_662090 : CollatzResearch.WordTrace tailWord_662090 prefixEnd_662090 226646937690279869020073 := by
  unfold tailWord_662090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6037101542842120203667931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16098937447578987209781149 6037101542842120203667931)
  ·
    refine ⟨9055652314263180305501897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6037101542842120203667931 9055652314263180305501897)
    ·
      refine ⟨6791739235697385229126423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9055652314263180305501897 6791739235697385229126423)
      ·
        refine ⟨10187608853546077843689635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6791739235697385229126423 10187608853546077843689635)
        ·
          refine ⟨15281413280319116765534453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10187608853546077843689635 15281413280319116765534453)
          ·
            refine ⟨1432632495029917196768855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15281413280319116765534453 1432632495029917196768855)
            ·
              refine ⟨2148948742544875795153283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432632495029917196768855 2148948742544875795153283)
              ·
                refine ⟨3223423113817313692729925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148948742544875795153283 3223423113817313692729925)
                ·
                  refine ⟨604391833840746317386861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3223423113817313692729925 604391833840746317386861)
                  ·
                    refine ⟨226646937690279869020073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 604391833840746317386861 226646937690279869020073)
                    ·
                      rfl

theorem cell22_662090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_662090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662090 prefixEnd_662090 := by exact prefixLift 662090
  have htrace : WordTrace (prefixWord ++ tailWord_662090) baseStart_662090 baseEnd_662090 := by
    simpa [prefixWord, tailWord_662090, baseEnd_662090] using wordTrace_append hprefix tailTrace_662090
  have hstable : (prefixWord ++ tailWord_662090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662090).length < 2 ^ (prefixWord ++ tailWord_662090).sum := by decide
  have hdescent : baseEnd_662090 < baseStart_662090 := by decide
  rcases family_descends (prefixWord ++ tailWord_662090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662120 : List Nat := [2, 1, 4, 3, 2, 1, 1, 8]
def baseStart_662120 : Nat := 118140960795 + 662120 * 2 ^ 59
def prefixEnd_662120 : Nat := 4983230072969 + 3 ^ 40 * 662120 * 2
def baseEnd_662120 : Nat := 25184134144818865641109

theorem tailTrace_662120 : CollatzResearch.WordTrace tailWord_662120 prefixEnd_662120 25184134144818865641109 := by
  unfold tailWord_662120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12074750180629897969131907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16099666907506530625509209 12074750180629897969131907)
  ·
    refine ⟨18112125270944846953697861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12074750180629897969131907 18112125270944846953697861)
    ·
      refine ⟨3396023488302158803818349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18112125270944846953697861 3396023488302158803818349)
      ·
        refine ⟨1273508808113309551431881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3396023488302158803818349 1273508808113309551431881)
        ·
          refine ⟨955131606084982163573911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1273508808113309551431881 955131606084982163573911)
          ·
            refine ⟨1432697409127473245360867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955131606084982163573911 1432697409127473245360867)
            ·
              refine ⟨2149046113691209868041301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432697409127473245360867 2149046113691209868041301)
              ·
                refine ⟨25184134144818865641109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2149046113691209868041301 25184134144818865641109)
                ·
                  rfl

theorem cell22_662120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 8].length) (baseStart_662120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662120 prefixEnd_662120 := by exact prefixLift 662120
  have htrace : WordTrace (prefixWord ++ tailWord_662120) baseStart_662120 baseEnd_662120 := by
    simpa [prefixWord, tailWord_662120, baseEnd_662120] using wordTrace_append hprefix tailTrace_662120
  have hstable : (prefixWord ++ tailWord_662120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662120).length < 2 ^ (prefixWord ++ tailWord_662120).sum := by decide
  have hdescent : baseEnd_662120 < baseStart_662120 := by decide
  rcases family_descends (prefixWord ++ tailWord_662120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662225 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 1, 5]
def baseStart_662225 : Nat := 118140960795 + 662225 * 2 ^ 59
def prefixEnd_662225 : Nat := 4983230072969 + 3 ^ 40 * 662225 * 2
def baseEnd_662225 : Nat := 226693150949184516894659

theorem tailTrace_662225 : CollatzResearch.WordTrace tailWord_662225 prefixEnd_662225 226693150949184516894659 := by
  unfold tailWord_662225
  simp only [CollatzResearch.WordTrace]
  refine ⟨24153330025879398870836129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16102220017252932580557419 24153330025879398870836129)
  ·
    refine ⟨18114997519409549153127097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24153330025879398870836129 18114997519409549153127097)
    ·
      refine ⟨13586248139557161864845323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18114997519409549153127097 13586248139557161864845323)
      ·
        refine ⟨20379372209335742797267985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13586248139557161864845323 20379372209335742797267985)
        ·
          refine ⟨15284529157001807097950989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20379372209335742797267985 15284529157001807097950989)
          ·
            refine ⟨5731698433875677661731621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15284529157001807097950989 5731698433875677661731621)
            ·
              refine ⟨1074693456351689561574679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5731698433875677661731621 1074693456351689561574679)
              ·
                refine ⟨1612040184527534342362019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074693456351689561574679 1612040184527534342362019)
                ·
                  refine ⟨2418060276791301513543029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612040184527534342362019 2418060276791301513543029)
                  ·
                    refine ⟨226693150949184516894659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2418060276791301513543029 226693150949184516894659)
                    ·
                      rfl

theorem cell22_662225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_662225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662225 prefixEnd_662225 := by exact prefixLift 662225
  have htrace : WordTrace (prefixWord ++ tailWord_662225) baseStart_662225 baseEnd_662225 := by
    simpa [prefixWord, tailWord_662225, baseEnd_662225] using wordTrace_append hprefix tailTrace_662225
  have hstable : (prefixWord ++ tailWord_662225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662225).length < 2 ^ (prefixWord ++ tailWord_662225).sum := by decide
  have hdescent : baseEnd_662225 < baseStart_662225 := by decide
  rcases family_descends (prefixWord ++ tailWord_662225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662261 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 6]
def baseStart_662261 : Nat := 118140960795 + 662261 * 2 ^ 59
def prefixEnd_662261 : Nat := 4983230072969 + 3 ^ 40 * 662261 * 2
def baseEnd_662261 : Nat := 75568491494964140998183

theorem tailTrace_662261 : CollatzResearch.WordTrace tailWord_662261 prefixEnd_662261 75568491494964140998183 := by
  unfold tailWord_662261
  simp only [CollatzResearch.WordTrace]
  refine ⟨24154643053748977019146637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16103095369165984679431091 24154643053748977019146637)
  ·
    refine ⟨9057991145155866382179989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24154643053748977019146637 9057991145155866382179989)
    ·
      refine ⟨424593334929181236664687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9057991145155866382179989 424593334929181236664687)
      ·
        refine ⟨636890002393771854997031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424593334929181236664687 636890002393771854997031)
        ·
          refine ⟨955335003590657782495547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636890002393771854997031 955335003590657782495547)
          ·
            refine ⟨1433002505385986673743321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955335003590657782495547 1433002505385986673743321)
            ·
              refine ⟨1074751879039490005307491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433002505385986673743321 1074751879039490005307491)
              ·
                refine ⟨1612127818559235007961237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074751879039490005307491 1612127818559235007961237)
                ·
                  refine ⟨75568491494964140998183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1612127818559235007961237 75568491494964140998183)
                  ·
                    rfl

theorem cell22_662261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_662261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662261 prefixEnd_662261 := by exact prefixLift 662261
  have htrace : WordTrace (prefixWord ++ tailWord_662261) baseStart_662261 baseEnd_662261 := by
    simpa [prefixWord, tailWord_662261, baseEnd_662261] using wordTrace_append hprefix tailTrace_662261
  have hstable : (prefixWord ++ tailWord_662261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662261).length < 2 ^ (prefixWord ++ tailWord_662261).sum := by decide
  have hdescent : baseEnd_662261 < baseStart_662261 := by decide
  rcases family_descends (prefixWord ++ tailWord_662261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662300 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 7]
def baseStart_662300 : Nat := 118140960795 + 662300 * 2 ^ 59
def prefixEnd_662300 : Nat := 4983230072969 + 3 ^ 40 * 662300 * 2
def baseEnd_662300 : Nat := 75572941660636440423143

theorem tailTrace_662300 : CollatzResearch.WordTrace tailWord_662300 prefixEnd_662300 75572941660636440423143 := by
  unfold tailWord_662300
  simp only [CollatzResearch.WordTrace]
  refine ⟨12078032750303843339908177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16104043667071791119877569 12078032750303843339908177)
  ·
    refine ⟨9058524562727882504931133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12078032750303843339908177 9058524562727882504931133)
    ·
      refine ⟨3396946711022955939349175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9058524562727882504931133 3396946711022955939349175)
      ·
        refine ⟨5095420066534433909023763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3396946711022955939349175 5095420066534433909023763)
        ·
          refine ⟨7643130099801650863535645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5095420066534433909023763 7643130099801650863535645)
          ·
            refine ⟨2866173787425619073825867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7643130099801650863535645 2866173787425619073825867)
            ·
              refine ⟨4299260681138428610738801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866173787425619073825867 4299260681138428610738801)
              ·
                refine ⟨3224445510853821458054101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4299260681138428610738801 3224445510853821458054101)
                ·
                  refine ⟨75572941660636440423143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3224445510853821458054101 75572941660636440423143)
                  ·
                    rfl

theorem cell22_662300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_662300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662300 prefixEnd_662300 := by exact prefixLift 662300
  have htrace : WordTrace (prefixWord ++ tailWord_662300) baseStart_662300 baseEnd_662300 := by
    simpa [prefixWord, tailWord_662300, baseEnd_662300] using wordTrace_append hprefix tailTrace_662300
  have hstable : (prefixWord ++ tailWord_662300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662300).length < 2 ^ (prefixWord ++ tailWord_662300).sum := by decide
  have hdescent : baseEnd_662300 < baseStart_662300 := by decide
  rcases family_descends (prefixWord ++ tailWord_662300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662321 : List Nat := [1, 2, 2, 3, 2, 1, 5, 2, 1, 3]
def baseStart_662321 : Nat := 118140960795 + 662321 * 2 ^ 59
def prefixEnd_662321 : Nat := 4983230072969 + 3 ^ 40 * 662321 * 2
def baseEnd_662321 : Nat := 226726013711072266494365

theorem tailTrace_662321 : CollatzResearch.WordTrace tailWord_662321 prefixEnd_662321 226726013711072266494365 := by
  unfold tailWord_662321
  simp only [CollatzResearch.WordTrace]
  refine ⟨24156831433531607266330817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16104554289021071510887211 24156831433531607266330817)
  ·
    refine ⟨18117623575148705449748113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24156831433531607266330817 18117623575148705449748113)
    ·
      refine ⟨13588217681361529087311085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18117623575148705449748113 13588217681361529087311085)
      ·
        refine ⟨5095581630510573407741657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13588217681361529087311085 5095581630510573407741657)
        ·
          refine ⟨3821686222882930055806243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5095581630510573407741657 3821686222882930055806243)
          ·
            refine ⟨5732529334324395083709365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821686222882930055806243 5732529334324395083709365)
            ·
              refine ⟨537424625092912039097753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5732529334324395083709365 537424625092912039097753)
              ·
                refine ⟨403068468819684029323315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537424625092912039097753 403068468819684029323315)
                ·
                  refine ⟨604602703229526043984973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403068468819684029323315 604602703229526043984973)
                  ·
                    refine ⟨226726013711072266494365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 604602703229526043984973 226726013711072266494365)
                    ·
                      rfl

theorem cell22_662321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_662321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662321 prefixEnd_662321 := by exact prefixLift 662321
  have htrace : WordTrace (prefixWord ++ tailWord_662321) baseStart_662321 baseEnd_662321 := by
    simpa [prefixWord, tailWord_662321, baseEnd_662321] using wordTrace_append hprefix tailTrace_662321
  have hstable : (prefixWord ++ tailWord_662321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662321).length < 2 ^ (prefixWord ++ tailWord_662321).sum := by decide
  have hdescent : baseEnd_662321 < baseStart_662321 := by decide
  rcases family_descends (prefixWord ++ tailWord_662321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662334 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_662334 : Nat := 118140960795 + 662334 * 2 ^ 59
def prefixEnd_662334 : Nat := 4983230072969 + 3 ^ 40 * 662334 * 2
def baseEnd_662334 : Nat := 75576821292248188639775

theorem tailTrace_662334 : CollatzResearch.WordTrace tailWord_662334 prefixEnd_662334 75576821292248188639775 := by
  unfold tailWord_662334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3019663197810563810819257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16104870388323006991036037 3019663197810563810819257)
  ·
    refine ⟨2264747398357922858114443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3019663197810563810819257 2264747398357922858114443)
    ·
      refine ⟨3397121097536884287171665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2264747398357922858114443 3397121097536884287171665)
      ·
        refine ⟨2547840823152663215378749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3397121097536884287171665 2547840823152663215378749)
        ·
          refine ⟨955440308682248705767031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2547840823152663215378749 955440308682248705767031)
          ·
            refine ⟨1433160463023373058650547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955440308682248705767031 1433160463023373058650547)
            ·
              refine ⟨2149740694535059587975821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433160463023373058650547 2149740694535059587975821)
              ·
                refine ⟨806152760450647345490933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2149740694535059587975821 806152760450647345490933)
                ·
                  refine ⟨75576821292248188639775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 806152760450647345490933 75576821292248188639775)
                  ·
                    rfl

theorem cell22_662334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_662334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662334 prefixEnd_662334 := by exact prefixLift 662334
  have htrace : WordTrace (prefixWord ++ tailWord_662334) baseStart_662334 baseEnd_662334 := by
    simpa [prefixWord, tailWord_662334, baseEnd_662334] using wordTrace_append hprefix tailTrace_662334
  have hstable : (prefixWord ++ tailWord_662334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662334).length < 2 ^ (prefixWord ++ tailWord_662334).sum := by decide
  have hdescent : baseEnd_662334 < baseStart_662334 := by decide
  rcases family_descends (prefixWord ++ tailWord_662334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662379 : List Nat := [1, 1, 1, 1, 2, 2, 8, 2, 4]
def baseStart_662379 : Nat := 118140960795 + 662379 * 2 ^ 59
def prefixEnd_662379 : Nat := 4983230072969 + 3 ^ 40 * 662379 * 2
def baseEnd_662379 : Nat := 75581956098793149514729

theorem tailTrace_662379 : CollatzResearch.WordTrace tailWord_662379 prefixEnd_662379 75581956098793149514729 := by
  unfold tailWord_662379
  simp only [CollatzResearch.WordTrace]
  refine ⟨24158946867321483171942191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16105964578214322114628127 24158946867321483171942191)
  ·
    refine ⟨36238420300982224757913287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24158946867321483171942191 36238420300982224757913287)
    ·
      refine ⟨54357630451473337136869931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36238420300982224757913287 54357630451473337136869931)
      ·
        refine ⟨81536445677210005705304897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54357630451473337136869931 81536445677210005705304897)
        ·
          refine ⟨61152334257907504278978673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81536445677210005705304897 61152334257907504278978673)
          ·
            refine ⟨45864250693430628209234005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61152334257907504278978673 45864250693430628209234005)
            ·
              refine ⟨537471687813640174326961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 45864250693430628209234005 537471687813640174326961)
              ·
                refine ⟨403103765860230130745221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537471687813640174326961 403103765860230130745221)
                ·
                  refine ⟨75581956098793149514729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403103765860230130745221 75581956098793149514729)
                  ·
                    rfl

theorem cell22_662379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 4].length) (baseStart_662379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662379 prefixEnd_662379 := by exact prefixLift 662379
  have htrace : WordTrace (prefixWord ++ tailWord_662379) baseStart_662379 baseEnd_662379 := by
    simpa [prefixWord, tailWord_662379, baseEnd_662379] using wordTrace_append hprefix tailTrace_662379
  have hstable : (prefixWord ++ tailWord_662379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662379).length < 2 ^ (prefixWord ++ tailWord_662379).sum := by decide
  have hdescent : baseEnd_662379 < baseStart_662379 := by decide
  rcases family_descends (prefixWord ++ tailWord_662379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662409 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 2, 4]
def baseStart_662409 : Nat := 118140960795 + 662409 * 2 ^ 59
def prefixEnd_662409 : Nat := 4983230072969 + 3 ^ 40 * 662409 * 2
def baseEnd_662409 : Nat := 226756137909469370294095

theorem tailTrace_662409 : CollatzResearch.WordTrace tailWord_662409 prefixEnd_662409 226756137909469370294095 := by
  unfold tailWord_662409
  simp only [CollatzResearch.WordTrace]
  refine ⟨24160041057212798295534281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16106694038141865530356187 24160041057212798295534281)
  ·
    refine ⟨18120030792909598721650711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24160041057212798295534281 18120030792909598721650711)
    ·
      refine ⟨27180046189364398082476067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18120030792909598721650711 27180046189364398082476067)
      ·
        refine ⟨40770069284046597123714101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27180046189364398082476067 40770069284046597123714101)
        ·
          refine ⟨3822193995379368480348197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40770069284046597123714101 3822193995379368480348197)
          ·
            refine ⟨716661374133631590065287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3822193995379368480348197 716661374133631590065287)
            ·
              refine ⟨1074992061200447385097931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716661374133631590065287 1074992061200447385097931)
              ·
                refine ⟨1612488091800671077646897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074992061200447385097931 1612488091800671077646897)
                ·
                  refine ⟨1209366068850503308235173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1612488091800671077646897 1209366068850503308235173)
                  ·
                    refine ⟨226756137909469370294095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209366068850503308235173 226756137909469370294095)
                    ·
                      rfl

theorem cell22_662409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 4].length) (baseStart_662409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662409 prefixEnd_662409 := by exact prefixLift 662409
  have htrace : WordTrace (prefixWord ++ tailWord_662409) baseStart_662409 baseEnd_662409 := by
    simpa [prefixWord, tailWord_662409, baseEnd_662409] using wordTrace_append hprefix tailTrace_662409
  have hstable : (prefixWord ++ tailWord_662409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662409).length < 2 ^ (prefixWord ++ tailWord_662409).sum := by decide
  have hdescent : baseEnd_662409 < baseStart_662409 := by decide
  rcases family_descends (prefixWord ++ tailWord_662409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662428 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 2, 3]
def baseStart_662428 : Nat := 118140960795 + 662428 * 2 ^ 59
def prefixEnd_662428 : Nat := 4983230072969 + 3 ^ 40 * 662428 * 2
def baseEnd_662428 : Nat := 226762641997759654069037

theorem tailTrace_662428 : CollatzResearch.WordTrace tailWord_662428 prefixEnd_662428 226762641997759654069037 := by
  unfold tailWord_662428
  simp only [CollatzResearch.WordTrace]
  refine ⟨12080367022071982270237969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16107156029429309693650625 12080367022071982270237969)
  ·
    refine ⟨9060275266553986702678477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12080367022071982270237969 9060275266553986702678477)
    ·
      refine ⟨3397603224957745013504429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9060275266553986702678477 3397603224957745013504429)
      ·
        refine ⟨1274101209359154380064161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3397603224957745013504429 1274101209359154380064161)
        ·
          refine ⟨955575907019365785048121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274101209359154380064161 955575907019365785048121)
          ·
            refine ⟨716681930264524338786091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 955575907019365785048121 716681930264524338786091)
            ·
              refine ⟨1075022895396786508179137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716681930264524338786091 1075022895396786508179137)
              ·
                refine ⟨806267171547589881134353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075022895396786508179137 806267171547589881134353)
                ·
                  refine ⟨604700378660692410850765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 806267171547589881134353 604700378660692410850765)
                  ·
                    refine ⟨226762641997759654069037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 604700378660692410850765 226762641997759654069037)
                    ·
                      rfl

theorem cell22_662428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_662428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662428 prefixEnd_662428 := by exact prefixLift 662428
  have htrace : WordTrace (prefixWord ++ tailWord_662428) baseStart_662428 baseEnd_662428 := by
    simpa [prefixWord, tailWord_662428, baseEnd_662428] using wordTrace_append hprefix tailTrace_662428
  have hstable : (prefixWord ++ tailWord_662428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662428).length < 2 ^ (prefixWord ++ tailWord_662428).sum := by decide
  have hdescent : baseEnd_662428 < baseStart_662428 := by decide
  rcases family_descends (prefixWord ++ tailWord_662428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662445 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_662445 : Nat := 118140960795 + 662445 * 2 ^ 59
def prefixEnd_662445 : Nat := 4983230072969 + 3 ^ 40 * 662445 * 2
def baseEnd_662445 : Nat := 226768461445177276393985

theorem tailTrace_662445 : CollatzResearch.WordTrace tailWord_662445 prefixEnd_662445 226768461445177276393985 := by
  unfold tailWord_662445
  simp only [CollatzResearch.WordTrace]
  refine ⟨24161354085082376443844789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16107569390054917629229859 24161354085082376443844789)
  ·
    refine ⟨2265126945476472791610449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24161354085082376443844789 2265126945476472791610449)
    ·
      refine ⟨1698845209107354593707837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2265126945476472791610449 1698845209107354593707837)
      ·
        refine ⟨637066953415257972640439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1698845209107354593707837 637066953415257972640439)
        ·
          refine ⟨955600430122886958960659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637066953415257972640439 955600430122886958960659)
          ·
            refine ⟨1433400645184330438440989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955600430122886958960659 1433400645184330438440989)
            ·
              refine ⟨537525241944123914415371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1433400645184330438440989 537525241944123914415371)
              ·
                refine ⟨806287862916185871623057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537525241944123914415371 806287862916185871623057)
                ·
                  refine ⟨604715897187139403717293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 806287862916185871623057 604715897187139403717293)
                  ·
                    refine ⟨226768461445177276393985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 604715897187139403717293 226768461445177276393985)
                    ·
                      rfl

theorem cell22_662445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_662445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662445 prefixEnd_662445 := by exact prefixLift 662445
  have htrace : WordTrace (prefixWord ++ tailWord_662445) baseStart_662445 baseEnd_662445 := by
    simpa [prefixWord, tailWord_662445, baseEnd_662445] using wordTrace_append hprefix tailTrace_662445
  have hstable : (prefixWord ++ tailWord_662445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662445).length < 2 ^ (prefixWord ++ tailWord_662445).sum := by decide
  have hdescent : baseEnd_662445 < baseStart_662445 := by decide
  rcases family_descends (prefixWord ++ tailWord_662445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662512 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_662512 : Nat := 118140960795 + 662512 * 2 ^ 59
def prefixEnd_662512 : Nat := 4983230072969 + 3 ^ 40 * 662512 * 2
def baseEnd_662512 : Nat := 226791396914411434968779

theorem tailTrace_662512 : CollatzResearch.WordTrace tailWord_662512 prefixEnd_662512 226791396914411434968779 := by
  unfold tailWord_662512
  simp only [CollatzResearch.WordTrace]
  refine ⟨12081898887919823443266895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16109198517226431257689193 12081898887919823443266895)
  ·
    refine ⟨18122848331879735164900343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12081898887919823443266895 18122848331879735164900343)
    ·
      refine ⟨27184272497819602747350515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18122848331879735164900343 27184272497819602747350515)
      ·
        refine ⟨40776408746729404121025773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27184272497819602747350515 40776408746729404121025773)
        ·
          refine ⟨15291153280023526545384665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40776408746729404121025773 15291153280023526545384665)
          ·
            refine ⟨11468364960017644909038499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15291153280023526545384665 11468364960017644909038499)
            ·
              refine ⟨17202547440026467363557749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11468364960017644909038499 17202547440026467363557749)
              ·
                refine ⟨1612738822502481315333539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17202547440026467363557749 1612738822502481315333539)
                ·
                  refine ⟨2419108233753721973000309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612738822502481315333539 2419108233753721973000309)
                  ·
                    refine ⟨226791396914411434968779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2419108233753721973000309 226791396914411434968779)
                    ·
                      rfl

theorem cell22_662512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_662512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662512 prefixEnd_662512 := by exact prefixLift 662512
  have htrace : WordTrace (prefixWord ++ tailWord_662512) baseStart_662512 baseEnd_662512 := by
    simpa [prefixWord, tailWord_662512, baseEnd_662512] using wordTrace_append hprefix tailTrace_662512
  have hstable : (prefixWord ++ tailWord_662512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662512).length < 2 ^ (prefixWord ++ tailWord_662512).sum := by decide
  have hdescent : baseEnd_662512 < baseStart_662512 := by decide
  rcases family_descends (prefixWord ++ tailWord_662512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662529 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_662529 : Nat := 118140960795 + 662529 * 2 ^ 59
def prefixEnd_662529 : Nat := 4983230072969 + 3 ^ 40 * 662529 * 2
def baseEnd_662529 : Nat := 226797216361829057293727

theorem tailTrace_662529 : CollatzResearch.WordTrace tailWord_662529 prefixEnd_662529 226797216361829057293727 := by
  unfold tailWord_662529
  simp only [CollatzResearch.WordTrace]
  refine ⟨24164417816778058789902641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16109611877852039193268427 24164417816778058789902641)
  ·
    refine ⟨18123313362583544092426981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24164417816778058789902641 18123313362583544092426981)
    ·
      refine ⟨3398121255484414517330059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18123313362583544092426981 3398121255484414517330059)
      ·
        refine ⟨5097181883226621775995089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3398121255484414517330059 5097181883226621775995089)
        ·
          refine ⟨3822886412419966331996317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5097181883226621775995089 3822886412419966331996317)
          ·
            refine ⟨1433582404657487374498619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3822886412419966331996317 1433582404657487374498619)
            ·
              refine ⟨2150373606986231061747929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433582404657487374498619 2150373606986231061747929)
              ·
                refine ⟨1612780205239673296310947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150373606986231061747929 1612780205239673296310947)
                ·
                  refine ⟨2419170307859509944466421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612780205239673296310947 2419170307859509944466421)
                  ·
                    refine ⟨226797216361829057293727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2419170307859509944466421 226797216361829057293727)
                    ·
                      rfl

theorem cell22_662529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_662529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662529 prefixEnd_662529 := by exact prefixLift 662529
  have htrace : WordTrace (prefixWord ++ tailWord_662529) baseStart_662529 baseEnd_662529 := by
    simpa [prefixWord, tailWord_662529, baseEnd_662529] using wordTrace_append hprefix tailTrace_662529
  have hstable : (prefixWord ++ tailWord_662529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662529).length < 2 ^ (prefixWord ++ tailWord_662529).sum := by decide
  have hdescent : baseEnd_662529 < baseStart_662529 := by decide
  rcases family_descends (prefixWord ++ tailWord_662529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662542 : List Nat := [4, 1, 1, 2, 2, 12]
def baseStart_662542 : Nat := 118140960795 + 662542 * 2 ^ 59
def prefixEnd_662542 : Nat := 4983230072969 + 3 ^ 40 * 662542 * 2
def baseEnd_662542 : Nat := 2800020574413596996527

theorem tailTrace_662542 : CollatzResearch.WordTrace tailWord_662542 prefixEnd_662542 2800020574413596996527 := by
  unfold tailWord_662542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3020611495716370251265735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16109927977153974673417253 3020611495716370251265735)
  ·
    refine ⟨4530917243574555376898603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3020611495716370251265735 4530917243574555376898603)
    ·
      refine ⟨6796375865361833065347905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4530917243574555376898603 6796375865361833065347905)
      ·
        refine ⟨5097281899021374799010929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6796375865361833065347905 5097281899021374799010929)
        ·
          refine ⟨3822961424266031099258197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5097281899021374799010929 3822961424266031099258197)
          ·
            refine ⟨2800020574413596996527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3822961424266031099258197 2800020574413596996527)
            ·
              rfl

theorem cell22_662542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 12].length) (baseStart_662542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662542 prefixEnd_662542 := by exact prefixLift 662542
  have htrace : WordTrace (prefixWord ++ tailWord_662542) baseStart_662542 baseEnd_662542 := by
    simpa [prefixWord, tailWord_662542, baseEnd_662542] using wordTrace_append hprefix tailTrace_662542
  have hstable : (prefixWord ++ tailWord_662542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662542).length < 2 ^ (prefixWord ++ tailWord_662542).sum := by decide
  have hdescent : baseEnd_662542 < baseStart_662542 := by decide
  rcases family_descends (prefixWord ++ tailWord_662542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662559 : List Nat := [1, 1, 2, 4, 1, 5, 1, 7]
def baseStart_662559 : Nat := 118140960795 + 662559 * 2 ^ 59
def prefixEnd_662559 : Nat := 4983230072969 + 3 ^ 40 * 662559 * 2
def baseEnd_662559 : Nat := 25200831774990997671515

theorem tailTrace_662559 : CollatzResearch.WordTrace tailWord_662559 prefixEnd_662559 25200831774990997671515 := by
  unfold tailWord_662559
  simp only [CollatzResearch.WordTrace]
  refine ⟨24165512006669373913494731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16110341337779582608996487 24165512006669373913494731)
  ·
    refine ⟨36248268010004060870242097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24165512006669373913494731 36248268010004060870242097)
    ·
      refine ⟨27186201007503045652681573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36248268010004060870242097 27186201007503045652681573)
      ·
        refine ⟨5097412688906821059877795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27186201007503045652681573 5097412688906821059877795)
        ·
          refine ⟨7646119033360231589816693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5097412688906821059877795 7646119033360231589816693)
          ·
            refine ⟨716823659377521711545315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7646119033360231589816693 716823659377521711545315)
            ·
              refine ⟨1075235489066282567317973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716823659377521711545315 1075235489066282567317973)
              ·
                refine ⟨25200831774990997671515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1075235489066282567317973 25200831774990997671515)
                ·
                  rfl

theorem cell22_662559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 7].length) (baseStart_662559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662559 prefixEnd_662559 := by exact prefixLift 662559
  have htrace : WordTrace (prefixWord ++ tailWord_662559) baseStart_662559 baseEnd_662559 := by
    simpa [prefixWord, tailWord_662559, baseEnd_662559] using wordTrace_append hprefix tailTrace_662559
  have hstable : (prefixWord ++ tailWord_662559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662559).length < 2 ^ (prefixWord ++ tailWord_662559).sum := by decide
  have hdescent : baseEnd_662559 < baseStart_662559 := by decide
  rcases family_descends (prefixWord ++ tailWord_662559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662572 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_662572 : Nat := 118140960795 + 662572 * 2 ^ 59
def prefixEnd_662572 : Nat := 4983230072969 + 3 ^ 40 * 662572 * 2
def baseEnd_662572 : Nat := 226811936140591278468595

theorem tailTrace_662572 : CollatzResearch.WordTrace tailWord_662572 prefixEnd_662572 226811936140591278468595 := by
  unfold tailWord_662572
  simp only [CollatzResearch.WordTrace]
  refine ⟨12082993077811138566858985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16110657437081518089145313 12082993077811138566858985)
  ·
    refine ⟨9062244808358353925144239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12082993077811138566858985 9062244808358353925144239)
    ·
      refine ⟨13593367212537530887716359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9062244808358353925144239 13593367212537530887716359)
      ·
        refine ⟨20390050818806296331574539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13593367212537530887716359 20390050818806296331574539)
        ·
          refine ⟨30585076228209444497361809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20390050818806296331574539 30585076228209444497361809)
          ·
            refine ⟨22938807171157083373021357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30585076228209444497361809 22938807171157083373021357)
            ·
              refine ⟨8602052689183906264883009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22938807171157083373021357 8602052689183906264883009)
              ·
                refine ⟨6451539516887929698662257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8602052689183906264883009 6451539516887929698662257)
                ·
                  refine ⟨4838654637665947273996693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6451539516887929698662257 4838654637665947273996693)
                  ·
                    refine ⟨226811936140591278468595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4838654637665947273996693 226811936140591278468595)
                    ·
                      rfl

theorem cell22_662572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_662572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662572 prefixEnd_662572 := by exact prefixLift 662572
  have htrace : WordTrace (prefixWord ++ tailWord_662572) baseStart_662572 baseEnd_662572 := by
    simpa [prefixWord, tailWord_662572, baseEnd_662572] using wordTrace_append hprefix tailTrace_662572
  have hstable : (prefixWord ++ tailWord_662572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662572).length < 2 ^ (prefixWord ++ tailWord_662572).sum := by decide
  have hdescent : baseEnd_662572 < baseStart_662572 := by decide
  rcases family_descends (prefixWord ++ tailWord_662572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662617 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_662617 : Nat := 118140960795 + 662617 * 2 ^ 59
def prefixEnd_662617 : Nat := 4983230072969 + 3 ^ 40 * 662617 * 2
def baseEnd_662617 : Nat := 226827340560226161093457

theorem tailTrace_662617 : CollatzResearch.WordTrace tailWord_662617 prefixEnd_662617 226827340560226161093457 := by
  unfold tailWord_662617
  simp only [CollatzResearch.WordTrace]
  refine ⟨24167627440459249819106105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16111751626972833212737403 24167627440459249819106105)
  ·
    refine ⟨18125720580344437364329579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24167627440459249819106105 18125720580344437364329579)
    ·
      refine ⟨27188580870516656046494369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18125720580344437364329579 27188580870516656046494369)
      ·
        refine ⟨20391435652887492034870777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27188580870516656046494369 20391435652887492034870777)
        ·
          refine ⟨15293576739665619026153083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20391435652887492034870777 15293576739665619026153083)
          ·
            refine ⟨22940365109498428539229625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15293576739665619026153083 22940365109498428539229625)
            ·
              refine ⟨17205273832123821404422219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22940365109498428539229625 17205273832123821404422219)
              ·
                refine ⟨25807910748185732106633329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17205273832123821404422219 25807910748185732106633329)
                ·
                  refine ⟨19355933061139299079974997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25807910748185732106633329 19355933061139299079974997)
                  ·
                    refine ⟨226827340560226161093457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19355933061139299079974997 226827340560226161093457)
                    ·
                      rfl

theorem cell22_662617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_662617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662617 prefixEnd_662617 := by exact prefixLift 662617
  have htrace : WordTrace (prefixWord ++ tailWord_662617) baseStart_662617 baseEnd_662617 := by
    simpa [prefixWord, tailWord_662617, baseEnd_662617] using wordTrace_append hprefix tailTrace_662617
  have hstable : (prefixWord ++ tailWord_662617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662617).length < 2 ^ (prefixWord ++ tailWord_662617).sum := by decide
  have hdescent : baseEnd_662617 < baseStart_662617 := by decide
  rcases family_descends (prefixWord ++ tailWord_662617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662698 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_662698 : Nat := 118140960795 + 662698 * 2 ^ 59
def prefixEnd_662698 : Nat := 4983230072969 + 3 ^ 40 * 662698 * 2
def baseEnd_662698 : Nat := 226855068515568949818209

theorem tailTrace_662698 : CollatzResearch.WordTrace tailWord_662698 prefixEnd_662698 226855068515568949818209 := by
  unfold tailWord_662698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6042645438291450163201187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16113721168777200435203165 6042645438291450163201187)
  ·
    refine ⟨9063968157437175244801781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6042645438291450163201187 9063968157437175244801781)
    ·
      refine ⟨849747014759735179200167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9063968157437175244801781 849747014759735179200167)
      ·
        refine ⟨1274620522139602768800251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849747014759735179200167 1274620522139602768800251)
        ·
          refine ⟨1911930783209404153200377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274620522139602768800251 1911930783209404153200377)
          ·
            refine ⟨1433948087407053114900283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911930783209404153200377 1433948087407053114900283)
            ·
              refine ⟨2150922131110579672350425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433948087407053114900283 2150922131110579672350425)
              ·
                refine ⟨1613191598332934754262819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150922131110579672350425 1613191598332934754262819)
                ·
                  refine ⟨2419787397499402131394229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613191598332934754262819 2419787397499402131394229)
                  ·
                    refine ⟨226855068515568949818209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2419787397499402131394229 226855068515568949818209)
                    ·
                      rfl

theorem cell22_662698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_662698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662698 prefixEnd_662698 := by exact prefixLift 662698
  have htrace : WordTrace (prefixWord ++ tailWord_662698) baseStart_662698 baseEnd_662698 := by
    simpa [prefixWord, tailWord_662698, baseEnd_662698] using wordTrace_append hprefix tailTrace_662698
  have hstable : (prefixWord ++ tailWord_662698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662698).length < 2 ^ (prefixWord ++ tailWord_662698).sum := by decide
  have hdescent : baseEnd_662698 < baseStart_662698 := by decide
  rcases family_descends (prefixWord ++ tailWord_662698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662760 : List Nat := [2, 1, 4, 1, 2, 1, 4, 3, 1, 3]
def baseStart_662760 : Nat := 118140960795 + 662760 * 2 ^ 59
def prefixEnd_662760 : Nat := 4983230072969 + 3 ^ 40 * 662760 * 2
def baseEnd_662760 : Nat := 226876292382621454768019

theorem tailTrace_662760 : CollatzResearch.WordTrace tailWord_662760 prefixEnd_662760 226876292382621454768019 := by
  unfold tailWord_662760
  simp only [CollatzResearch.WordTrace]
  refine ⟨12086421539470592620780867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16115228719294123494374489 12086421539470592620780867)
  ·
    refine ⟨18129632309205888931171301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12086421539470592620780867 18129632309205888931171301)
    ·
      refine ⟨3399306057976104174594619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18129632309205888931171301 3399306057976104174594619)
      ·
        refine ⟨5098959086964156261891929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399306057976104174594619 5098959086964156261891929)
        ·
          refine ⟨3824219315223117196418947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5098959086964156261891929 3824219315223117196418947)
          ·
            refine ⟨5736328972834675794628421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3824219315223117196418947 5736328972834675794628421)
            ·
              refine ⟨1075561682406501711492829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5736328972834675794628421 1075561682406501711492829)
              ·
                refine ⟨403335630902438141809811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1075561682406501711492829 403335630902438141809811)
                ·
                  refine ⟨605003446353657212714717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403335630902438141809811 605003446353657212714717)
                  ·
                    refine ⟨226876292382621454768019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 605003446353657212714717 226876292382621454768019)
                    ·
                      rfl

theorem cell22_662760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_662760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662760 prefixEnd_662760 := by exact prefixLift 662760
  have htrace : WordTrace (prefixWord ++ tailWord_662760) baseStart_662760 baseEnd_662760 := by
    simpa [prefixWord, tailWord_662760, baseEnd_662760] using wordTrace_append hprefix tailTrace_662760
  have hstable : (prefixWord ++ tailWord_662760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662760).length < 2 ^ (prefixWord ++ tailWord_662760).sum := by decide
  have hdescent : baseEnd_662760 < baseStart_662760 := by decide
  rcases family_descends (prefixWord ++ tailWord_662760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662833 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 4, 3]
def baseStart_662833 : Nat := 118140960795 + 662833 * 2 ^ 59
def prefixEnd_662833 : Nat := 4983230072969 + 3 ^ 40 * 662833 * 2
def baseEnd_662833 : Nat := 226901281774473597692795

theorem tailTrace_662833 : CollatzResearch.WordTrace tailWord_662833 prefixEnd_662833 226901281774473597692795 := by
  unfold tailWord_662833
  simp only [CollatzResearch.WordTrace]
  refine ⟨24175505607676718708969153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16117003738451145805979435 24175505607676718708969153)
  ·
    refine ⟨18131629205757539031726865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24175505607676718708969153 18131629205757539031726865)
    ·
      refine ⟨13598721904318154273795149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18131629205757539031726865 13598721904318154273795149)
      ·
        refine ⟨5099520714119307852673181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13598721904318154273795149 5099520714119307852673181)
        ·
          refine ⟨1912320267794740444752443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5099520714119307852673181 1912320267794740444752443)
          ·
            refine ⟨2868480401692110667128665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912320267794740444752443 2868480401692110667128665)
            ·
              refine ⟨2151360301269083000346499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2868480401692110667128665 2151360301269083000346499)
              ·
                refine ⟨3227040451903624500519749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151360301269083000346499 3227040451903624500519749)
                ·
                  refine ⟨605070084731929593847453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3227040451903624500519749 605070084731929593847453)
                  ·
                    refine ⟨226901281774473597692795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 605070084731929593847453 226901281774473597692795)
                    ·
                      rfl

theorem cell22_662833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_662833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662833 prefixEnd_662833 := by exact prefixLift 662833
  have htrace : WordTrace (prefixWord ++ tailWord_662833) baseStart_662833 baseEnd_662833 := by
    simpa [prefixWord, tailWord_662833, baseEnd_662833] using wordTrace_append hprefix tailTrace_662833
  have hstable : (prefixWord ++ tailWord_662833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662833).length < 2 ^ (prefixWord ++ tailWord_662833).sum := by decide
  have hdescent : baseEnd_662833 < baseStart_662833 := by decide
  rcases family_descends (prefixWord ++ tailWord_662833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662835 : List Nat := [1, 1, 1, 2, 5, 3, 3, 2, 4]
def baseStart_662835 : Nat := 118140960795 + 662835 * 2 ^ 59
def prefixEnd_662835 : Nat := 4983230072969 + 3 ^ 40 * 662835 * 2
def baseEnd_662835 : Nat := 75633988805115419714263

theorem tailTrace_662835 : CollatzResearch.WordTrace tailWord_662835 prefixEnd_662835 75633988805115419714263 := by
  unfold tailWord_662835
  simp only [CollatzResearch.WordTrace]
  refine ⟨24175578553669473050541959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16117052369112982033694639 24175578553669473050541959)
  ·
    refine ⟨36263367830504209575812939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24175578553669473050541959 36263367830504209575812939)
    ·
      refine ⟨54395051745756314363719409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36263367830504209575812939 54395051745756314363719409)
      ·
        refine ⟨40796288809317235772789557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54395051745756314363719409 40796288809317235772789557)
        ·
          refine ⟨3824652075873490853699021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40796288809317235772789557 3824652075873490853699021)
          ·
            refine ⟨1434244528452559070137133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3824652075873490853699021 1434244528452559070137133)
            ·
              refine ⟨537841698169709651301425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1434244528452559070137133 537841698169709651301425)
              ·
                refine ⟨403381273627282238476069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537841698169709651301425 403381273627282238476069)
                ·
                  refine ⟨75633988805115419714263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403381273627282238476069 75633988805115419714263)
                  ·
                    rfl

theorem cell22_662835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 4].length) (baseStart_662835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662835 prefixEnd_662835 := by exact prefixLift 662835
  have htrace : WordTrace (prefixWord ++ tailWord_662835) baseStart_662835 baseEnd_662835 := by
    simpa [prefixWord, tailWord_662835, baseEnd_662835] using wordTrace_append hprefix tailTrace_662835
  have hstable : (prefixWord ++ tailWord_662835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662835).length < 2 ^ (prefixWord ++ tailWord_662835).sum := by decide
  have hdescent : baseEnd_662835 < baseStart_662835 := by decide
  rcases family_descends (prefixWord ++ tailWord_662835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662895 : List Nat := [1, 1, 2, 1, 3, 1, 5, 4, 1, 3]
def baseStart_662895 : Nat := 118140960795 + 662895 * 2 ^ 59
def prefixEnd_662895 : Nat := 4983230072969 + 3 ^ 40 * 662895 * 2
def baseEnd_662895 : Nat := 226922505641526102642605

theorem tailTrace_662895 : CollatzResearch.WordTrace tailWord_662895 prefixEnd_662895 226922505641526102642605 := by
  unfold tailWord_662895
  simp only [CollatzResearch.WordTrace]
  refine ⟨24177766933452103297726139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16118511288968068865150759 24177766933452103297726139)
  ·
    refine ⟨36266650400178154946589209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24177766933452103297726139 36266650400178154946589209)
    ·
      refine ⟨27199987800133616209941907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36266650400178154946589209 27199987800133616209941907)
      ·
        refine ⟨40799981700200424314912861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27199987800133616209941907 40799981700200424314912861)
        ·
          refine ⟨15299993137575159118092323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40799981700200424314912861 15299993137575159118092323)
          ·
            refine ⟨22949989706362738677138485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15299993137575159118092323 22949989706362738677138485)
            ·
              refine ⟨2151561534971506750981733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22949989706362738677138485 2151561534971506750981733)
              ·
                refine ⟨403417787807157515809075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2151561534971506750981733 403417787807157515809075)
                ·
                  refine ⟨605126681710736273713613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403417787807157515809075 605126681710736273713613)
                  ·
                    refine ⟨226922505641526102642605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 605126681710736273713613 226922505641526102642605)
                    ·
                      rfl

theorem cell22_662895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 1, 3].length) (baseStart_662895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662895 prefixEnd_662895 := by exact prefixLift 662895
  have htrace : WordTrace (prefixWord ++ tailWord_662895) baseStart_662895 baseEnd_662895 := by
    simpa [prefixWord, tailWord_662895, baseEnd_662895] using wordTrace_append hprefix tailTrace_662895
  have hstable : (prefixWord ++ tailWord_662895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662895).length < 2 ^ (prefixWord ++ tailWord_662895).sum := by decide
  have hdescent : baseEnd_662895 < baseStart_662895 := by decide
  rcases family_descends (prefixWord ++ tailWord_662895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662906 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_662906 : Nat := 118140960795 + 662906 * 2 ^ 59
def prefixEnd_662906 : Nat := 4983230072969 + 3 ^ 40 * 662906 * 2
def baseEnd_662906 : Nat := 226926271166325740617571

theorem tailTrace_662906 : CollatzResearch.WordTrace tailWord_662906 prefixEnd_662906 226926271166325740617571 := by
  unfold tailWord_662906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6044542034103063044094143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16118778757608168117584381 6044542034103063044094143)
  ·
    refine ⟨9066813051154594566141215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6044542034103063044094143 9066813051154594566141215)
    ·
      refine ⟨13600219576731891849211823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9066813051154594566141215 13600219576731891849211823)
      ·
        refine ⟨20400329365097837773817735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13600219576731891849211823 20400329365097837773817735)
        ·
          refine ⟨30600494047646756660726603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20400329365097837773817735 30600494047646756660726603)
          ·
            refine ⟨45900741071470134991089905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30600494047646756660726603 45900741071470134991089905)
            ·
              refine ⟨34425555803602601243317429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45900741071470134991089905 34425555803602601243317429)
              ·
                refine ⟨3227395856587743866561009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34425555803602601243317429 3227395856587743866561009)
                ·
                  refine ⟨2420546892440807899920757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3227395856587743866561009 2420546892440807899920757)
                  ·
                    refine ⟨226926271166325740617571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2420546892440807899920757 226926271166325740617571)
                    ·
                      rfl

theorem cell22_662906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_662906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662906 prefixEnd_662906 := by exact prefixLift 662906
  have htrace : WordTrace (prefixWord ++ tailWord_662906) baseStart_662906 baseEnd_662906 := by
    simpa [prefixWord, tailWord_662906, baseEnd_662906] using wordTrace_append hprefix tailTrace_662906
  have hstable : (prefixWord ++ tailWord_662906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662906).length < 2 ^ (prefixWord ++ tailWord_662906).sum := by decide
  have hdescent : baseEnd_662906 < baseStart_662906 := by decide
  rcases family_descends (prefixWord ++ tailWord_662906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662968 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 1, 5]
def baseStart_662968 : Nat := 118140960795 + 662968 * 2 ^ 59
def prefixEnd_662968 : Nat := 4983230072969 + 3 ^ 40 * 662968 * 2
def baseEnd_662968 : Nat := 226947495033378245567381

theorem tailTrace_662968 : CollatzResearch.WordTrace tailWord_662968 prefixEnd_662968 226947495033378245567381 := by
  unfold tailWord_662968
  simp only [CollatzResearch.WordTrace]
  refine ⟨12090214731093818382566779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16120286308125091176755705 12090214731093818382566779)
  ·
    refine ⟨18135322096640727573850169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12090214731093818382566779 18135322096640727573850169)
    ·
      refine ⟨13601491572480545680387627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18135322096640727573850169 13601491572480545680387627)
      ·
        refine ⟨20402237358720818520581441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13601491572480545680387627 20402237358720818520581441)
        ·
          refine ⟨15301678019040613890436081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20402237358720818520581441 15301678019040613890436081)
          ·
            refine ⟨11476258514280460417827061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15301678019040613890436081 11476258514280460417827061)
            ·
              refine ⟨1075899235713793164171287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11476258514280460417827061 1075899235713793164171287)
              ·
                refine ⟨1613848853570689746256931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075899235713793164171287 1613848853570689746256931)
                ·
                  refine ⟨2420773280356034619385397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613848853570689746256931 2420773280356034619385397)
                  ·
                    refine ⟨226947495033378245567381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2420773280356034619385397 226947495033378245567381)
                    ·
                      rfl

theorem cell22_662968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_662968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662968 prefixEnd_662968 := by exact prefixLift 662968
  have htrace : WordTrace (prefixWord ++ tailWord_662968) baseStart_662968 baseEnd_662968 := by
    simpa [prefixWord, tailWord_662968, baseEnd_662968] using wordTrace_append hprefix tailTrace_662968
  have hstable : (prefixWord ++ tailWord_662968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662968).length < 2 ^ (prefixWord ++ tailWord_662968).sum := by decide
  have hdescent : baseEnd_662968 < baseStart_662968 := by decide
  rcases family_descends (prefixWord ++ tailWord_662968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662972 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_662972 : Nat := 118140960795 + 662972 * 2 ^ 59
def prefixEnd_662972 : Nat := 4983230072969 + 3 ^ 40 * 662972 * 2
def baseEnd_662972 : Nat := 226948864315123568467369

theorem tailTrace_662972 : CollatzResearch.WordTrace tailWord_662972 prefixEnd_662972 226948864315123568467369 := by
  unfold tailWord_662972
  simp only [CollatzResearch.WordTrace]
  refine ⟨12090287677086572724139585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16120383569448763632186113 12090287677086572724139585)
  ·
    refine ⟨9067715757814929543104689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12090287677086572724139585 9067715757814929543104689)
    ·
      refine ⟨6800786818361197157328517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9067715757814929543104689 6800786818361197157328517)
      ·
        refine ⟨1275147528442724466999097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6800786818361197157328517 1275147528442724466999097)
        ·
          refine ⟨956360646332043350249323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1275147528442724466999097 956360646332043350249323)
          ·
            refine ⟨1434540969498065025373985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956360646332043350249323 1434540969498065025373985)
            ·
              refine ⟨1075905727123548769030489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434540969498065025373985 1075905727123548769030489)
              ·
                refine ⟨806929295342661576772867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075905727123548769030489 806929295342661576772867)
                ·
                  refine ⟨1210393943013992365159301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806929295342661576772867 1210393943013992365159301)
                  ·
                    refine ⟨226948864315123568467369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1210393943013992365159301 226948864315123568467369)
                    ·
                      rfl

theorem cell22_662972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_662972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662972 prefixEnd_662972 := by exact prefixLift 662972
  have htrace : WordTrace (prefixWord ++ tailWord_662972) baseStart_662972 baseEnd_662972 := by
    simpa [prefixWord, tailWord_662972, baseEnd_662972] using wordTrace_append hprefix tailTrace_662972
  have hstable : (prefixWord ++ tailWord_662972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662972).length < 2 ^ (prefixWord ++ tailWord_662972).sum := by decide
  have hdescent : baseEnd_662972 < baseStart_662972 := by decide
  rcases family_descends (prefixWord ++ tailWord_662972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662983 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 2, 4]
def baseStart_662983 : Nat := 118140960795 + 662983 * 2 ^ 59
def prefixEnd_662983 : Nat := 4983230072969 + 3 ^ 40 * 662983 * 2
def baseEnd_662983 : Nat := 226952629839923206442335

theorem tailTrace_662983 : CollatzResearch.WordTrace tailWord_662983 prefixEnd_662983 226952629839923206442335 := by
  unfold tailWord_662983
  simp only [CollatzResearch.WordTrace]
  refine ⟨24180976557133294326929603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16120651038088862884619735 24180976557133294326929603)
  ·
    refine ⟨36271464835699941490394405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24180976557133294326929603 36271464835699941490394405)
    ·
      refine ⟨6800899656693739029448951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36271464835699941490394405 6800899656693739029448951)
      ·
        refine ⟨10201349485040608544173427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6800899656693739029448951 10201349485040608544173427)
        ·
          refine ⟨15302024227560912816260141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10201349485040608544173427 15302024227560912816260141)
          ·
            refine ⟨5738259085335342306097553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15302024227560912816260141 5738259085335342306097553)
            ·
              refine ⟨4303694314001506729573165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5738259085335342306097553 4303694314001506729573165)
              ·
                refine ⟨1613885367750565023589937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4303694314001506729573165 1613885367750565023589937)
                ·
                  refine ⟨1210414025812923767692453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1613885367750565023589937 1210414025812923767692453)
                  ·
                    refine ⟨226952629839923206442335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1210414025812923767692453 226952629839923206442335)
                    ·
                      rfl

theorem cell22_662983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_662983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_662983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_662983 prefixEnd_662983 := by exact prefixLift 662983
  have htrace : WordTrace (prefixWord ++ tailWord_662983) baseStart_662983 baseEnd_662983 := by
    simpa [prefixWord, tailWord_662983, baseEnd_662983] using wordTrace_append hprefix tailTrace_662983
  have hstable : (prefixWord ++ tailWord_662983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662983).length < 2 ^ (prefixWord ++ tailWord_662983).sum := by decide
  have hdescent : baseEnd_662983 < baseStart_662983 := by decide
  rcases family_descends (prefixWord ++ tailWord_662983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663064 : List Nat := [2, 1, 2, 3, 4, 1, 1, 4, 1, 3]
def baseStart_663064 : Nat := 118140960795 + 663064 * 2 ^ 59
def prefixEnd_663064 : Nat := 4983230072969 + 3 ^ 40 * 663064 * 2
def baseEnd_663064 : Nat := 226980357795265995167087

theorem tailTrace_663064 : CollatzResearch.WordTrace tailWord_663064 prefixEnd_663064 226980357795265995167087 := by
  unfold tailWord_663064
  simp only [CollatzResearch.WordTrace]
  refine ⟨12091965434919922580314123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16122620579893230107085497 12091965434919922580314123)
  ·
    refine ⟨18137948152379883870471185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12091965434919922580314123 18137948152379883870471185)
    ·
      refine ⟨13603461114284912902853389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18137948152379883870471185 13603461114284912902853389)
      ·
        refine ⟨5101297917856842338570021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13603461114284912902853389 5101297917856842338570021)
        ·
          refine ⟨956493359598157938481879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5101297917856842338570021 956493359598157938481879)
          ·
            refine ⟨1434740039397236907722819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956493359598157938481879 1434740039397236907722819)
            ·
              refine ⟨2152110059095855361584229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434740039397236907722819 2152110059095855361584229)
              ·
                refine ⟨403520636080472880297043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2152110059095855361584229 403520636080472880297043)
                ·
                  refine ⟨605280954120709320445565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403520636080472880297043 605280954120709320445565)
                  ·
                    refine ⟨226980357795265995167087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 605280954120709320445565 226980357795265995167087)
                    ·
                      rfl

theorem cell22_663064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_663064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663064 prefixEnd_663064 := by exact prefixLift 663064
  have htrace : WordTrace (prefixWord ++ tailWord_663064) baseStart_663064 baseEnd_663064 := by
    simpa [prefixWord, tailWord_663064, baseEnd_663064] using wordTrace_append hprefix tailTrace_663064
  have hstable : (prefixWord ++ tailWord_663064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663064).length < 2 ^ (prefixWord ++ tailWord_663064).sum := by decide
  have hdescent : baseEnd_663064 < baseStart_663064 := by decide
  rcases family_descends (prefixWord ++ tailWord_663064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663075 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 2, 5]
def baseStart_663075 : Nat := 118140960795 + 663075 * 2 ^ 59
def prefixEnd_663075 : Nat := 4983230072969 + 3 ^ 40 * 663075 * 2
def baseEnd_663075 : Nat := 226984123320065633142053

theorem tailTrace_663075 : CollatzResearch.WordTrace tailWord_663075 prefixEnd_663075 226984123320065633142053 := by
  unfold tailWord_663075
  simp only [CollatzResearch.WordTrace]
  refine ⟨24184332072799994039278679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16122888048533329359519119 24184332072799994039278679)
  ·
    refine ⟨36276498109199991058918019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24184332072799994039278679 36276498109199991058918019)
    ·
      refine ⟨54414747163799986588377029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36276498109199991058918019 54414747163799986588377029)
      ·
        refine ⟨10202765093212497485320693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54414747163799986588377029 10202765093212497485320693)
        ·
          refine ⟨956509227488671639248815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10202765093212497485320693 956509227488671639248815)
          ·
            refine ⟨1434763841233007458873223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956509227488671639248815 1434763841233007458873223)
            ·
              refine ⟨2152145761849511188309835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434763841233007458873223 2152145761849511188309835)
              ·
                refine ⟨3228218642774266782464753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152145761849511188309835 3228218642774266782464753)
                ·
                  refine ⟨2421163982080700086848565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3228218642774266782464753 2421163982080700086848565)
                  ·
                    refine ⟨226984123320065633142053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2421163982080700086848565 226984123320065633142053)
                    ·
                      rfl

theorem cell22_663075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 5].length) (baseStart_663075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663075 prefixEnd_663075 := by exact prefixLift 663075
  have htrace : WordTrace (prefixWord ++ tailWord_663075) baseStart_663075 baseEnd_663075 := by
    simpa [prefixWord, tailWord_663075, baseEnd_663075] using wordTrace_append hprefix tailTrace_663075
  have hstable : (prefixWord ++ tailWord_663075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663075).length < 2 ^ (prefixWord ++ tailWord_663075).sum := by decide
  have hdescent : baseEnd_663075 < baseStart_663075 := by decide
  rcases family_descends (prefixWord ++ tailWord_663075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663090 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_663090 : Nat := 118140960795 + 663090 * 2 ^ 59
def prefixEnd_663090 : Nat := 4983230072969 + 3 ^ 40 * 663090 * 2
def baseEnd_663090 : Nat := 226989258126610594017007

theorem tailTrace_663090 : CollatzResearch.WordTrace tailWord_663090 prefixEnd_663090 226989258126610594017007 := by
  unfold tailWord_663090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046219791936412900268681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16123252778497101067383149 6046219791936412900268681)
  ·
    refine ⟨4534664843952309675201511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6046219791936412900268681 4534664843952309675201511)
    ·
      refine ⟨6801997265928464512802267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4534664843952309675201511 6801997265928464512802267)
      ·
        refine ⟨10202995898892696769203401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6801997265928464512802267 10202995898892696769203401)
        ·
          refine ⟨7652246924169522576902551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10202995898892696769203401 7652246924169522576902551)
          ·
            refine ⟨11478370386254283865353827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7652246924169522576902551 11478370386254283865353827)
            ·
              refine ⟨17217555579381425798030741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11478370386254283865353827 17217555579381425798030741)
              ·
                refine ⟨807072917783504334282691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17217555579381425798030741 807072917783504334282691)
                ·
                  refine ⟨1210609376675256501424037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807072917783504334282691 1210609376675256501424037)
                  ·
                    refine ⟨226989258126610594017007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1210609376675256501424037 226989258126610594017007)
                    ·
                      rfl

theorem cell22_663090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_663090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663090 prefixEnd_663090 := by exact prefixLift 663090
  have htrace : WordTrace (prefixWord ++ tailWord_663090) baseStart_663090 baseEnd_663090 := by
    simpa [prefixWord, tailWord_663090, baseEnd_663090] using wordTrace_append hprefix tailTrace_663090
  have hstable : (prefixWord ++ tailWord_663090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663090).length < 2 ^ (prefixWord ++ tailWord_663090).sum := by decide
  have hdescent : baseEnd_663090 < baseStart_663090 := by decide
  rcases family_descends (prefixWord ++ tailWord_663090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663120 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 4, 3]
def baseStart_663120 : Nat := 118140960795 + 663120 * 2 ^ 59
def prefixEnd_663120 : Nat := 4983230072969 + 3 ^ 40 * 663120 * 2
def baseEnd_663120 : Nat := 226999527739700515766915

theorem tailTrace_663120 : CollatzResearch.WordTrace tailWord_663120 prefixEnd_663120 226999527739700515766915 := by
  unfold tailWord_663120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12092986678818483362333407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16123982238424644483111209 12092986678818483362333407)
  ·
    refine ⟨18139480018227725043500111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12092986678818483362333407 18139480018227725043500111)
    ·
      refine ⟨27209220027341587565250167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18139480018227725043500111 27209220027341587565250167)
      ·
        refine ⟨40813830041012381347875251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27209220027341587565250167 40813830041012381347875251)
        ·
          refine ⟨61220745061518572021812877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40813830041012381347875251 61220745061518572021812877)
          ·
            refine ⟨22957779398069464508179829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61220745061518572021812877 22957779398069464508179829)
            ·
              refine ⟨2152291818569012297641859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22957779398069464508179829 2152291818569012297641859)
              ·
                refine ⟨3228437727853518446462789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152291818569012297641859 3228437727853518446462789)
                ·
                  refine ⟨605332073972534708711773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3228437727853518446462789 605332073972534708711773)
                  ·
                    refine ⟨226999527739700515766915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 605332073972534708711773 226999527739700515766915)
                    ·
                      rfl

theorem cell22_663120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4, 3].length) (baseStart_663120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663120 prefixEnd_663120 := by exact prefixLift 663120
  have htrace : WordTrace (prefixWord ++ tailWord_663120) baseStart_663120 baseEnd_663120 := by
    simpa [prefixWord, tailWord_663120, baseEnd_663120] using wordTrace_append hprefix tailTrace_663120
  have hstable : (prefixWord ++ tailWord_663120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663120).length < 2 ^ (prefixWord ++ tailWord_663120).sum := by decide
  have hdescent : baseEnd_663120 < baseStart_663120 := by decide
  rcases family_descends (prefixWord ++ tailWord_663120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663122 : List Nat := [3, 2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_663122 : Nat := 118140960795 + 663122 * 2 ^ 59
def prefixEnd_663122 : Nat := 4983230072969 + 3 ^ 40 * 663122 * 2
def baseEnd_663122 : Nat := 75666737460191059072303

theorem tailTrace_663122 : CollatzResearch.WordTrace tailWord_663122 prefixEnd_663122 75666737460191059072303 := by
  unfold tailWord_663122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046511575907430266559905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16124030869086480710826413 6046511575907430266559905)
  ·
    refine ⟨4534883681930572699919929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6046511575907430266559905 4534883681930572699919929)
    ·
      refine ⟨3401162761447929524939947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4534883681930572699919929 3401162761447929524939947)
      ·
        refine ⟨5101744142171894287409921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401162761447929524939947 5101744142171894287409921)
        ·
          refine ⟨3826308106628920715557441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5101744142171894287409921 3826308106628920715557441)
          ·
            refine ⟨2869731079971690536668081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3826308106628920715557441 2869731079971690536668081)
            ·
              refine ⟨2152298309978767902501061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2869731079971690536668081 2152298309978767902501061)
              ·
                refine ⟨403555933121018981718949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2152298309978767902501061 403555933121018981718949)
                ·
                  refine ⟨75666737460191059072303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403555933121018981718949 75666737460191059072303)
                  ·
                    rfl

theorem cell22_663122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_663122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663122 prefixEnd_663122 := by exact prefixLift 663122
  have htrace : WordTrace (prefixWord ++ tailWord_663122) baseStart_663122 baseEnd_663122 := by
    simpa [prefixWord, tailWord_663122, baseEnd_663122] using wordTrace_append hprefix tailTrace_663122
  have hstable : (prefixWord ++ tailWord_663122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663122).length < 2 ^ (prefixWord ++ tailWord_663122).sum := by decide
  have hdescent : baseEnd_663122 < baseStart_663122 := by decide
  rcases family_descends (prefixWord ++ tailWord_663122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663148 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_663148 : Nat := 118140960795 + 663148 * 2 ^ 59
def prefixEnd_663148 : Nat := 4983230072969 + 3 ^ 40 * 663148 * 2
def baseEnd_663148 : Nat := 227009112711917776066829

theorem tailTrace_663148 : CollatzResearch.WordTrace tailWord_663148 prefixEnd_663148 227009112711917776066829 := by
  unfold tailWord_663148
  simp only [CollatzResearch.WordTrace]
  refine ⟨12093497300767763753343049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16124663067690351671124065 12093497300767763753343049)
  ·
    refine ⟨9070122975575822815007287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12093497300767763753343049 9070122975575822815007287)
    ·
      refine ⟨13605184463363734222510931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9070122975575822815007287 13605184463363734222510931)
      ·
        refine ⟨20407776695045601333766397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13605184463363734222510931 20407776695045601333766397)
        ·
          refine ⟨7652916260642100500162399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20407776695045601333766397 7652916260642100500162399)
          ·
            refine ⟨11479374390963150750243599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7652916260642100500162399 11479374390963150750243599)
            ·
              refine ⟨17219061586444726125365399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11479374390963150750243599 17219061586444726125365399)
              ·
                refine ⟨25828592379667089188048099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17219061586444726125365399 25828592379667089188048099)
                ·
                  refine ⟨38742888569500633782072149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25828592379667089188048099 38742888569500633782072149)
                  ·
                    refine ⟨227009112711917776066829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 38742888569500633782072149 227009112711917776066829)
                    ·
                      rfl

theorem cell22_663148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_663148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663148 prefixEnd_663148 := by exact prefixLift 663148
  have htrace : WordTrace (prefixWord ++ tailWord_663148) baseStart_663148 baseEnd_663148 := by
    simpa [prefixWord, tailWord_663148, baseEnd_663148] using wordTrace_append hprefix tailTrace_663148
  have hstable : (prefixWord ++ tailWord_663148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663148).length < 2 ^ (prefixWord ++ tailWord_663148).sum := by decide
  have hdescent : baseEnd_663148 < baseStart_663148 := by decide
  rcases family_descends (prefixWord ++ tailWord_663148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663188 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_663188 : Nat := 118140960795 + 663188 * 2 ^ 59
def prefixEnd_663188 : Nat := 4983230072969 + 3 ^ 40 * 663188 * 2
def baseEnd_663188 : Nat := 227022805529371005066707

theorem tailTrace_663188 : CollatzResearch.WordTrace tailWord_663188 prefixEnd_663188 227022805529371005066707 := by
  unfold tailWord_663188
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094226760695307169071109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16125635680927076225428145 12094226760695307169071109)
  ·
    refine ⟨2267667517630370094200833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12094226760695307169071109 2267667517630370094200833)
    ·
      refine ⟨1700750638222777570650625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2267667517630370094200833 1700750638222777570650625)
      ·
        refine ⟨1275562978667083177987969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1700750638222777570650625 1275562978667083177987969)
        ·
          refine ⟨956672234000312383490977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1275562978667083177987969 956672234000312383490977)
          ·
            refine ⟨717504175500234287618233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 956672234000312383490977 717504175500234287618233)
            ·
              refine ⟨538128131625175715713675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717504175500234287618233 538128131625175715713675)
              ·
                refine ⟨807192197437763573570513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538128131625175715713675 807192197437763573570513)
                ·
                  refine ⟨605394148078322680177885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 807192197437763573570513 605394148078322680177885)
                  ·
                    refine ⟨227022805529371005066707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 605394148078322680177885 227022805529371005066707)
                    ·
                      rfl

theorem cell22_663188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_663188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663188 prefixEnd_663188 := by exact prefixLift 663188
  have htrace : WordTrace (prefixWord ++ tailWord_663188) baseStart_663188 baseEnd_663188 := by
    simpa [prefixWord, tailWord_663188, baseEnd_663188] using wordTrace_append hprefix tailTrace_663188
  have hstable : (prefixWord ++ tailWord_663188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663188).length < 2 ^ (prefixWord ++ tailWord_663188).sum := by decide
  have hdescent : baseEnd_663188 < baseStart_663188 := by decide
  rcases family_descends (prefixWord ++ tailWord_663188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663240 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 6]
def baseStart_663240 : Nat := 118140960795 + 663240 * 2 ^ 59
def prefixEnd_663240 : Nat := 4983230072969 + 3 ^ 40 * 663240 * 2
def baseEnd_663240 : Nat := 75680202064020067588849

theorem tailTrace_663240 : CollatzResearch.WordTrace tailWord_663240 prefixEnd_663240 75680202064020067588849 := by
  unfold tailWord_663240
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095175058601113609517587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16126900078134818146023449 12095175058601113609517587)
  ·
    refine ⟨18142762587901670414276381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12095175058601113609517587 18142762587901670414276381)
    ·
      refine ⟨6803535970463126405353643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18142762587901670414276381 6803535970463126405353643)
      ·
        refine ⟨10205303955694689608030465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6803535970463126405353643 10205303955694689608030465)
        ·
          refine ⟨7653977966771017206022849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10205303955694689608030465 7653977966771017206022849)
          ·
            refine ⟨5740483475078262904517137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7653977966771017206022849 5740483475078262904517137)
            ·
              refine ⟨4305362606308697178387853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5740483475078262904517137 4305362606308697178387853)
              ·
                refine ⟨1614510977365761441895445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4305362606308697178387853 1614510977365761441895445)
                ·
                  refine ⟨75680202064020067588849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1614510977365761441895445 75680202064020067588849)
                  ·
                    rfl

theorem cell22_663240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_663240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663240 prefixEnd_663240 := by exact prefixLift 663240
  have htrace : WordTrace (prefixWord ++ tailWord_663240) baseStart_663240 baseEnd_663240 := by
    simpa [prefixWord, tailWord_663240, baseEnd_663240] using wordTrace_append hprefix tailTrace_663240
  have hstable : (prefixWord ++ tailWord_663240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663240).length < 2 ^ (prefixWord ++ tailWord_663240).sum := by decide
  have hdescent : baseEnd_663240 < baseStart_663240 := by decide
  rcases family_descends (prefixWord ++ tailWord_663240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663272 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_663272 : Nat := 118140960795 + 663272 * 2 ^ 59
def prefixEnd_663272 : Nat := 4983230072969 + 3 ^ 40 * 663272 * 2
def baseEnd_663272 : Nat := 227051560446022785966449

theorem tailTrace_663272 : CollatzResearch.WordTrace tailWord_663272 prefixEnd_663272 227051560446022785966449 := by
  unfold tailWord_663272
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095758626543148342100035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16127678168724197789466713 12095758626543148342100035)
  ·
    refine ⟨18143637939814722513150053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12095758626543148342100035 18143637939814722513150053)
    ·
      refine ⟨3401932113715260471215635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18143637939814722513150053 3401932113715260471215635)
      ·
        refine ⟨5102898170572890706823453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401932113715260471215635 5102898170572890706823453)
        ·
          refine ⟨1913586813964834015058795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5102898170572890706823453 1913586813964834015058795)
          ·
            refine ⟨2870380220947251022588193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913586813964834015058795 2870380220947251022588193)
            ·
              refine ⟨2152785165710438266941145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870380220947251022588193 2152785165710438266941145)
              ·
                refine ⟨1614588874282828700205859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2152785165710438266941145 1614588874282828700205859)
                ·
                  refine ⟨2421883311424243050308789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614588874282828700205859 2421883311424243050308789)
                  ·
                    refine ⟨227051560446022785966449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2421883311424243050308789 227051560446022785966449)
                    ·
                      rfl

theorem cell22_663272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_663272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663272 prefixEnd_663272 := by exact prefixLift 663272
  have htrace : WordTrace (prefixWord ++ tailWord_663272) baseStart_663272 baseEnd_663272 := by
    simpa [prefixWord, tailWord_663272, baseEnd_663272] using wordTrace_append hprefix tailTrace_663272
  have hstable : (prefixWord ++ tailWord_663272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663272).length < 2 ^ (prefixWord ++ tailWord_663272).sum := by decide
  have hdescent : baseEnd_663272 < baseStart_663272 := by decide
  rcases family_descends (prefixWord ++ tailWord_663272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663306 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 2, 3]
def baseStart_663306 : Nat := 118140960795 + 663306 * 2 ^ 59
def prefixEnd_663306 : Nat := 4983230072969 + 3 ^ 40 * 663306 * 2
def baseEnd_663306 : Nat := 227063199340858030616345

theorem tailTrace_663306 : CollatzResearch.WordTrace tailWord_663306 prefixEnd_663306 227063199340858030616345 := by
  unfold tailWord_663306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6048189333740780122734443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16128504889975413660625181 6048189333740780122734443)
  ·
    refine ⟨9072284000611170184101665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6048189333740780122734443 9072284000611170184101665)
    ·
      refine ⟨6804213000458377638076249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9072284000611170184101665 6804213000458377638076249)
      ·
        refine ⟨5103159750343783228557187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6804213000458377638076249 5103159750343783228557187)
        ·
          refine ⟨7654739625515674842835781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5103159750343783228557187 7654739625515674842835781)
          ·
            refine ⟨1435263679784189033031709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7654739625515674842835781 1435263679784189033031709)
            ·
              refine ⟨538223879919070887386891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1435263679784189033031709 538223879919070887386891)
              ·
                refine ⟨807335819878606331080337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538223879919070887386891 807335819878606331080337)
                ·
                  refine ⟨605501864908954748310253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 807335819878606331080337 605501864908954748310253)
                  ·
                    refine ⟨227063199340858030616345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 605501864908954748310253 227063199340858030616345)
                    ·
                      rfl

theorem cell22_663306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_663306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663306 prefixEnd_663306 := by exact prefixLift 663306
  have htrace : WordTrace (prefixWord ++ tailWord_663306) baseStart_663306 baseEnd_663306 := by
    simpa [prefixWord, tailWord_663306, baseEnd_663306] using wordTrace_append hprefix tailTrace_663306
  have hstable : (prefixWord ++ tailWord_663306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663306).length < 2 ^ (prefixWord ++ tailWord_663306).sum := by decide
  have hdescent : baseEnd_663306 < baseStart_663306 := by decide
  rcases family_descends (prefixWord ++ tailWord_663306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663319 : List Nat := [1, 1, 3, 4, 2, 3, 2, 6]
def baseStart_663319 : Nat := 118140960795 + 663319 * 2 ^ 59
def prefixEnd_663319 : Nat := 4983230072969 + 3 ^ 40 * 663319 * 2
def baseEnd_663319 : Nat := 25229738834058925560145

theorem tailTrace_663319 : CollatzResearch.WordTrace tailWord_663319 prefixEnd_663319 25229738834058925560145 := by
  unfold tailWord_663319
  simp only [CollatzResearch.WordTrace]
  refine ⟨24193231483916023711161011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16128820989277349140774007 24193231483916023711161011)
  ·
    refine ⟨36289847225874035566741517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24193231483916023711161011 36289847225874035566741517)
    ·
      refine ⟨13608692709702763337528069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36289847225874035566741517 13608692709702763337528069)
      ·
        refine ⟨2551629883069268125786513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13608692709702763337528069 2551629883069268125786513)
        ·
          refine ⟨1913722412301951094339885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2551629883069268125786513 1913722412301951094339885)
          ·
            refine ⟨717645904613231660377457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1913722412301951094339885 717645904613231660377457)
            ·
              refine ⟨538234428459923745283093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717645904613231660377457 538234428459923745283093)
              ·
                refine ⟨25229738834058925560145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 538234428459923745283093 25229738834058925560145)
                ·
                  rfl

theorem cell22_663319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 6].length) (baseStart_663319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663319 prefixEnd_663319 := by exact prefixLift 663319
  have htrace : WordTrace (prefixWord ++ tailWord_663319) baseStart_663319 baseEnd_663319 := by
    simpa [prefixWord, tailWord_663319, baseEnd_663319] using wordTrace_append hprefix tailTrace_663319
  have hstable : (prefixWord ++ tailWord_663319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663319).length < 2 ^ (prefixWord ++ tailWord_663319).sum := by decide
  have hdescent : baseEnd_663319 < baseStart_663319 := by decide
  rcases family_descends (prefixWord ++ tailWord_663319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663360 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_663360 : Nat := 118140960795 + 663360 * 2 ^ 59
def prefixEnd_663360 : Nat := 4983230072969 + 3 ^ 40 * 663360 * 2
def baseEnd_663360 : Nat := 227081684644419889766179

theorem tailTrace_663360 : CollatzResearch.WordTrace tailWord_663360 prefixEnd_663360 227081684644419889766179 := by
  unfold tailWord_663360
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097363438383743856701767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16129817917844991808935689 12097363438383743856701767)
  ·
    refine ⟨18146045157575615785052651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12097363438383743856701767 18146045157575615785052651)
    ·
      refine ⟨27219067736363423677578977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18146045157575615785052651 27219067736363423677578977)
      ·
        refine ⟨20414300802272567758184233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27219067736363423677578977 20414300802272567758184233)
        ·
          refine ⟨15310725601704425818638175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20414300802272567758184233 15310725601704425818638175)
          ·
            refine ⟨22966088402556638727957263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15310725601704425818638175 22966088402556638727957263)
            ·
              refine ⟨34449132603834958091935895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22966088402556638727957263 34449132603834958091935895)
              ·
                refine ⟨51673698905752437137903843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34449132603834958091935895 51673698905752437137903843)
                ·
                  refine ⟨77510548358628655706855765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51673698905752437137903843 77510548358628655706855765)
                  ·
                    refine ⟨227081684644419889766179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 77510548358628655706855765 227081684644419889766179)
                    ·
                      rfl

theorem cell22_663360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_663360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663360 prefixEnd_663360 := by exact prefixLift 663360
  have htrace : WordTrace (prefixWord ++ tailWord_663360) baseStart_663360 baseEnd_663360 := by
    simpa [prefixWord, tailWord_663360, baseEnd_663360] using wordTrace_append hprefix tailTrace_663360
  have hstable : (prefixWord ++ tailWord_663360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663360).length < 2 ^ (prefixWord ++ tailWord_663360).sum := by decide
  have hdescent : baseEnd_663360 < baseStart_663360 := by decide
  rcases family_descends (prefixWord ++ tailWord_663360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663402 : List Nat := [3, 1, 3, 4, 1, 2, 2, 2, 1, 3]
def baseStart_663402 : Nat := 118140960795 + 663402 * 2 ^ 59
def prefixEnd_663402 : Nat := 4983230072969 + 3 ^ 40 * 663402 * 2
def baseEnd_663402 : Nat := 227096062102745780216051

theorem tailTrace_663402 : CollatzResearch.WordTrace tailWord_663402 prefixEnd_663402 227096062102745780216051 := by
  unfold tailWord_663402
  simp only [CollatzResearch.WordTrace]
  refine ⟨6049064685653832221608115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16130839161743552590954973 6049064685653832221608115)
  ·
    refine ⟨9073597028480748332412173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6049064685653832221608115 9073597028480748332412173)
    ·
      refine ⟨3402598885680280624654565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9073597028480748332412173 3402598885680280624654565)
      ·
        refine ⟨637987291065052617122731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3402598885680280624654565 637987291065052617122731)
        ·
          refine ⟨956980936597578925684097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637987291065052617122731 956980936597578925684097)
          ·
            refine ⟨717735702448184194263073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 956980936597578925684097 717735702448184194263073)
            ·
              refine ⟨538301776836138145697305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717735702448184194263073 538301776836138145697305)
              ·
                refine ⟨403726332627103609272979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538301776836138145697305 403726332627103609272979)
                ·
                  refine ⟨605589498940655413909469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403726332627103609272979 605589498940655413909469)
                  ·
                    refine ⟨227096062102745780216051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 605589498940655413909469 227096062102745780216051)
                    ·
                      rfl

theorem cell22_663402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_663402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663402 prefixEnd_663402 := by exact prefixLift 663402
  have htrace : WordTrace (prefixWord ++ tailWord_663402) baseStart_663402 baseEnd_663402 := by
    simpa [prefixWord, tailWord_663402, baseEnd_663402] using wordTrace_append hprefix tailTrace_663402
  have hstable : (prefixWord ++ tailWord_663402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663402).length < 2 ^ (prefixWord ++ tailWord_663402).sum := by decide
  have hdescent : baseEnd_663402 < baseStart_663402 := by decide
  rcases family_descends (prefixWord ++ tailWord_663402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663409 : List Nat := [1, 2, 2, 2, 1, 3, 3, 4, 4]
def baseStart_663409 : Nat := 118140960795 + 663409 * 2 ^ 59
def prefixEnd_663409 : Nat := 4983230072969 + 3 ^ 40 * 663409 * 2
def baseEnd_663409 : Nat := 75699486115266698430343

theorem tailTrace_663409 : CollatzResearch.WordTrace tailWord_663409 prefixEnd_663409 75699486115266698430343 := by
  unfold tailWord_663409
  simp only [CollatzResearch.WordTrace]
  refine ⟨24196514053589969081937281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16131009369059979387958187 24196514053589969081937281)
  ·
    refine ⟨18147385540192476811452961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24196514053589969081937281 18147385540192476811452961)
    ·
      refine ⟨13610539155144357608589721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18147385540192476811452961 13610539155144357608589721)
      ·
        refine ⟨10207904366358268206442291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13610539155144357608589721 10207904366358268206442291)
        ·
          refine ⟨15311856549537402309663437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10207904366358268206442291 15311856549537402309663437)
          ·
            refine ⟨5741946206076525866123789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15311856549537402309663437 5741946206076525866123789)
            ·
              refine ⟨2153229827278697199796421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5741946206076525866123789 2153229827278697199796421)
              ·
                refine ⟨403730592614755724961829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2153229827278697199796421 403730592614755724961829)
                ·
                  refine ⟨75699486115266698430343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403730592614755724961829 75699486115266698430343)
                  ·
                    rfl

theorem cell22_663409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 4].length) (baseStart_663409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663409 prefixEnd_663409 := by exact prefixLift 663409
  have htrace : WordTrace (prefixWord ++ tailWord_663409) baseStart_663409 baseEnd_663409 := by
    simpa [prefixWord, tailWord_663409, baseEnd_663409] using wordTrace_append hprefix tailTrace_663409
  have hstable : (prefixWord ++ tailWord_663409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663409).length < 2 ^ (prefixWord ++ tailWord_663409).sum := by decide
  have hdescent : baseEnd_663409 < baseStart_663409 := by decide
  rcases family_descends (prefixWord ++ tailWord_663409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663424 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 2, 3]
def baseStart_663424 : Nat := 118140960795 + 663424 * 2 ^ 59
def prefixEnd_663424 : Nat := 4983230072969 + 3 ^ 40 * 663424 * 2
def baseEnd_663424 : Nat := 227103593152345056165983

theorem tailTrace_663424 : CollatzResearch.WordTrace tailWord_663424 prefixEnd_663424 227103593152345056165983 := by
  unfold tailWord_663424
  simp only [CollatzResearch.WordTrace]
  refine ⟨12098530574267813321866663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16131374099023751095822217 12098530574267813321866663)
  ·
    refine ⟨18147795861401719982799995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12098530574267813321866663 18147795861401719982799995)
    ·
      refine ⟨27221693792102579974199993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18147795861401719982799995 27221693792102579974199993)
      ·
        refine ⟨20416270344076934980649995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27221693792102579974199993 20416270344076934980649995)
        ·
          refine ⟨30624405516115402470974993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20416270344076934980649995 30624405516115402470974993)
          ·
            refine ⟨22968304137086551853231245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30624405516115402470974993 22968304137086551853231245)
            ·
              refine ⟨8613114051407456944961717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22968304137086551853231245 8613114051407456944961717)
              ·
                refine ⟨807479442319449088590161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8613114051407456944961717 807479442319449088590161)
                ·
                  refine ⟨605609581739586816442621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 807479442319449088590161 605609581739586816442621)
                  ·
                    refine ⟨227103593152345056165983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 605609581739586816442621 227103593152345056165983)
                    ·
                      rfl

theorem cell22_663424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2, 3].length) (baseStart_663424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663424 prefixEnd_663424 := by exact prefixLift 663424
  have htrace : WordTrace (prefixWord ++ tailWord_663424) baseStart_663424 baseEnd_663424 := by
    simpa [prefixWord, tailWord_663424, baseEnd_663424] using wordTrace_append hprefix tailTrace_663424
  have hstable : (prefixWord ++ tailWord_663424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663424).length < 2 ^ (prefixWord ++ tailWord_663424).sum := by decide
  have hdescent : baseEnd_663424 < baseStart_663424 := by decide
  rcases family_descends (prefixWord ++ tailWord_663424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663486 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_663486 : Nat := 118140960795 + 663486 * 2 ^ 59
def prefixEnd_663486 : Nat := 4983230072969 + 3 ^ 40 * 663486 * 2
def baseEnd_663486 : Nat := 227124817019397561115793

theorem tailTrace_663486 : CollatzResearch.WordTrace tailWord_663486 prefixEnd_663486 227124817019397561115793 := by
  unfold tailWord_663486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3024915309288876404061289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16132881649540674154993541 3024915309288876404061289)
  ·
    refine ⟨2268686481966657303045967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3024915309288876404061289 2268686481966657303045967)
    ·
      refine ⟨3403029722949985954568951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2268686481966657303045967 3403029722949985954568951)
      ·
        refine ⟨5104544584424978931853427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3403029722949985954568951 5104544584424978931853427)
        ·
          refine ⟨7656816876637468397780141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5104544584424978931853427 7656816876637468397780141)
          ·
            refine ⟨2871306328739050649167553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7656816876637468397780141 2871306328739050649167553)
            ·
              refine ⟨2153479746554287986875665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2871306328739050649167553 2153479746554287986875665)
              ·
                refine ⟨1615109809915715990156749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2153479746554287986875665 1615109809915715990156749)
                ·
                  refine ⟨605666178718393496308781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1615109809915715990156749 605666178718393496308781)
                  ·
                    refine ⟨227124817019397561115793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 605666178718393496308781 227124817019397561115793)
                    ·
                      rfl

theorem cell22_663486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_663486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663486 prefixEnd_663486 := by exact prefixLift 663486
  have htrace : WordTrace (prefixWord ++ tailWord_663486) baseStart_663486 baseEnd_663486 := by
    simpa [prefixWord, tailWord_663486, baseEnd_663486] using wordTrace_append hprefix tailTrace_663486
  have hstable : (prefixWord ++ tailWord_663486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663486).length < 2 ^ (prefixWord ++ tailWord_663486).sum := by decide
  have hdescent : baseEnd_663486 < baseStart_663486 := by decide
  rcases family_descends (prefixWord ++ tailWord_663486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663533 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 5]
def baseStart_663533 : Nat := 118140960795 + 663533 * 2 ^ 59
def prefixEnd_663533 : Nat := 4983230072969 + 3 ^ 40 * 663533 * 2
def baseEnd_663533 : Nat := 75713635359968368396883

theorem tailTrace_663533 : CollatzResearch.WordTrace tailWord_663533 prefixEnd_663533 75713635359968368396883 := by
  unfold tailWord_663533
  simp only [CollatzResearch.WordTrace]
  refine ⟨24201036705140738259451253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16134024470093825506300835 24201036705140738259451253)
  ·
    refine ⟨2268847191106944211823555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24201036705140738259451253 2268847191106944211823555)
    ·
      refine ⟨3403270786660416317735333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2268847191106944211823555 3403270786660416317735333)
      ·
        refine ⟨638113272498828059575375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3403270786660416317735333 638113272498828059575375)
        ·
          refine ⟨957169908748242089363063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638113272498828059575375 957169908748242089363063)
          ·
            refine ⟨1435754863122363134044595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957169908748242089363063 1435754863122363134044595)
            ·
              refine ⟨2153632294683544701066893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435754863122363134044595 2153632294683544701066893)
              ·
                refine ⟨807612110506329262900085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2153632294683544701066893 807612110506329262900085)
                ·
                  refine ⟨75713635359968368396883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 807612110506329262900085 75713635359968368396883)
                  ·
                    rfl

theorem cell22_663533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_663533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663533 prefixEnd_663533 := by exact prefixLift 663533
  have htrace : WordTrace (prefixWord ++ tailWord_663533) baseStart_663533 baseEnd_663533 := by
    simpa [prefixWord, tailWord_663533, baseEnd_663533] using wordTrace_append hprefix tailTrace_663533
  have hstable : (prefixWord ++ tailWord_663533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663533).length < 2 ^ (prefixWord ++ tailWord_663533).sum := by decide
  have hdescent : baseEnd_663533 < baseStart_663533 := by decide
  rcases family_descends (prefixWord ++ tailWord_663533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663559 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 3, 5]
def baseStart_663559 : Nat := 118140960795 + 663559 * 2 ^ 59
def prefixEnd_663559 : Nat := 4983230072969 + 3 ^ 40 * 663559 * 2
def baseEnd_663559 : Nat := 227149806411249704040569

theorem tailTrace_663559 : CollatzResearch.WordTrace tailWord_663559 prefixEnd_663559 227149806411249704040569 := by
  unfold tailWord_663559
  simp only [CollatzResearch.WordTrace]
  refine ⟨24201985003046544699897731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16134656668697696466598487 24201985003046544699897731)
  ·
    refine ⟨36302977504569817049846597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24201985003046544699897731 36302977504569817049846597)
    ·
      refine ⟨6806808282106840696846237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36302977504569817049846597 6806808282106840696846237)
      ·
        refine ⟨2552553105790065261317339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6806808282106840696846237 2552553105790065261317339)
        ·
          refine ⟨3828829658685097891976009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552553105790065261317339 3828829658685097891976009)
          ·
            refine ⟨2871622244013823418982007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3828829658685097891976009 2871622244013823418982007)
            ·
              refine ⟨4307433366020735128473011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871622244013823418982007 4307433366020735128473011)
              ·
                refine ⟨6461150049031102692709517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4307433366020735128473011 6461150049031102692709517)
                ·
                  refine ⟨2422931268386663509766069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6461150049031102692709517 2422931268386663509766069)
                  ·
                    refine ⟨227149806411249704040569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2422931268386663509766069 227149806411249704040569)
                    ·
                      rfl

theorem cell22_663559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_663559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663559 prefixEnd_663559 := by exact prefixLift 663559
  have htrace : WordTrace (prefixWord ++ tailWord_663559) baseStart_663559 baseEnd_663559 := by
    simpa [prefixWord, tailWord_663559, baseEnd_663559] using wordTrace_append hprefix tailTrace_663559
  have hstable : (prefixWord ++ tailWord_663559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663559).length < 2 ^ (prefixWord ++ tailWord_663559).sum := by decide
  have hdescent : baseEnd_663559 < baseStart_663559 := by decide
  rcases family_descends (prefixWord ++ tailWord_663559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663578 : List Nat := [3, 1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_663578 : Nat := 118140960795 + 663578 * 2 ^ 59
def prefixEnd_663578 : Nat := 4983230072969 + 3 ^ 40 * 663578 * 2
def baseEnd_663578 : Nat := 75718770166513329271837

theorem tailTrace_663578 : CollatzResearch.WordTrace tailWord_663578 prefixEnd_663578 75718770166513329271837 := by
  unfold tailWord_663578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6050669497494427736209847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16135118659985140629892925 6050669497494427736209847)
  ·
    refine ⟨9076004246241641604314771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6050669497494427736209847 9076004246241641604314771)
    ·
      refine ⟨13614006369362462406472157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9076004246241641604314771 13614006369362462406472157)
      ·
        refine ⟨5105252388510923402427059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13614006369362462406472157 5105252388510923402427059)
        ·
          refine ⟨7657878582766385103640589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5105252388510923402427059 7657878582766385103640589)
          ·
            refine ⟨2871704468537394413865221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7657878582766385103640589 2871704468537394413865221)
            ·
              refine ⟨538444587850761452599729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2871704468537394413865221 538444587850761452599729)
              ·
                refine ⟨403833440888071089449797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538444587850761452599729 403833440888071089449797)
                ·
                  refine ⟨75718770166513329271837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403833440888071089449797 75718770166513329271837)
                  ·
                    rfl

theorem cell22_663578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_663578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663578 prefixEnd_663578 := by exact prefixLift 663578
  have htrace : WordTrace (prefixWord ++ tailWord_663578) baseStart_663578 baseEnd_663578 := by
    simpa [prefixWord, tailWord_663578, baseEnd_663578] using wordTrace_append hprefix tailTrace_663578
  have hstable : (prefixWord ++ tailWord_663578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663578).length < 2 ^ (prefixWord ++ tailWord_663578).sum := by decide
  have hdescent : baseEnd_663578 < baseStart_663578 := by decide
  rcases family_descends (prefixWord ++ tailWord_663578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663589 : List Nat := [1, 3, 1, 2, 2, 3, 3, 7]
def baseStart_663589 : Nat := 118140960795 + 663589 * 2 ^ 59
def prefixEnd_663589 : Nat := 4983230072969 + 3 ^ 40 * 663589 * 2
def baseEnd_663589 : Nat := 25240008447148847310053

theorem tailTrace_663589 : CollatzResearch.WordTrace tailWord_663589 prefixEnd_663589 25240008447148847310053 := by
  unfold tailWord_663589
  simp only [CollatzResearch.WordTrace]
  refine ⟨24203079192937859823489821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16135386128625239882326547 24203079192937859823489821)
  ·
    refine ⟨9076154697351697433808683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24203079192937859823489821 9076154697351697433808683)
    ·
      refine ⟨13614232046027546150713025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9076154697351697433808683 13614232046027546150713025)
      ·
        refine ⟨10210674034520659613034769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13614232046027546150713025 10210674034520659613034769)
        ·
          refine ⟨7658005525890494709776077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10210674034520659613034769 7658005525890494709776077)
          ·
            refine ⟨2871752072208935516166029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7658005525890494709776077 2871752072208935516166029)
            ·
              refine ⟨1076907027078350818562261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2871752072208935516166029 1076907027078350818562261)
              ·
                refine ⟨25240008447148847310053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1076907027078350818562261 25240008447148847310053)
                ·
                  rfl

theorem cell22_663589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 7].length) (baseStart_663589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663589 prefixEnd_663589 := by exact prefixLift 663589
  have htrace : WordTrace (prefixWord ++ tailWord_663589) baseStart_663589 baseEnd_663589 := by
    simpa [prefixWord, tailWord_663589, baseEnd_663589] using wordTrace_append hprefix tailTrace_663589
  have hstable : (prefixWord ++ tailWord_663589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663589).length < 2 ^ (prefixWord ++ tailWord_663589).sum := by decide
  have hdescent : baseEnd_663589 < baseStart_663589 := by decide
  rcases family_descends (prefixWord ++ tailWord_663589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663608 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 2, 4]
def baseStart_663608 : Nat := 118140960795 + 663608 * 2 ^ 59
def prefixEnd_663608 : Nat := 4983230072969 + 3 ^ 40 * 663608 * 2
def baseEnd_663608 : Nat := 227166580112629909565419

theorem tailTrace_663608 : CollatzResearch.WordTrace tailWord_663608 prefixEnd_663608 227166580112629909565419 := by
  unfold tailWord_663608
  simp only [CollatzResearch.WordTrace]
  refine ⟨12101886089934513034215739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16135848119912684045620985 12101886089934513034215739)
  ·
    refine ⟨18152829134901769551323609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12101886089934513034215739 18152829134901769551323609)
    ·
      refine ⟨13614621851176327163492707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18152829134901769551323609 13614621851176327163492707)
      ·
        refine ⟨20421932776764490745239061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13614621851176327163492707 20421932776764490745239061)
        ·
          refine ⟨957278098910835503683081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20421932776764490745239061 957278098910835503683081)
          ·
            refine ⟨717958574183126627762311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957278098910835503683081 717958574183126627762311)
            ·
              refine ⟨1076937861274689941643467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717958574183126627762311 1076937861274689941643467)
              ·
                refine ⟨1615406791912034912465201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076937861274689941643467 1615406791912034912465201)
                ·
                  refine ⟨1211555093934026184348901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1615406791912034912465201 1211555093934026184348901)
                  ·
                    refine ⟨227166580112629909565419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1211555093934026184348901 227166580112629909565419)
                    ·
                      rfl

theorem cell22_663608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_663608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663608 prefixEnd_663608 := by exact prefixLift 663608
  have htrace : WordTrace (prefixWord ++ tailWord_663608) baseStart_663608 baseEnd_663608 := by
    simpa [prefixWord, tailWord_663608, baseEnd_663608] using wordTrace_append hprefix tailTrace_663608
  have hstable : (prefixWord ++ tailWord_663608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663608).length < 2 ^ (prefixWord ++ tailWord_663608).sum := by decide
  have hdescent : baseEnd_663608 < baseStart_663608 := by decide
  rcases family_descends (prefixWord ++ tailWord_663608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663758 : List Nat := [4, 1, 1, 1, 4, 3, 1, 7]
def baseStart_663758 : Nat := 118140960795 + 663758 * 2 ^ 59
def prefixEnd_663758 : Nat := 4983230072969 + 3 ^ 40 * 663758 * 2
def baseEnd_663758 : Nat := 25246436464231057590551

theorem tailTrace_663758 : CollatzResearch.WordTrace tailWord_663758 prefixEnd_663758 25246436464231057590551 := by
  unfold tailWord_663758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3026155391165700210798991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16139495419550401124261285 3026155391165700210798991)
  ·
    refine ⟨4539233086748550316198487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3026155391165700210798991 4539233086748550316198487)
    ·
      refine ⟨6808849630122825474297731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4539233086748550316198487 6808849630122825474297731)
      ·
        refine ⟨10213274445184238211446597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6808849630122825474297731 10213274445184238211446597)
        ·
          refine ⟨1914988958472044664646237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10213274445184238211446597 1914988958472044664646237)
          ·
            refine ⟨718120859427016749242339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1914988958472044664646237 718120859427016749242339)
            ·
              refine ⟨1077181289140525123863509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718120859427016749242339 1077181289140525123863509)
              ·
                refine ⟨25246436464231057590551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1077181289140525123863509 25246436464231057590551)
                ·
                  rfl

theorem cell22_663758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_663758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663758 prefixEnd_663758 := by exact prefixLift 663758
  have htrace : WordTrace (prefixWord ++ tailWord_663758) baseStart_663758 baseEnd_663758 := by
    simpa [prefixWord, tailWord_663758, baseEnd_663758] using wordTrace_append hprefix tailTrace_663758
  have hstable : (prefixWord ++ tailWord_663758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663758).length < 2 ^ (prefixWord ++ tailWord_663758).sum := by decide
  have hdescent : baseEnd_663758 < baseStart_663758 := by decide
  rcases family_descends (prefixWord ++ tailWord_663758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663786 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_663786 : Nat := 118140960795 + 663786 * 2 ^ 59
def prefixEnd_663786 : Nat := 4983230072969 + 3 ^ 40 * 663786 * 2
def baseEnd_663786 : Nat := 75742504383432259538291

theorem tailTrace_663786 : CollatzResearch.WordTrace tailWord_663786 prefixEnd_663786 75742504383432259538291 := by
  unfold tailWord_663786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6052566093306040617102803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16140176248816108312274141 6052566093306040617102803)
  ·
    refine ⟨9078849139959060925654205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6052566093306040617102803 9078849139959060925654205)
    ·
      refine ⟨3404568427484647847120327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9078849139959060925654205 3404568427484647847120327)
      ·
        refine ⟨5106852641226971770680491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3404568427484647847120327 5106852641226971770680491)
        ·
          refine ⟨7660278961840457656020737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5106852641226971770680491 7660278961840457656020737)
          ·
            refine ⟨5745209221380343242015553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7660278961840457656020737 5745209221380343242015553)
            ·
              refine ⟨4308906916035257431511665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5745209221380343242015553 4308906916035257431511665)
              ·
                refine ⟨3231680187026443073633749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4308906916035257431511665 3231680187026443073633749)
                ·
                  refine ⟨75742504383432259538291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3231680187026443073633749 75742504383432259538291)
                  ·
                    rfl

theorem cell22_663786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_663786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663786 prefixEnd_663786 := by exact prefixLift 663786
  have htrace : WordTrace (prefixWord ++ tailWord_663786) baseStart_663786 baseEnd_663786 := by
    simpa [prefixWord, tailWord_663786, baseEnd_663786] using wordTrace_append hprefix tailTrace_663786
  have hstable : (prefixWord ++ tailWord_663786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663786).length < 2 ^ (prefixWord ++ tailWord_663786).sum := by decide
  have hdescent : baseEnd_663786 < baseStart_663786 := by decide
  rcases family_descends (prefixWord ++ tailWord_663786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663865 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 6]
def baseStart_663865 : Nat := 118140960795 + 663865 * 2 ^ 59
def prefixEnd_663865 : Nat := 4983230072969 + 3 ^ 40 * 663865 * 2
def baseEnd_663865 : Nat := 75751518821588968629877

theorem tailTrace_663865 : CollatzResearch.WordTrace tailWord_663865 prefixEnd_663865 75751518821588968629877 := by
  unfold tailWord_663865
  simp only [CollatzResearch.WordTrace]
  refine ⟨24213145739937958960537049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16142097159958639307024699 24213145739937958960537049)
  ·
    refine ⟨18159859304953469220402787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24213145739937958960537049 18159859304953469220402787)
    ·
      refine ⟨27239788957430203830604181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18159859304953469220402787 27239788957430203830604181)
      ·
        refine ⟨1276865107379540804559571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27239788957430203830604181 1276865107379540804559571)
        ·
          refine ⟨1915297661069311206839357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1276865107379540804559571 1915297661069311206839357)
          ·
            refine ⟨718236622900991702564759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1915297661069311206839357 718236622900991702564759)
            ·
              refine ⟨1077354934351487553847139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718236622900991702564759 1077354934351487553847139)
              ·
                refine ⟨1616032401527231330770709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077354934351487553847139 1616032401527231330770709)
                ·
                  refine ⟨75751518821588968629877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1616032401527231330770709 75751518821588968629877)
                  ·
                    rfl

theorem cell22_663865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 6].length) (baseStart_663865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_663865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_663865 prefixEnd_663865 := by exact prefixLift 663865
  have htrace : WordTrace (prefixWord ++ tailWord_663865) baseStart_663865 baseEnd_663865 := by
    simpa [prefixWord, tailWord_663865, baseEnd_663865] using wordTrace_append hprefix tailTrace_663865
  have hstable : (prefixWord ++ tailWord_663865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663865).length < 2 ^ (prefixWord ++ tailWord_663865).sum := by decide
  have hdescent : baseEnd_663865 < baseStart_663865 := by decide
  rcases family_descends (prefixWord ++ tailWord_663865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664045 : List Nat := [1, 5, 1, 3, 1, 1, 1, 9]
def baseStart_664045 : Nat := 118140960795 + 664045 * 2 ^ 59
def prefixEnd_664045 : Nat := 4983230072969 + 3 ^ 40 * 664045 * 2
def baseEnd_664045 : Nat := 25257352682589604043231

theorem tailTrace_664045 : CollatzResearch.WordTrace tailWord_664045 prefixEnd_664045 25257352682589604043231 := by
  unfold tailWord_664045
  simp only [CollatzResearch.WordTrace]
  refine ⟨24219710879285849702089589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16146473919523899801393059 24219710879285849702089589)
  ·
    refine ⟨2270597894933048409570899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24219710879285849702089589 2270597894933048409570899)
    ·
      refine ⟨3405896842399572614356349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270597894933048409570899 3405896842399572614356349)
      ·
        refine ⟨1277211315899839730383631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3405896842399572614356349 1277211315899839730383631)
        ·
          refine ⟨1915816973849759595575447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277211315899839730383631 1915816973849759595575447)
          ·
            refine ⟨2873725460774639393363171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915816973849759595575447 2873725460774639393363171)
            ·
              refine ⟨4310588191161959090044757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873725460774639393363171 4310588191161959090044757)
              ·
                refine ⟨25257352682589604043231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4310588191161959090044757 25257352682589604043231)
                ·
                  rfl

theorem cell22_664045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 9].length) (baseStart_664045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664045 prefixEnd_664045 := by exact prefixLift 664045
  have htrace : WordTrace (prefixWord ++ tailWord_664045) baseStart_664045 baseEnd_664045 := by
    simpa [prefixWord, tailWord_664045, baseEnd_664045] using wordTrace_append hprefix tailTrace_664045
  have hstable : (prefixWord ++ tailWord_664045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664045).length < 2 ^ (prefixWord ++ tailWord_664045).sum := by decide
  have hdescent : baseEnd_664045 < baseStart_664045 := by decide
  rcases family_descends (prefixWord ++ tailWord_664045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664058 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_664058 : Nat := 118140960795 + 664058 * 2 ^ 59
def prefixEnd_664058 : Nat := 4983230072969 + 3 ^ 40 * 664058 * 2
def baseEnd_664058 : Nat := 227320624308978735814039

theorem tailTrace_664058 : CollatzResearch.WordTrace tailWord_664058 prefixEnd_664058 227320624308978735814039 := by
  unfold tailWord_664058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6055046257059688230578207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16146790018825835281541885 6055046257059688230578207)
  ·
    refine ⟨9082569385589532345867311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6055046257059688230578207 9082569385589532345867311)
    ·
      refine ⟨13623854078384298518800967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9082569385589532345867311 13623854078384298518800967)
      ·
        refine ⟨20435781117576447778201451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13623854078384298518800967 20435781117576447778201451)
        ·
          refine ⟨30653671676364671667302177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20435781117576447778201451 30653671676364671667302177)
          ·
            refine ⟨22990253757273503750476633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30653671676364671667302177 22990253757273503750476633)
            ·
              refine ⟨17242690317955127812857475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22990253757273503750476633 17242690317955127812857475)
              ·
                refine ⟨25864035476932691719286213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17242690317955127812857475 25864035476932691719286213)
                ·
                  refine ⟨4849506651924879697366165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25864035476932691719286213 4849506651924879697366165)
                  ·
                    refine ⟨227320624308978735814039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4849506651924879697366165 227320624308978735814039)
                    ·
                      rfl

theorem cell22_664058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_664058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664058 prefixEnd_664058 := by exact prefixLift 664058
  have htrace : WordTrace (prefixWord ++ tailWord_664058) baseStart_664058 baseEnd_664058 := by
    simpa [prefixWord, tailWord_664058, baseEnd_664058] using wordTrace_append hprefix tailTrace_664058
  have hstable : (prefixWord ++ tailWord_664058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664058).length < 2 ^ (prefixWord ++ tailWord_664058).sum := by decide
  have hdescent : baseEnd_664058 < baseStart_664058 := by decide
  rcases family_descends (prefixWord ++ tailWord_664058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664060 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 5, 3]
def baseStart_664060 : Nat := 118140960795 + 664060 * 2 ^ 59
def prefixEnd_664060 : Nat := 4983230072969 + 3 ^ 40 * 664060 * 2
def baseEnd_664060 : Nat := 227321308949851397264033

theorem tailTrace_664060 : CollatzResearch.WordTrace tailWord_664060 prefixEnd_664060 227321308949851397264033 := by
  unfold tailWord_664060
  simp only [CollatzResearch.WordTrace]
  refine ⟨12110128987115753631942817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16146838649487671509257089 12110128987115753631942817)
  ·
    refine ⟨9082596740336815223957113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12110128987115753631942817 9082596740336815223957113)
    ·
      refine ⟨6811947555252611417967835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9082596740336815223957113 6811947555252611417967835)
      ·
        refine ⟨10217921332878917126951753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6811947555252611417967835 10217921332878917126951753)
        ·
          refine ⟨7663440999659187845213815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10217921332878917126951753 7663440999659187845213815)
          ·
            refine ⟨11495161499488781767820723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663440999659187845213815 11495161499488781767820723)
            ·
              refine ⟨17242742249233172651731085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11495161499488781767820723 17242742249233172651731085)
              ·
                refine ⟨6466028343462439744399157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17242742249233172651731085 6466028343462439744399157)
                ·
                  refine ⟨606190157199603726037421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6466028343462439744399157 606190157199603726037421)
                  ·
                    refine ⟨227321308949851397264033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 606190157199603726037421 227321308949851397264033)
                    ·
                      rfl

theorem cell22_664060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_664060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664060 prefixEnd_664060 := by exact prefixLift 664060
  have htrace : WordTrace (prefixWord ++ tailWord_664060) baseStart_664060 baseEnd_664060 := by
    simpa [prefixWord, tailWord_664060, baseEnd_664060] using wordTrace_append hprefix tailTrace_664060
  have hstable : (prefixWord ++ tailWord_664060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664060).length < 2 ^ (prefixWord ++ tailWord_664060).sum := by decide
  have hdescent : baseEnd_664060 < baseStart_664060 := by decide
  rcases family_descends (prefixWord ++ tailWord_664060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664073 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 7]
def baseStart_664073 : Nat := 118140960795 + 664073 * 2 ^ 59
def prefixEnd_664073 : Nat := 4983230072969 + 3 ^ 40 * 664073 * 2
def baseEnd_664073 : Nat := 75775253038507898896331

theorem tailTrace_664073 : CollatzResearch.WordTrace tailWord_664073 prefixEnd_664073 75775253038507898896331 := by
  unfold tailWord_664073
  simp only [CollatzResearch.WordTrace]
  refine ⟨24220732123184410484108873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16147154748789606989405915 24220732123184410484108873)
  ·
    refine ⟨18165549092388307863081655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24220732123184410484108873 18165549092388307863081655)
    ·
      refine ⟨27248323638582461794622483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18165549092388307863081655 27248323638582461794622483)
      ·
        refine ⟨40872485457873692691933725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27248323638582461794622483 40872485457873692691933725)
        ·
          refine ⟨15327182046702634759475147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40872485457873692691933725 15327182046702634759475147)
          ·
            refine ⟨22990773070053952139212721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15327182046702634759475147 22990773070053952139212721)
            ·
              refine ⟨17243079802540464104409541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22990773070053952139212721 17243079802540464104409541)
              ·
                refine ⟨3233077462976337019576789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17243079802540464104409541 3233077462976337019576789)
                ·
                  refine ⟨75775253038507898896331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3233077462976337019576789 75775253038507898896331)
                  ·
                    rfl

theorem cell22_664073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_664073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664073 prefixEnd_664073 := by exact prefixLift 664073
  have htrace : WordTrace (prefixWord ++ tailWord_664073) baseStart_664073 baseEnd_664073 := by
    simpa [prefixWord, tailWord_664073, baseEnd_664073] using wordTrace_append hprefix tailTrace_664073
  have hstable : (prefixWord ++ tailWord_664073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664073).length < 2 ^ (prefixWord ++ tailWord_664073).sum := by decide
  have hdescent : baseEnd_664073 < baseStart_664073 := by decide
  rcases family_descends (prefixWord ++ tailWord_664073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664090 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_664090 : Nat := 118140960795 + 664090 * 2 ^ 59
def prefixEnd_664090 : Nat := 4983230072969 + 3 ^ 40 * 664090 * 2
def baseEnd_664090 : Nat := 75777192854313773004647

theorem tailTrace_664090 : CollatzResearch.WordTrace tailWord_664090 prefixEnd_664090 75777192854313773004647 := by
  unfold tailWord_664090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6055338041030705596869431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16147568109415214924985149 6055338041030705596869431)
  ·
    refine ⟨9083007061546058395304147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6055338041030705596869431 9083007061546058395304147)
    ·
      refine ⟨13624510592319087592956221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9083007061546058395304147 13624510592319087592956221)
      ·
        refine ⟨5109191472119657847358583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13624510592319087592956221 5109191472119657847358583)
        ·
          refine ⟨7663787208179486771037875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5109191472119657847358583 7663787208179486771037875)
          ·
            refine ⟨11495680812269230156556813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663787208179486771037875 11495680812269230156556813)
            ·
              refine ⟨4310880304600961308708805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11495680812269230156556813 4310880304600961308708805)
              ·
                refine ⟨808290057112680245382901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4310880304600961308708805 808290057112680245382901)
                ·
                  refine ⟨75777192854313773004647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 808290057112680245382901 75777192854313773004647)
                  ·
                    rfl

theorem cell22_664090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_664090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664090 prefixEnd_664090 := by exact prefixLift 664090
  have htrace : WordTrace (prefixWord ++ tailWord_664090) baseStart_664090 baseEnd_664090 := by
    simpa [prefixWord, tailWord_664090, baseEnd_664090] using wordTrace_append hprefix tailTrace_664090
  have hstable : (prefixWord ++ tailWord_664090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664090).length < 2 ^ (prefixWord ++ tailWord_664090).sum := by decide
  have hdescent : baseEnd_664090 < baseStart_664090 := by decide
  rcases family_descends (prefixWord ++ tailWord_664090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664120 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_664120 : Nat := 118140960795 + 664120 * 2 ^ 59
def prefixEnd_664120 : Nat := 4983230072969 + 3 ^ 40 * 664120 * 2
def baseEnd_664120 : Nat := 227341848176031240763849

theorem tailTrace_664120 : CollatzResearch.WordTrace tailWord_664120 prefixEnd_664120 227341848176031240763849 := by
  unfold tailWord_664120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12111223177007068755534907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16148297569342758340713209 12111223177007068755534907)
  ·
    refine ⟨18166834765510603133302361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12111223177007068755534907 18166834765510603133302361)
    ·
      refine ⟨13625126074132952349976771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18166834765510603133302361 13625126074132952349976771)
      ·
        refine ⟨20437689111199428524965157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13625126074132952349976771 20437689111199428524965157)
        ·
          refine ⟨3832066708349892848430967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20437689111199428524965157 3832066708349892848430967)
          ·
            refine ⟨5748100062524839272646451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832066708349892848430967 5748100062524839272646451)
            ·
              refine ⟨8622150093787258908969677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5748100062524839272646451 8622150093787258908969677)
              ·
                refine ⟨3233306285170222090863629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8622150093787258908969677 3233306285170222090863629)
                ·
                  refine ⟨1212489856938833284073861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3233306285170222090863629 1212489856938833284073861)
                  ·
                    refine ⟨227341848176031240763849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1212489856938833284073861 227341848176031240763849)
                    ·
                      rfl

theorem cell22_664120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_664120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664120 prefixEnd_664120 := by exact prefixLift 664120
  have htrace : WordTrace (prefixWord ++ tailWord_664120) baseStart_664120 baseEnd_664120 := by
    simpa [prefixWord, tailWord_664120, baseEnd_664120] using wordTrace_append hprefix tailTrace_664120
  have hstable : (prefixWord ++ tailWord_664120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664120).length < 2 ^ (prefixWord ++ tailWord_664120).sum := by decide
  have hdescent : baseEnd_664120 < baseStart_664120 := by decide
  rcases family_descends (prefixWord ++ tailWord_664120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664152 : List Nat := [2, 1, 2, 2, 1, 2, 4, 4, 4]
def baseStart_664152 : Nat := 118140960795 + 664152 * 2 ^ 59
def prefixEnd_664152 : Nat := 4983230072969 + 3 ^ 40 * 664152 * 2
def baseEnd_664152 : Nat := 75784267476664607987917

theorem tailTrace_664152 : CollatzResearch.WordTrace tailWord_664152 prefixEnd_664152 75784267476664607987917 := by
  unfold tailWord_664152
  simp only [CollatzResearch.WordTrace]
  refine ⟨12111806744949103488117355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16149075659932137984156473 12111806744949103488117355)
  ·
    refine ⟨18167710117423655232176033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12111806744949103488117355 18167710117423655232176033)
    ·
      refine ⟨13625782588067741424132025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18167710117423655232176033 13625782588067741424132025)
      ·
        refine ⟨10219336941050806068099019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13625782588067741424132025 10219336941050806068099019)
        ·
          refine ⟨15329005411576209102148529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10219336941050806068099019 15329005411576209102148529)
          ·
            refine ⟨11496754058682156826611397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15329005411576209102148529 11496754058682156826611397)
            ·
              refine ⟨2155641386002904404989637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11496754058682156826611397 2155641386002904404989637)
              ·
                refine ⟨404182759875544575935557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2155641386002904404989637 404182759875544575935557)
                ·
                  refine ⟨75784267476664607987917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404182759875544575935557 75784267476664607987917)
                  ·
                    rfl

theorem cell22_664152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 4].length) (baseStart_664152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664152 prefixEnd_664152 := by exact prefixLift 664152
  have htrace : WordTrace (prefixWord ++ tailWord_664152) baseStart_664152 baseEnd_664152 := by
    simpa [prefixWord, tailWord_664152, baseEnd_664152] using wordTrace_append hprefix tailTrace_664152
  have hstable : (prefixWord ++ tailWord_664152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664152).length < 2 ^ (prefixWord ++ tailWord_664152).sum := by decide
  have hdescent : baseEnd_664152 < baseStart_664152 := by decide
  rcases family_descends (prefixWord ++ tailWord_664152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664240 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_664240 : Nat := 118140960795 + 664240 * 2 ^ 59
def prefixEnd_664240 : Nat := 4983230072969 + 3 ^ 40 * 664240 * 2
def baseEnd_664240 : Nat := 227382926628390927763481

theorem tailTrace_664240 : CollatzResearch.WordTrace tailWord_664240 prefixEnd_664240 227382926628390927763481 := by
  unfold tailWord_664240
  simp only [CollatzResearch.WordTrace]
  refine ⟨12113411556789699002719087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16151215409052932003625449 12113411556789699002719087)
  ·
    refine ⟨18170117335184548504078631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12113411556789699002719087 18170117335184548504078631)
    ·
      refine ⟨27255176002776822756117947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18170117335184548504078631 27255176002776822756117947)
      ·
        refine ⟨40882764004165234134176921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27255176002776822756117947 40882764004165234134176921)
        ·
          refine ⟨30662073003123925600632691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40882764004165234134176921 30662073003123925600632691)
          ·
            refine ⟨45993109504685888400949037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30662073003123925600632691 45993109504685888400949037)
            ·
              refine ⟨17247416064257208150355889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45993109504685888400949037 17247416064257208150355889)
              ·
                refine ⟨12935562048192906112766917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17247416064257208150355889 12935562048192906112766917)
                ·
                  refine ⟨2425417884036169896143797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12935562048192906112766917 2425417884036169896143797)
                  ·
                    refine ⟨227382926628390927763481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2425417884036169896143797 227382926628390927763481)
                    ·
                      rfl

theorem cell22_664240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_664240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664240 prefixEnd_664240 := by exact prefixLift 664240
  have htrace : WordTrace (prefixWord ++ tailWord_664240) baseStart_664240 baseEnd_664240 := by
    simpa [prefixWord, tailWord_664240, baseEnd_664240] using wordTrace_append hprefix tailTrace_664240
  have hstable : (prefixWord ++ tailWord_664240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664240).length < 2 ^ (prefixWord ++ tailWord_664240).sum := by decide
  have hdescent : baseEnd_664240 < baseStart_664240 := by decide
  rcases family_descends (prefixWord ++ tailWord_664240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664274 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_664274 : Nat := 118140960795 + 664274 * 2 ^ 59
def prefixEnd_664274 : Nat := 4983230072969 + 3 ^ 40 * 664274 * 2
def baseEnd_664274 : Nat := 227394565523226172413377

theorem tailTrace_664274 : CollatzResearch.WordTrace tailWord_664274 prefixEnd_664274 227394565523226172413377 := by
  unfold tailWord_664274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057015798864055453043969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16152042130304147874783917 6057015798864055453043969)
  ·
    refine ⟨4542761849148041589782977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6057015798864055453043969 4542761849148041589782977)
    ·
      refine ⟨3407071386861031192337233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4542761849148041589782977 3407071386861031192337233)
      ·
        refine ⟨2555303540145773394252925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3407071386861031192337233 2555303540145773394252925)
        ·
          refine ⟨958238827554665022844847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2555303540145773394252925 958238827554665022844847)
          ·
            refine ⟨1437358241331997534267271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958238827554665022844847 1437358241331997534267271)
            ·
              refine ⟨2156037361997996301400907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437358241331997534267271 2156037361997996301400907)
              ·
                refine ⟨3234056042996994452101361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156037361997996301400907 3234056042996994452101361)
                ·
                  refine ⟨2425542032247745839076021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3234056042996994452101361 2425542032247745839076021)
                  ·
                    refine ⟨227394565523226172413377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2425542032247745839076021 227394565523226172413377)
                    ·
                      rfl

theorem cell22_664274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_664274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664274 prefixEnd_664274 := by exact prefixLift 664274
  have htrace : WordTrace (prefixWord ++ tailWord_664274) baseStart_664274 baseEnd_664274 := by
    simpa [prefixWord, tailWord_664274, baseEnd_664274] using wordTrace_append hprefix tailTrace_664274
  have hstable : (prefixWord ++ tailWord_664274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664274).length < 2 ^ (prefixWord ++ tailWord_664274).sum := by decide
  have hdescent : baseEnd_664274 < baseStart_664274 := by decide
  rcases family_descends (prefixWord ++ tailWord_664274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664287 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 6]
def baseStart_664287 : Nat := 118140960795 + 664287 * 2 ^ 59
def prefixEnd_664287 : Nat := 4983230072969 + 3 ^ 40 * 664287 * 2
def baseEnd_664287 : Nat := 75799671896299490612779

theorem tailTrace_664287 : CollatzResearch.WordTrace tailWord_664287 prefixEnd_664287 75799671896299490612779 := by
  unfold tailWord_664287
  simp only [CollatzResearch.WordTrace]
  refine ⟨24228537344409125032399115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16152358229606083354932743 24228537344409125032399115)
  ·
    refine ⟨36342806016613687548598673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24228537344409125032399115 36342806016613687548598673)
    ·
      refine ⟨27257104512460265661449005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36342806016613687548598673 27257104512460265661449005)
      ·
        refine ⟨10221414192172599623043377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27257104512460265661449005 10221414192172599623043377)
        ·
          refine ⟨7666060644129449717282533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10221414192172599623043377 7666060644129449717282533)
          ·
            refine ⟨1437386370774271821990475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7666060644129449717282533 1437386370774271821990475)
            ·
              refine ⟨2156079556161407732985713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437386370774271821990475 2156079556161407732985713)
              ·
                refine ⟨1617059667121055799739285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2156079556161407732985713 1617059667121055799739285)
                ·
                  refine ⟨75799671896299490612779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1617059667121055799739285 75799671896299490612779)
                  ·
                    rfl

theorem cell22_664287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 6].length) (baseStart_664287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664287 prefixEnd_664287 := by exact prefixLift 664287
  have htrace : WordTrace (prefixWord ++ tailWord_664287) baseStart_664287 baseEnd_664287 := by
    simpa [prefixWord, tailWord_664287, baseEnd_664287] using wordTrace_append hprefix tailTrace_664287
  have hstable : (prefixWord ++ tailWord_664287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664287).length < 2 ^ (prefixWord ++ tailWord_664287).sum := by decide
  have hdescent : baseEnd_664287 < baseStart_664287 := by decide
  rcases family_descends (prefixWord ++ tailWord_664287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664304 : List Nat := [2, 1, 1, 1, 3, 1, 6, 3, 4]
def baseStart_664304 : Nat := 118140960795 + 664304 * 2 ^ 59
def prefixEnd_664304 : Nat := 4983230072969 + 3 ^ 40 * 664304 * 2
def baseEnd_664304 : Nat := 75801611712105364721095

theorem tailTrace_664304 : CollatzResearch.WordTrace tailWord_664304 prefixEnd_664304 75801611712105364721095 := by
  unfold tailWord_664304
  simp only [CollatzResearch.WordTrace]
  refine ⟨12114578692673768467883983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16152771590231691290511977 12114578692673768467883983)
  ·
    refine ⟨18171868039010652701825975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12114578692673768467883983 18171868039010652701825975)
    ·
      refine ⟨27257802058515979052738963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18171868039010652701825975 27257802058515979052738963)
      ·
        refine ⟨40886703087773968579108445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27257802058515979052738963 40886703087773968579108445)
        ·
          refine ⟨15332513657915238217165667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40886703087773968579108445 15332513657915238217165667)
          ·
            refine ⟨22998770486872857325748501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15332513657915238217165667 22998770486872857325748501)
            ·
              refine ⟨1078067366572165187144461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22998770486872857325748501 1078067366572165187144461)
              ·
                refine ⟨404275262464561945179173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1078067366572165187144461 404275262464561945179173)
                ·
                  refine ⟨75801611712105364721095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404275262464561945179173 75801611712105364721095)
                  ·
                    rfl

theorem cell22_664304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 4].length) (baseStart_664304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664304 prefixEnd_664304 := by exact prefixLift 664304
  have htrace : WordTrace (prefixWord ++ tailWord_664304) baseStart_664304 baseEnd_664304 := by
    simpa [prefixWord, tailWord_664304, baseEnd_664304] using wordTrace_append hprefix tailTrace_664304
  have hstable : (prefixWord ++ tailWord_664304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664304).length < 2 ^ (prefixWord ++ tailWord_664304).sum := by decide
  have hdescent : baseEnd_664304 < baseStart_664304 := by decide
  rcases family_descends (prefixWord ++ tailWord_664304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664306 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_664306 : Nat := 118140960795 + 664306 * 2 ^ 59
def prefixEnd_664306 : Nat := 4983230072969 + 3 ^ 40 * 664306 * 2
def baseEnd_664306 : Nat := 227405519777188755613279

theorem tailTrace_664306 : CollatzResearch.WordTrace tailWord_664306 prefixEnd_664306 227405519777188755613279 := by
  unfold tailWord_664306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057307582835072819335193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16152820220893527518227181 6057307582835072819335193)
  ·
    refine ⟨4542980687126304614501395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6057307582835072819335193 4542980687126304614501395)
    ·
      refine ⟨6814471030689456921752093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4542980687126304614501395 6814471030689456921752093)
      ·
        refine ⟨2555426636508546345657035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6814471030689456921752093 2555426636508546345657035)
        ·
          refine ⟨3833139954762819518485553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2555426636508546345657035 3833139954762819518485553)
          ·
            refine ⟨2874854966072114638864165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3833139954762819518485553 2874854966072114638864165)
            ·
              refine ⟨539035306138521494787031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2874854966072114638864165 539035306138521494787031)
              ·
                refine ⟨808552959207782242180547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539035306138521494787031 808552959207782242180547)
                ·
                  refine ⟨1212829438811673363270821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808552959207782242180547 1212829438811673363270821)
                  ·
                    refine ⟨227405519777188755613279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1212829438811673363270821 227405519777188755613279)
                    ·
                      rfl

theorem cell22_664306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_664306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664306 prefixEnd_664306 := by exact prefixLift 664306
  have htrace : WordTrace (prefixWord ++ tailWord_664306) baseStart_664306 baseEnd_664306 := by
    simpa [prefixWord, tailWord_664306, baseEnd_664306] using wordTrace_append hprefix tailTrace_664306
  have hstable : (prefixWord ++ tailWord_664306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664306).length < 2 ^ (prefixWord ++ tailWord_664306).sum := by decide
  have hdescent : baseEnd_664306 < baseStart_664306 := by decide
  rcases family_descends (prefixWord ++ tailWord_664306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664317 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_664317 : Nat := 118140960795 + 664317 * 2 ^ 59
def prefixEnd_664317 : Nat := 4983230072969 + 3 ^ 40 * 664317 * 2
def baseEnd_664317 : Nat := 227409285301988393588245

theorem tailTrace_664317 : CollatzResearch.WordTrace tailWord_664317 prefixEnd_664317 227409285301988393588245 := by
  unfold tailWord_664317
  simp only [CollatzResearch.WordTrace]
  refine ⟨24229631534300440155991205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16153087689533626770660803 24229631534300440155991205)
  ·
    refine ⟨4543055912681332529248351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24229631534300440155991205 4543055912681332529248351)
    ·
      refine ⟨6814583869021998793872527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4543055912681332529248351 6814583869021998793872527)
      ·
        refine ⟨10221875803532998190808791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6814583869021998793872527 10221875803532998190808791)
        ·
          refine ⟨15332813705299497286213187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10221875803532998190808791 15332813705299497286213187)
          ·
            refine ⟨22999220557949245929319781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15332813705299497286213187 22999220557949245929319781)
            ·
              refine ⟨4312353854615483611747459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22999220557949245929319781 4312353854615483611747459)
              ·
                refine ⟨6468530781923225417621189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312353854615483611747459 6468530781923225417621189)
                ·
                  refine ⟨1212849521610604765803973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6468530781923225417621189 1212849521610604765803973)
                  ·
                    refine ⟨227409285301988393588245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1212849521610604765803973 227409285301988393588245)
                    ·
                      rfl

theorem cell22_664317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_664317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664317 prefixEnd_664317 := by exact prefixLift 664317
  have htrace : WordTrace (prefixWord ++ tailWord_664317) baseStart_664317 baseEnd_664317 := by
    simpa [prefixWord, tailWord_664317, baseEnd_664317] using wordTrace_append hprefix tailTrace_664317
  have hstable : (prefixWord ++ tailWord_664317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664317).length < 2 ^ (prefixWord ++ tailWord_664317).sum := by decide
  have hdescent : baseEnd_664317 < baseStart_664317 := by decide
  rcases family_descends (prefixWord ++ tailWord_664317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664392 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_664392 : Nat := 118140960795 + 664392 * 2 ^ 59
def prefixEnd_664392 : Nat := 4983230072969 + 3 ^ 40 * 664392 * 2
def baseEnd_664392 : Nat := 227434959334713197963015

theorem tailTrace_664392 : CollatzResearch.WordTrace tailWord_664392 prefixEnd_664392 227434959334713197963015 := by
  unfold tailWord_664392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12116183504514363982485715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16154911339352485309980953 12116183504514363982485715)
  ·
    refine ⟨18174275256771545973728573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12116183504514363982485715 18174275256771545973728573)
    ·
      refine ⟨6815353221289329740148215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18174275256771545973728573 6815353221289329740148215)
      ·
        refine ⟨10223029831933994610222323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6815353221289329740148215 10223029831933994610222323)
        ·
          refine ⟨15334544747900991915333485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10223029831933994610222323 15334544747900991915333485)
          ·
            refine ⟨5750454280462871968250057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15334544747900991915333485 5750454280462871968250057)
            ·
              refine ⟨4312840710347153976187543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5750454280462871968250057 4312840710347153976187543)
              ·
                refine ⟨6469261065520730964281315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312840710347153976187543 6469261065520730964281315)
                ·
                  refine ⟨9703891598281096446421973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6469261065520730964281315 9703891598281096446421973)
                  ·
                    refine ⟨227434959334713197963015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9703891598281096446421973 227434959334713197963015)
                    ·
                      rfl

theorem cell22_664392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_664392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664392 prefixEnd_664392 := by exact prefixLift 664392
  have htrace : WordTrace (prefixWord ++ tailWord_664392) baseStart_664392 baseEnd_664392 := by
    simpa [prefixWord, tailWord_664392, baseEnd_664392] using wordTrace_append hprefix tailTrace_664392
  have hstable : (prefixWord ++ tailWord_664392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664392).length < 2 ^ (prefixWord ++ tailWord_664392).sum := by decide
  have hdescent : baseEnd_664392 < baseStart_664392 := by decide
  rcases family_descends (prefixWord ++ tailWord_664392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664469 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_664469 : Nat := 118140960795 + 664469 * 2 ^ 59
def prefixEnd_664469 : Nat := 4983230072969 + 3 ^ 40 * 664469 * 2
def baseEnd_664469 : Nat := 227461318008310663787779

theorem tailTrace_664469 : CollatzResearch.WordTrace tailWord_664469 prefixEnd_664469 227461318008310663787779 := by
  unfold tailWord_664469
  simp only [CollatzResearch.WordTrace]
  refine ⟨24235175429749770115524461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16156783619833180077016307 24235175429749770115524461)
  ·
    refine ⟨9088190786156163793321673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24235175429749770115524461 9088190786156163793321673)
    ·
      refine ⟨6816143089617122844991255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9088190786156163793321673 6816143089617122844991255)
      ·
        refine ⟨10224214634425684267486883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6816143089617122844991255 10224214634425684267486883)
        ·
          refine ⟨15336321951638526401230325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10224214634425684267486883 15336321951638526401230325)
          ·
            refine ⟨1437780182966111850115343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15336321951638526401230325 1437780182966111850115343)
            ·
              refine ⟨2156670274449167775173015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437780182966111850115343 2156670274449167775173015)
              ·
                refine ⟨3235005411673751662759523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156670274449167775173015 3235005411673751662759523)
                ·
                  refine ⟨4852508117510627494139285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3235005411673751662759523 4852508117510627494139285)
                  ·
                    refine ⟨227461318008310663787779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4852508117510627494139285 227461318008310663787779)
                    ·
                      rfl

theorem cell22_664469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_664469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664469 prefixEnd_664469 := by exact prefixLift 664469
  have htrace : WordTrace (prefixWord ++ tailWord_664469) baseStart_664469 baseEnd_664469 := by
    simpa [prefixWord, tailWord_664469, baseEnd_664469] using wordTrace_append hprefix tailTrace_664469
  have hstable : (prefixWord ++ tailWord_664469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664469).length < 2 ^ (prefixWord ++ tailWord_664469).sum := by decide
  have hdescent : baseEnd_664469 < baseStart_664469 := by decide
  rcases family_descends (prefixWord ++ tailWord_664469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664638 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_664638 : Nat := 118140960795 + 664638 * 2 ^ 59
def prefixEnd_664638 : Nat := 4983230072969 + 3 ^ 40 * 664638 * 2
def baseEnd_664638 : Nat := 227519170162050556312261

theorem tailTrace_664638 : CollatzResearch.WordTrace tailWord_664638 prefixEnd_664638 227519170162050556312261 := by
  unfold tailWord_664638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3030167420767188997303321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16160892910758341318951045 3030167420767188997303321)
  ·
    refine ⟨2272625565575391747977491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3030167420767188997303321 2272625565575391747977491)
    ·
      refine ⟨3408938348363087621966237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2272625565575391747977491 3408938348363087621966237)
      ·
        refine ⟨1278351880636157858237339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3408938348363087621966237 1278351880636157858237339)
        ·
          refine ⟨1917527820954236787356009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278351880636157858237339 1917527820954236787356009)
          ·
            refine ⟨1438145865715677590517007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1917527820954236787356009 1438145865715677590517007)
            ·
              refine ⟨2157218798573516385775511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438145865715677590517007 2157218798573516385775511)
              ·
                refine ⟨3235828197860274578663267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2157218798573516385775511 3235828197860274578663267)
                ·
                  refine ⟨4853742296790411867994901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3235828197860274578663267 4853742296790411867994901)
                  ·
                    refine ⟨227519170162050556312261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4853742296790411867994901 227519170162050556312261)
                    ·
                      rfl

theorem cell22_664638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_664638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664638 prefixEnd_664638 := by exact prefixLift 664638
  have htrace : WordTrace (prefixWord ++ tailWord_664638) baseStart_664638 baseEnd_664638 := by
    simpa [prefixWord, tailWord_664638, baseEnd_664638] using wordTrace_append hprefix tailTrace_664638
  have hstable : (prefixWord ++ tailWord_664638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664638).length < 2 ^ (prefixWord ++ tailWord_664638).sum := by decide
  have hdescent : baseEnd_664638 < baseStart_664638 := by decide
  rcases family_descends (prefixWord ++ tailWord_664638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664649 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_664649 : Nat := 118140960795 + 664649 * 2 ^ 59
def prefixEnd_664649 : Nat := 4983230072969 + 3 ^ 40 * 664649 * 2
def baseEnd_664649 : Nat := 227522935686850194287227

theorem tailTrace_664649 : CollatzResearch.WordTrace tailWord_664649 prefixEnd_664649 227522935686850194287227 := by
  unfold tailWord_664649
  simp only [CollatzResearch.WordTrace]
  refine ⟨24241740569097660857077001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16161160379398440571384667 24241740569097660857077001)
  ·
    refine ⟨18181305426823245642807751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24241740569097660857077001 18181305426823245642807751)
    ·
      refine ⟨27271958140234868464211627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18181305426823245642807751 27271958140234868464211627)
      ·
        refine ⟨40907937210352302696317441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27271958140234868464211627 40907937210352302696317441)
        ·
          refine ⟨30680952907764227022238081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40907937210352302696317441 30680952907764227022238081)
          ·
            refine ⟨23010714680823170266678561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30680952907764227022238081 23010714680823170266678561)
            ·
              refine ⟨17258036010617377700008921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23010714680823170266678561 17258036010617377700008921)
              ·
                refine ⟨12943527007963033275006691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17258036010617377700008921 12943527007963033275006691)
                ·
                  refine ⟨19415290511944549912510037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12943527007963033275006691 19415290511944549912510037)
                  ·
                    refine ⟨227522935686850194287227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19415290511944549912510037 227522935686850194287227)
                    ·
                      rfl

theorem cell22_664649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_664649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664649 prefixEnd_664649 := by exact prefixLift 664649
  have htrace : WordTrace (prefixWord ++ tailWord_664649) baseStart_664649 baseEnd_664649 := by
    simpa [prefixWord, tailWord_664649, baseEnd_664649] using wordTrace_append hprefix tailTrace_664649
  have hstable : (prefixWord ++ tailWord_664649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664649).length < 2 ^ (prefixWord ++ tailWord_664649).sum := by decide
  have hdescent : baseEnd_664649 < baseStart_664649 := by decide
  rcases family_descends (prefixWord ++ tailWord_664649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664711 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 5, 4]
def baseStart_664711 : Nat := 118140960795 + 664711 * 2 ^ 59
def prefixEnd_664711 : Nat := 4983230072969 + 3 ^ 40 * 664711 * 2
def baseEnd_664711 : Nat := 227544159553902699237037

theorem tailTrace_664711 : CollatzResearch.WordTrace tailWord_664711 prefixEnd_664711 227544159553902699237037 := by
  unfold tailWord_664711
  simp only [CollatzResearch.WordTrace]
  refine ⟨24244001894873045445833987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16162667929915363630555991 24244001894873045445833987)
  ·
    refine ⟨36366002842309568168750981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24244001894873045445833987 36366002842309568168750981)
    ·
      refine ⟨6818625532933044031640809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36366002842309568168750981 6818625532933044031640809)
      ·
        refine ⟨5113969149699783023730607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6818625532933044031640809 5113969149699783023730607)
        ·
          refine ⟨7670953724549674535595911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113969149699783023730607 7670953724549674535595911)
          ·
            refine ⟨11506430586824511803393867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7670953724549674535595911 11506430586824511803393867)
            ·
              refine ⟨17259645880236767705090801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11506430586824511803393867 17259645880236767705090801)
              ·
                refine ⟨12944734410177575778818101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17259645880236767705090801 12944734410177575778818101)
                ·
                  refine ⟨1213568850954147729264197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12944734410177575778818101 1213568850954147729264197)
                  ·
                    refine ⟨227544159553902699237037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1213568850954147729264197 227544159553902699237037)
                    ·
                      rfl

theorem cell22_664711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_664711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664711 prefixEnd_664711 := by exact prefixLift 664711
  have htrace : WordTrace (prefixWord ++ tailWord_664711) baseStart_664711 baseEnd_664711 := by
    simpa [prefixWord, tailWord_664711, baseEnd_664711] using wordTrace_append hprefix tailTrace_664711
  have hstable : (prefixWord ++ tailWord_664711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664711).length < 2 ^ (prefixWord ++ tailWord_664711).sum := by decide
  have hdescent : baseEnd_664711 < baseStart_664711 := by decide
  rcases family_descends (prefixWord ++ tailWord_664711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664770 : List Nat := [3, 5, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_664770 : Nat := 118140960795 + 664770 * 2 ^ 59
def prefixEnd_664770 : Nat := 4983230072969 + 3 ^ 40 * 664770 * 2
def baseEnd_664770 : Nat := 227564356459646212011857

theorem tailTrace_664770 : CollatzResearch.WordTrace tailWord_664770 prefixEnd_664770 227564356459646212011857 := by
  unfold tailWord_664770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6061538450414824630557941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16164102534439532348154509 6061538450414824630557941)
  ·
    refine ⟨568269229726389809114807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6061538450414824630557941 568269229726389809114807)
    ·
      refine ⟨852403844589584713672211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568269229726389809114807 852403844589584713672211)
      ·
        refine ⟨1278605766884377070508317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852403844589584713672211 1278605766884377070508317)
        ·
          refine ⟨479477162581641401440619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1278605766884377070508317 479477162581641401440619)
          ·
            refine ⟨719215743872462102160929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479477162581641401440619 719215743872462102160929)
            ·
              refine ⟨539411807904346576620697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719215743872462102160929 539411807904346576620697)
              ·
                refine ⟨404558855928259932465523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539411807904346576620697 404558855928259932465523)
                ·
                  refine ⟨606838283892389898698285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404558855928259932465523 606838283892389898698285)
                  ·
                    refine ⟨227564356459646212011857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 606838283892389898698285 227564356459646212011857)
                    ·
                      rfl

theorem cell22_664770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_664770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664770 prefixEnd_664770 := by exact prefixLift 664770
  have htrace : WordTrace (prefixWord ++ tailWord_664770) baseStart_664770 baseEnd_664770 := by
    simpa [prefixWord, tailWord_664770, baseEnd_664770] using wordTrace_append hprefix tailTrace_664770
  have hstable : (prefixWord ++ tailWord_664770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664770).length < 2 ^ (prefixWord ++ tailWord_664770).sum := by decide
  have hdescent : baseEnd_664770 < baseStart_664770 := by decide
  rcases family_descends (prefixWord ++ tailWord_664770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664805 : List Nat := [1, 3, 1, 4, 3, 1, 3, 6]
def baseStart_664805 : Nat := 118140960795 + 664805 * 2 ^ 59
def prefixEnd_664805 : Nat := 4983230072969 + 3 ^ 40 * 664805 * 2
def baseEnd_664805 : Nat := 25286259741657531931861

theorem tailTrace_664805 : CollatzResearch.WordTrace tailWord_664805 prefixEnd_664805 25286259741657531931861 := by
  unfold tailWord_664805
  simp only [CollatzResearch.WordTrace]
  refine ⟨24247430356532499499755869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16164953571021666333170579 24247430356532499499755869)
  ·
    refine ⟨9092786383699687312408451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24247430356532499499755869 9092786383699687312408451)
    ·
      refine ⟨13639179575549530968612677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9092786383699687312408451 13639179575549530968612677)
      ·
        refine ⟨2557346170415537056614877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13639179575549530968612677 2557346170415537056614877)
        ·
          refine ⟨959004813905826396230579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2557346170415537056614877 959004813905826396230579)
          ·
            refine ⟨1438507220858739594345869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959004813905826396230579 1438507220858739594345869)
            ·
              refine ⟨539440207822027347879701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1438507220858739594345869 539440207822027347879701)
              ·
                refine ⟨25286259741657531931861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 539440207822027347879701 25286259741657531931861)
                ·
                  rfl

theorem cell22_664805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 6].length) (baseStart_664805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664805 prefixEnd_664805 := by exact prefixLift 664805
  have htrace : WordTrace (prefixWord ++ tailWord_664805) baseStart_664805 baseEnd_664805 := by
    simpa [prefixWord, tailWord_664805, baseEnd_664805] using wordTrace_append hprefix tailTrace_664805
  have hstable : (prefixWord ++ tailWord_664805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664805).length < 2 ^ (prefixWord ++ tailWord_664805).sum := by decide
  have hdescent : baseEnd_664805 < baseStart_664805 := by decide
  rcases family_descends (prefixWord ++ tailWord_664805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
