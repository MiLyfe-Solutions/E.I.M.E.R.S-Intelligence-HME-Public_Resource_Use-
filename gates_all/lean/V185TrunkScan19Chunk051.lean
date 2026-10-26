import V185TrunkScan19Chunk050

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_511589 : List Nat := [1, 3, 1, 3, 3, 1, 4, 3]
def baseStart_511589 : Nat := 118140960795 + 511589 * 2 ^ 59
def prefixEnd_511589 : Nat := 4983230072969 + 3 ^ 40 * 511589 * 2
def baseEnd_511589 : Nat := 155668773068506156672445

theorem tailTrace_511589 : CollatzResearch.WordTrace tailWord_511589 prefixEnd_511589 155668773068506156672445 := by
  unfold tailWord_511589
  simp only [CollatzResearch.WordTrace]
  refine ⟨18659183743607900290233821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12439455829071933526822547 18659183743607900290233821)
  ·
    refine ⟨6997193903852962608837683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18659183743607900290233821 6997193903852962608837683)
    ·
      refine ⟨10495790855779443913256525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6997193903852962608837683 10495790855779443913256525)
      ·
        refine ⟨3935921570917291467471197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10495790855779443913256525 3935921570917291467471197)
        ·
          refine ⟨1475970589093984300301699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3935921570917291467471197 1475970589093984300301699)
          ·
            refine ⟨2213955883640976450452549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475970589093984300301699 2213955883640976450452549)
            ·
              refine ⟨415116728182683084459853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2213955883640976450452549 415116728182683084459853)
              ·
                refine ⟨155668773068506156672445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415116728182683084459853 155668773068506156672445)
                ·
                  rfl

theorem cell19_511589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 3].length) (baseStart_511589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511589 prefixEnd_511589 := by exact prefixLift 511589
  have htrace : WordTrace (prefixWord ++ tailWord_511589) baseStart_511589 baseEnd_511589 := by
    simpa [prefixWord, tailWord_511589, baseEnd_511589] using wordTrace_append hprefix tailTrace_511589
  have hstable : (prefixWord ++ tailWord_511589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511589).length < 2 ^ (prefixWord ++ tailWord_511589).sum := by decide
  have hdescent : baseEnd_511589 < baseStart_511589 := by decide
  rcases family_descends (prefixWord ++ tailWord_511589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511646 : List Nat := [4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_511646 : Nat := 118140960795 + 511646 * 2 ^ 59
def prefixEnd_511646 : Nat := 4983230072969 + 3 ^ 40 * 511646 * 2
def baseEnd_511646 : Nat := 155686117303946913405623

theorem tailTrace_511646 : CollatzResearch.WordTrace tailWord_511646 prefixEnd_511646 155686117303946913405623 := by
  unfold tailWord_511646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2332657838050174878132349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12440841802934266016705861 2332657838050174878132349)
  ·
    refine ⟨874746689268815579299631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2332657838050174878132349 874746689268815579299631)
    ·
      refine ⟨1312120033903223368949447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 874746689268815579299631 1312120033903223368949447)
      ·
        refine ⟨1968180050854835053424171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312120033903223368949447 1968180050854835053424171)
        ·
          refine ⟨2952270076282252580136257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968180050854835053424171 2952270076282252580136257)
          ·
            refine ⟨2214202557211689435102193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2952270076282252580136257 2214202557211689435102193)
            ·
              refine ⟨1660651917908767076326645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2214202557211689435102193 1660651917908767076326645)
              ·
                refine ⟨155686117303946913405623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1660651917908767076326645 155686117303946913405623)
                ·
                  rfl

theorem cell19_511646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_511646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511646 prefixEnd_511646 := by exact prefixLift 511646
  have htrace : WordTrace (prefixWord ++ tailWord_511646) baseStart_511646 baseEnd_511646 := by
    simpa [prefixWord, tailWord_511646, baseEnd_511646] using wordTrace_append hprefix tailTrace_511646
  have hstable : (prefixWord ++ tailWord_511646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511646).length < 2 ^ (prefixWord ++ tailWord_511646).sum := by decide
  have hdescent : baseEnd_511646 < baseStart_511646 := by decide
  rcases family_descends (prefixWord ++ tailWord_511646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511648 : List Nat := [2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_511648 : Nat := 118140960795 + 511648 * 2 ^ 59
def prefixEnd_511648 : Nat := 4983230072969 + 3 ^ 40 * 511648 * 2
def baseEnd_511648 : Nat := 155686725873611501361173

theorem tailTrace_511648 : CollatzResearch.WordTrace tailWord_511648 prefixEnd_511648 155686725873611501361173 := by
  unfold tailWord_511648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330667825197076683315799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12440890433596102244421065 9330667825197076683315799)
  ·
    refine ⟨13996001737795615024973699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9330667825197076683315799 13996001737795615024973699)
    ·
      refine ⟨20994002606693422537460549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13996001737795615024973699 20994002606693422537460549)
      ·
        refine ⟨3936375488755016725773853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20994002606693422537460549 3936375488755016725773853)
        ·
          refine ⟨1476140808283131272165195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3936375488755016725773853 1476140808283131272165195)
          ·
            refine ⟨2214211212424696908247793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476140808283131272165195 2214211212424696908247793)
            ·
              refine ⟨1660658409318522681185845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2214211212424696908247793 1660658409318522681185845)
              ·
                refine ⟨155686725873611501361173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1660658409318522681185845 155686725873611501361173)
                ·
                  rfl

theorem cell19_511648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_511648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511648 prefixEnd_511648 := by exact prefixLift 511648
  have htrace : WordTrace (prefixWord ++ tailWord_511648) baseStart_511648 baseEnd_511648 := by
    simpa [prefixWord, tailWord_511648, baseEnd_511648] using wordTrace_append hprefix tailTrace_511648
  have hstable : (prefixWord ++ tailWord_511648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511648).length < 2 ^ (prefixWord ++ tailWord_511648).sum := by decide
  have hdescent : baseEnd_511648 < baseStart_511648 := by decide
  rcases family_descends (prefixWord ++ tailWord_511648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511750 : List Nat := [6, 2, 2, 1, 1, 2, 2, 3]
def baseStart_511750 : Nat := 118140960795 + 511750 * 2 ^ 59
def prefixEnd_511750 : Nat := 4983230072969 + 3 ^ 40 * 511750 * 2
def baseEnd_511750 : Nat := 155717762926505487094229

theorem tailTrace_511750 : CollatzResearch.WordTrace tailWord_511750 prefixEnd_511750 155717762926505487094229 := by
  unfold tailWord_511750
  simp only [CollatzResearch.WordTrace]
  refine ⟨583282996750769524588897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12443370597349749857896469 583282996750769524588897)
  ·
    refine ⟨437462247563077143441673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 583282996750769524588897 437462247563077143441673)
    ·
      refine ⟨328096685672307857581255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437462247563077143441673 328096685672307857581255)
      ·
        refine ⟨492145028508461786371883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328096685672307857581255 492145028508461786371883)
        ·
          refine ⟨738217542762692679557825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492145028508461786371883 738217542762692679557825)
          ·
            refine ⟨553663157072019509668369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738217542762692679557825 553663157072019509668369)
            ·
              refine ⟨415247367804014632251277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553663157072019509668369 415247367804014632251277)
              ·
                refine ⟨155717762926505487094229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415247367804014632251277 155717762926505487094229)
                ·
                  rfl

theorem cell19_511750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_511750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511750 prefixEnd_511750 := by exact prefixLift 511750
  have htrace : WordTrace (prefixWord ++ tailWord_511750) baseStart_511750 baseEnd_511750 := by
    simpa [prefixWord, tailWord_511750, baseEnd_511750] using wordTrace_append hprefix tailTrace_511750
  have hstable : (prefixWord ++ tailWord_511750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511750).length < 2 ^ (prefixWord ++ tailWord_511750).sum := by decide
  have hdescent : baseEnd_511750 < baseStart_511750 := by decide
  rcases family_descends (prefixWord ++ tailWord_511750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511781 : List Nat := [1, 3, 1, 2, 3, 4, 5]
def baseStart_511781 : Nat := 118140960795 + 511781 * 2 ^ 59
def prefixEnd_511781 : Nat := 4983230072969 + 3 ^ 40 * 511781 * 2
def baseEnd_511781 : Nat := 51909065252102200135085

theorem tailTrace_511781 : CollatzResearch.WordTrace tailWord_511781 prefixEnd_511781 51909065252102200135085 := by
  unfold tailWord_511781
  simp only [CollatzResearch.WordTrace]
  refine ⟨18666186558912317081223197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12444124372608211387482131 18666186558912317081223197)
  ·
    refine ⟨6999819959592118905458699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18666186558912317081223197 6999819959592118905458699)
    ·
      refine ⟨10499729939388178358188049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6999819959592118905458699 10499729939388178358188049)
      ·
        refine ⟨7874797454541133768641037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10499729939388178358188049 7874797454541133768641037)
        ·
          refine ⟨2953049045452925163240389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7874797454541133768641037 2953049045452925163240389)
          ·
            refine ⟨553696696022423468107573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2953049045452925163240389 553696696022423468107573)
            ·
              refine ⟨51909065252102200135085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 553696696022423468107573 51909065252102200135085)
              ·
                rfl

theorem cell19_511781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_511781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511781 prefixEnd_511781 := by exact prefixLift 511781
  have htrace : WordTrace (prefixWord ++ tailWord_511781) baseStart_511781 baseEnd_511781 := by
    simpa [prefixWord, tailWord_511781, baseEnd_511781] using wordTrace_append hprefix tailTrace_511781
  have hstable : (prefixWord ++ tailWord_511781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511781).length < 2 ^ (prefixWord ++ tailWord_511781).sum := by decide
  have hdescent : baseEnd_511781 < baseStart_511781 := by decide
  rcases family_descends (prefixWord ++ tailWord_511781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511798 : List Nat := [5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_511798 : Nat := 118140960795 + 511798 * 2 ^ 59
def prefixEnd_511798 : Nat := 4983230072969 + 3 ^ 40 * 511798 * 2
def baseEnd_511798 : Nat := 155732368598455598027431

theorem tailTrace_511798 : CollatzResearch.WordTrace tailWord_511798 prefixEnd_511798 155732368598455598027431 := by
  unfold tailWord_511798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166675412490670561537003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12444537733233819323061365 1166675412490670561537003)
  ·
    refine ⟨1750013118736005842305505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1166675412490670561537003 1750013118736005842305505)
    ·
      refine ⟨1312509839052004381729129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1750013118736005842305505 1312509839052004381729129)
      ·
        refine ⟨984382379289003286296847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1312509839052004381729129 984382379289003286296847)
        ·
          refine ⟨1476573568933504929445271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984382379289003286296847 1476573568933504929445271)
          ·
            refine ⟨2214860353400257394167907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476573568933504929445271 2214860353400257394167907)
            ·
              refine ⟨3322290530100386091251861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214860353400257394167907 3322290530100386091251861)
              ·
                refine ⟨155732368598455598027431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3322290530100386091251861 155732368598455598027431)
                ·
                  rfl

theorem cell19_511798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_511798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511798 prefixEnd_511798 := by exact prefixLift 511798
  have htrace : WordTrace (prefixWord ++ tailWord_511798) baseStart_511798 baseEnd_511798 := by
    simpa [prefixWord, tailWord_511798, baseEnd_511798] using wordTrace_append hprefix tailTrace_511798
  have hstable : (prefixWord ++ tailWord_511798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511798).length < 2 ^ (prefixWord ++ tailWord_511798).sum := by decide
  have hdescent : baseEnd_511798 < baseStart_511798 := by decide
  rcases family_descends (prefixWord ++ tailWord_511798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511800 : List Nat := [2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_511800 : Nat := 118140960795 + 511800 * 2 ^ 59
def prefixEnd_511800 : Nat := 4983230072969 + 3 ^ 40 * 511800 * 2
def baseEnd_511800 : Nat := 155732977168120185982981

theorem tailTrace_511800 : CollatzResearch.WordTrace tailWord_511800 prefixEnd_511800 155732977168120185982981 := by
  unfold tailWord_511800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9333439772921741663082427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12444586363895655550776569 9333439772921741663082427)
  ·
    refine ⟨14000159659382612494623641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9333439772921741663082427 14000159659382612494623641)
    ·
      refine ⟨10500119744536959370967731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14000159659382612494623641 10500119744536959370967731)
      ·
        refine ⟨15750179616805439056451597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10500119744536959370967731 15750179616805439056451597)
        ·
          refine ⟨5906317356302039646169349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15750179616805439056451597 5906317356302039646169349)
          ·
            refine ⟨1107434504306632433656753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5906317356302039646169349 1107434504306632433656753)
            ·
              refine ⟨830575878229974325242565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107434504306632433656753 830575878229974325242565)
              ·
                refine ⟨155732977168120185982981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 830575878229974325242565 155732977168120185982981)
                ·
                  rfl

theorem cell19_511800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_511800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511800 prefixEnd_511800 := by exact prefixLift 511800
  have htrace : WordTrace (prefixWord ++ tailWord_511800) baseStart_511800 baseEnd_511800 := by
    simpa [prefixWord, tailWord_511800, baseEnd_511800] using wordTrace_append hprefix tailTrace_511800
  have hstable : (prefixWord ++ tailWord_511800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511800).length < 2 ^ (prefixWord ++ tailWord_511800).sum := by decide
  have hdescent : baseEnd_511800 < baseStart_511800 := by decide
  rcases family_descends (prefixWord ++ tailWord_511800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511836 : List Nat := [2, 2, 4, 2, 3, 6]
def baseStart_511836 : Nat := 118140960795 + 511836 * 2 ^ 59
def prefixEnd_511836 : Nat := 4983230072969 + 3 ^ 40 * 511836 * 2
def baseEnd_511836 : Nat := 17304881269120307686987

theorem tailTrace_511836 : CollatzResearch.WordTrace tailWord_511836 prefixEnd_511836 17304881269120307686987 := by
  unfold tailWord_511836
  simp only [CollatzResearch.WordTrace]
  refine ⟨9334096286856530737237681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12445461715808707649650241 9334096286856530737237681)
  ·
    refine ⟨7000572215142398052928261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9334096286856530737237681 7000572215142398052928261)
    ·
      refine ⟨1312607290339199634924049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7000572215142398052928261 1312607290339199634924049)
      ·
        refine ⟨984455467754399726193037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1312607290339199634924049 984455467754399726193037)
        ·
          refine ⟨369170800407899897322389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 984455467754399726193037 369170800407899897322389)
          ·
            refine ⟨17304881269120307686987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 369170800407899897322389 17304881269120307686987)
            ·
              rfl

theorem cell19_511836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 6].length) (baseStart_511836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511836 prefixEnd_511836 := by exact prefixLift 511836
  have htrace : WordTrace (prefixWord ++ tailWord_511836) baseStart_511836 baseEnd_511836 := by
    simpa [prefixWord, tailWord_511836, baseEnd_511836] using wordTrace_append hprefix tailTrace_511836
  have hstable : (prefixWord ++ tailWord_511836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511836).length < 2 ^ (prefixWord ++ tailWord_511836).sum := by decide
  have hdescent : baseEnd_511836 < baseStart_511836 := by decide
  rcases family_descends (prefixWord ++ tailWord_511836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511838 : List Nat := [4, 4, 11]
def baseStart_511838 : Nat := 118140960795 + 511838 * 2 ^ 59
def prefixEnd_511838 : Nat := 4983230072969 + 3 ^ 40 * 511838 * 2
def baseEnd_511838 : Nat := 640924032887849206331

theorem tailTrace_511838 : CollatzResearch.WordTrace tailWord_511838 prefixEnd_511838 640924032887849206331 := by
  unfold tailWord_511838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333533189963226977006021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12445510346470543877365445 2333533189963226977006021)
  ·
    refine ⟨437537473118105058188629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2333533189963226977006021 437537473118105058188629)
    ·
      refine ⟨640924032887849206331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 11 437537473118105058188629 640924032887849206331)
      ·
        rfl

theorem cell19_511838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 11].length) (baseStart_511838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511838 prefixEnd_511838 := by exact prefixLift 511838
  have htrace : WordTrace (prefixWord ++ tailWord_511838) baseStart_511838 baseEnd_511838 := by
    simpa [prefixWord, tailWord_511838, baseEnd_511838] using wordTrace_append hprefix tailTrace_511838
  have hstable : (prefixWord ++ tailWord_511838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511838).length < 2 ^ (prefixWord ++ tailWord_511838).sum := by decide
  have hdescent : baseEnd_511838 < baseStart_511838 := by decide
  rcases family_descends (prefixWord ++ tailWord_511838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511840 : List Nat := [2, 1, 1, 3, 3, 9]
def baseStart_511840 : Nat := 118140960795 + 511840 * 2 ^ 59
def prefixEnd_511840 : Nat := 4983230072969 + 3 ^ 40 * 511840 * 2
def baseEnd_511840 : Nat := 17305016506823549454887

theorem tailTrace_511840 : CollatzResearch.WordTrace tailWord_511840 prefixEnd_511840 17305016506823549454887 := by
  unfold tailWord_511840
  simp only [CollatzResearch.WordTrace]
  refine ⟨9334169232849285078810487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12445558977132380105080649 9334169232849285078810487)
  ·
    refine ⟨14001253849273927618215731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9334169232849285078810487 14001253849273927618215731)
    ·
      refine ⟨21001880773910891427323597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14001253849273927618215731 21001880773910891427323597)
      ·
        refine ⟨7875705290216584285246349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21001880773910891427323597 7875705290216584285246349)
        ·
          refine ⟨2953389483831219106967381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7875705290216584285246349 2953389483831219106967381)
          ·
            refine ⟨17305016506823549454887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2953389483831219106967381 17305016506823549454887)
            ·
              rfl

theorem cell19_511840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 9].length) (baseStart_511840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511840 prefixEnd_511840 := by exact prefixLift 511840
  have htrace : WordTrace (prefixWord ++ tailWord_511840) baseStart_511840 baseEnd_511840 := by
    simpa [prefixWord, tailWord_511840, baseEnd_511840] using wordTrace_append hprefix tailTrace_511840
  have hstable : (prefixWord ++ tailWord_511840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511840).length < 2 ^ (prefixWord ++ tailWord_511840).sum := by decide
  have hdescent : baseEnd_511840 < baseStart_511840 := by decide
  rcases family_descends (prefixWord ++ tailWord_511840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511933 : List Nat := [1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_511933 : Nat := 118140960795 + 511933 * 2 ^ 59
def prefixEnd_511933 : Nat := 4983230072969 + 3 ^ 40 * 511933 * 2
def baseEnd_511933 : Nat := 155773447050815285027063

theorem tailTrace_511933 : CollatzResearch.WordTrace tailWord_511933 prefixEnd_511933 155773447050815285027063 := by
  unfold tailWord_511933
  simp only [CollatzResearch.WordTrace]
  refine ⟨18671730454361647040756453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12447820302907764693837635 18671730454361647040756453)
  ·
    refine ⟨3500949460192808820141835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18671730454361647040756453 3500949460192808820141835)
    ·
      refine ⟨5251424190289213230212753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500949460192808820141835 5251424190289213230212753)
      ·
        refine ⟨3938568142716909922659565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5251424190289213230212753 3938568142716909922659565)
        ·
          refine ⟨1476963053518841220997337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3938568142716909922659565 1476963053518841220997337)
          ·
            refine ⟨1107722290139130915748003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1476963053518841220997337 1107722290139130915748003)
            ·
              refine ⟨1661583435208696373622005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107722290139130915748003 1661583435208696373622005)
              ·
                refine ⟨155773447050815285027063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1661583435208696373622005 155773447050815285027063)
                ·
                  rfl

theorem cell19_511933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_511933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511933 prefixEnd_511933 := by exact prefixLift 511933
  have htrace : WordTrace (prefixWord ++ tailWord_511933) baseStart_511933 baseEnd_511933 := by
    simpa [prefixWord, tailWord_511933, baseEnd_511933] using wordTrace_append hprefix tailTrace_511933
  have hstable : (prefixWord ++ tailWord_511933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511933).length < 2 ^ (prefixWord ++ tailWord_511933).sum := by decide
  have hdescent : baseEnd_511933 < baseStart_511933 := by decide
  rcases family_descends (prefixWord ++ tailWord_511933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511935 : List Nat := [1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_511935 : Nat := 118140960795 + 511935 * 2 ^ 59
def prefixEnd_511935 : Nat := 4983230072969 + 3 ^ 40 * 511935 * 2
def baseEnd_511935 : Nat := 155774055620479872982613

theorem tailTrace_511935 : CollatzResearch.WordTrace tailWord_511935 prefixEnd_511935 155774055620479872982613 := by
  unfold tailWord_511935
  simp only [CollatzResearch.WordTrace]
  refine ⟨18671803400354401382329259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12447868933569600921552839 18671803400354401382329259)
  ·
    refine ⟨28007705100531602073493889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18671803400354401382329259 28007705100531602073493889)
    ·
      refine ⟨21005778825398701555120417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28007705100531602073493889 21005778825398701555120417)
      ·
        refine ⟨15754334119049026166340313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21005778825398701555120417 15754334119049026166340313)
        ·
          refine ⟨11815750589286769624755235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15754334119049026166340313 11815750589286769624755235)
          ·
            refine ⟨17723625883930154437132853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11815750589286769624755235 17723625883930154437132853)
            ·
              refine ⟨1661589926618451978481205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17723625883930154437132853 1661589926618451978481205)
              ·
                refine ⟨155774055620479872982613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1661589926618451978481205 155774055620479872982613)
                ·
                  rfl

theorem cell19_511935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_511935 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511935 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511935 prefixEnd_511935 := by exact prefixLift 511935
  have htrace : WordTrace (prefixWord ++ tailWord_511935) baseStart_511935 baseEnd_511935 := by
    simpa [prefixWord, tailWord_511935, baseEnd_511935] using wordTrace_append hprefix tailTrace_511935
  have hstable : (prefixWord ++ tailWord_511935).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511935).length < 2 ^ (prefixWord ++ tailWord_511935).sum := by decide
  have hdescent : baseEnd_511935 < baseStart_511935 := by decide
  rcases family_descends (prefixWord ++ tailWord_511935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511971 : List Nat := [1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_511971 : Nat := 118140960795 + 511971 * 2 ^ 59
def prefixEnd_511971 : Nat := 4983230072969 + 3 ^ 40 * 511971 * 2
def baseEnd_511971 : Nat := 155785009874442456182515

theorem tailTrace_511971 : CollatzResearch.WordTrace tailWord_511971 prefixEnd_511971 155785009874442456182515 := by
  unfold tailWord_511971
  simp only [CollatzResearch.WordTrace]
  refine ⟨18673116428223979530639767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12448744285482653020426511 18673116428223979530639767)
  ·
    refine ⟨28009674642335969295959651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18673116428223979530639767 28009674642335969295959651)
    ·
      refine ⟨42014511963503953943939477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28009674642335969295959651 42014511963503953943939477)
      ·
        refine ⟨1969430248289247841122163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42014511963503953943939477 1969430248289247841122163)
        ·
          refine ⟨2954145372433871761683245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969430248289247841122163 2954145372433871761683245)
          ·
            refine ⟨1107804514662701910631217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2954145372433871761683245 1107804514662701910631217)
            ·
              refine ⟨830853385997026432973413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107804514662701910631217 830853385997026432973413)
              ·
                refine ⟨155785009874442456182515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 830853385997026432973413 155785009874442456182515)
                ·
                  rfl

theorem cell19_511971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_511971 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511971 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511971 prefixEnd_511971 := by exact prefixLift 511971
  have htrace : WordTrace (prefixWord ++ tailWord_511971) baseStart_511971 baseEnd_511971 := by
    simpa [prefixWord, tailWord_511971, baseEnd_511971] using wordTrace_append hprefix tailTrace_511971
  have hstable : (prefixWord ++ tailWord_511971).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511971).length < 2 ^ (prefixWord ++ tailWord_511971).sum := by decide
  have hdescent : baseEnd_511971 < baseStart_511971 := by decide
  rcases family_descends (prefixWord ++ tailWord_511971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511992 : List Nat := [2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_511992 : Nat := 118140960795 + 511992 * 2 ^ 59
def prefixEnd_511992 : Nat := 4983230072969 + 3 ^ 40 * 511992 * 2
def baseEnd_511992 : Nat := 155791399855920629715791

theorem tailTrace_511992 : CollatzResearch.WordTrace tailWord_511992 prefixEnd_511992 155791399855920629715791 := by
  unfold tailWord_511992
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336941180573950058577115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12449254907431933411436153 9336941180573950058577115)
  ·
    refine ⟨14005411770860925087865673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9336941180573950058577115 14005411770860925087865673)
    ·
      refine ⟨10504058828145693815899255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14005411770860925087865673 10504058828145693815899255)
      ·
        refine ⟨15756088242218540723848883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10504058828145693815899255 15756088242218540723848883)
        ·
          refine ⟨23634132363327811085773325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15756088242218540723848883 23634132363327811085773325)
          ·
            refine ⟨8862799636247929157164997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23634132363327811085773325 8862799636247929157164997)
            ·
              refine ⟨1661774931796486716968437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8862799636247929157164997 1661774931796486716968437)
              ·
                refine ⟨155791399855920629715791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1661774931796486716968437 155791399855920629715791)
                ·
                  rfl

theorem cell19_511992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_511992 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_511992 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_511992 prefixEnd_511992 := by exact prefixLift 511992
  have htrace : WordTrace (prefixWord ++ tailWord_511992) baseStart_511992 baseEnd_511992 := by
    simpa [prefixWord, tailWord_511992, baseEnd_511992] using wordTrace_append hprefix tailTrace_511992
  have hstable : (prefixWord ++ tailWord_511992).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511992).length < 2 ^ (prefixWord ++ tailWord_511992).sum := by decide
  have hdescent : baseEnd_511992 < baseStart_511992 := by decide
  rcases family_descends (prefixWord ++ tailWord_511992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512028 : List Nat := [2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_512028 : Nat := 118140960795 + 512028 * 2 ^ 59
def prefixEnd_512028 : Nat := 4983230072969 + 3 ^ 40 * 512028 * 2
def baseEnd_512028 : Nat := 155802354109883212915693

theorem tailTrace_512028 : CollatzResearch.WordTrace tailWord_512028 prefixEnd_512028 155802354109883212915693 := by
  unfold tailWord_512028
  simp only [CollatzResearch.WordTrace]
  refine ⟨9337597694508739132732369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12450130259344985510309825 9337597694508739132732369)
  ·
    refine ⟨7003198270881554349549277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9337597694508739132732369 7003198270881554349549277)
    ·
      refine ⟨2626199351580582881080979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7003198270881554349549277 2626199351580582881080979)
      ·
        refine ⟨3939299027370874321621469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2626199351580582881080979 3939299027370874321621469)
        ·
          refine ⟨1477237135264077870608051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3939299027370874321621469 1477237135264077870608051)
          ·
            refine ⟨2215855702896116805912077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477237135264077870608051 2215855702896116805912077)
            ·
              refine ⟨830945888586043802217029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2215855702896116805912077 830945888586043802217029)
              ·
                refine ⟨155802354109883212915693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 830945888586043802217029 155802354109883212915693)
                ·
                  rfl

theorem cell19_512028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_512028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512028 prefixEnd_512028 := by exact prefixLift 512028
  have htrace : WordTrace (prefixWord ++ tailWord_512028) baseStart_512028 baseEnd_512028 := by
    simpa [prefixWord, tailWord_512028, baseEnd_512028] using wordTrace_append hprefix tailTrace_512028
  have hstable : (prefixWord ++ tailWord_512028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512028).length < 2 ^ (prefixWord ++ tailWord_512028).sum := by decide
  have hdescent : baseEnd_512028 < baseStart_512028 := by decide
  rcases family_descends (prefixWord ++ tailWord_512028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512098 : List Nat := [3, 3, 2, 2, 3, 1, 2, 3]
def baseStart_512098 : Nat := 118140960795 + 512098 * 2 ^ 59
def prefixEnd_512098 : Nat := 4983230072969 + 3 ^ 40 * 512098 * 2
def baseEnd_512098 : Nat := 155823654048143791359947

theorem tailTrace_512098 : CollatzResearch.WordTrace tailWord_512098 prefixEnd_512098 155823654048143791359947 := by
  unfold tailWord_512098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669437124690970055128237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12451832332509253480341965 4669437124690970055128237)
  ·
    refine ⟨1751038921759113770673089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4669437124690970055128237 1751038921759113770673089)
    ·
      refine ⟨1313279191319335328004817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1751038921759113770673089 1313279191319335328004817)
      ·
        refine ⟨984959393489501496003613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1313279191319335328004817 984959393489501496003613)
        ·
          refine ⟨369359772558563061001355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 984959393489501496003613 369359772558563061001355)
          ·
            refine ⟨554039658837844591502033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369359772558563061001355 554039658837844591502033)
            ·
              refine ⟨415529744128383443626525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554039658837844591502033 415529744128383443626525)
              ·
                refine ⟨155823654048143791359947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415529744128383443626525 155823654048143791359947)
                ·
                  rfl

theorem cell19_512098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_512098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512098 prefixEnd_512098 := by exact prefixLift 512098
  have htrace : WordTrace (prefixWord ++ tailWord_512098) baseStart_512098 baseEnd_512098 := by
    simpa [prefixWord, tailWord_512098, baseEnd_512098] using wordTrace_append hprefix tailTrace_512098
  have hstable : (prefixWord ++ tailWord_512098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512098).length < 2 ^ (prefixWord ++ tailWord_512098).sum := by decide
  have hdescent : baseEnd_512098 < baseStart_512098 := by decide
  rcases family_descends (prefixWord ++ tailWord_512098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512125 : List Nat := [1, 4, 1, 1, 3, 2, 7]
def baseStart_512125 : Nat := 118140960795 + 512125 * 2 ^ 59
def prefixEnd_512125 : Nat := 4983230072969 + 3 ^ 40 * 512125 * 2
def baseEnd_512125 : Nat := 51943956579538576253291

theorem tailTrace_512125 : CollatzResearch.WordTrace tailWord_512125 prefixEnd_512125 51943956579538576253291 := by
  unfold tailWord_512125
  simp only [CollatzResearch.WordTrace]
  refine ⟨18678733269666063831745829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12452488846444042554497219 18678733269666063831745829)
  ·
    refine ⟨3502262488062386968452343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18678733269666063831745829 3502262488062386968452343)
    ·
      refine ⟨5253393732093580452678515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502262488062386968452343 5253393732093580452678515)
      ·
        refine ⟨7880090598140370679017773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5253393732093580452678515 7880090598140370679017773)
        ·
          refine ⟨2955033974302639004631665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7880090598140370679017773 2955033974302639004631665)
          ·
            refine ⟨2216275480726979253473749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2955033974302639004631665 2216275480726979253473749)
            ·
              refine ⟨51943956579538576253291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2216275480726979253473749 51943956579538576253291)
              ·
                rfl

theorem cell19_512125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_512125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512125 prefixEnd_512125 := by exact prefixLift 512125
  have htrace : WordTrace (prefixWord ++ tailWord_512125) baseStart_512125 baseEnd_512125 := by
    simpa [prefixWord, tailWord_512125, baseEnd_512125] using wordTrace_append hprefix tailTrace_512125
  have hstable : (prefixWord ++ tailWord_512125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512125).length < 2 ^ (prefixWord ++ tailWord_512125).sum := by decide
  have hdescent : baseEnd_512125 < baseStart_512125 := by decide
  rcases family_descends (prefixWord ++ tailWord_512125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512144 : List Nat := [2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_512144 : Nat := 118140960795 + 512144 * 2 ^ 59
def prefixEnd_512144 : Nat := 4983230072969 + 3 ^ 40 * 512144 * 2
def baseEnd_512144 : Nat := 155837651150429314337599

theorem tailTrace_512144 : CollatzResearch.WordTrace tailWord_512144 prefixEnd_512144 155837651150429314337599 := by
  unfold tailWord_512144
  simp only [CollatzResearch.WordTrace]
  refine ⟨9339713128298615038343743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12452950837731486717791657 9339713128298615038343743)
  ·
    refine ⟨14009569692447922557515615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9339713128298615038343743 14009569692447922557515615)
    ·
      refine ⟨21014354538671883836273423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14009569692447922557515615 21014354538671883836273423)
      ·
        refine ⟨31521531808007825754410135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21014354538671883836273423 31521531808007825754410135)
        ·
          refine ⟨47282297712011738631615203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31521531808007825754410135 47282297712011738631615203)
          ·
            refine ⟨70923446568017607947422805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47282297712011738631615203 70923446568017607947422805)
            ·
              refine ⟨831134139468956343133861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 70923446568017607947422805 831134139468956343133861)
              ·
                refine ⟨155837651150429314337599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831134139468956343133861 155837651150429314337599)
                ·
                  rfl

theorem cell19_512144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_512144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512144 prefixEnd_512144 := by exact prefixLift 512144
  have htrace : WordTrace (prefixWord ++ tailWord_512144) baseStart_512144 baseEnd_512144 := by
    simpa [prefixWord, tailWord_512144, baseEnd_512144] using wordTrace_append hprefix tailTrace_512144
  have hstable : (prefixWord ++ tailWord_512144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512144).length < 2 ^ (prefixWord ++ tailWord_512144).sum := by decide
  have hdescent : baseEnd_512144 < baseStart_512144 := by decide
  rcases family_descends (prefixWord ++ tailWord_512144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512214 : List Nat := [5, 2, 1, 2, 1, 2, 3, 3]
def baseStart_512214 : Nat := 118140960795 + 512214 * 2 ^ 59
def prefixEnd_512214 : Nat := 4983230072969 + 3 ^ 40 * 512214 * 2
def baseEnd_512214 : Nat := 155858951088689892781853

theorem tailTrace_512214 : CollatzResearch.WordTrace tailWord_512214 prefixEnd_512214 155858951088689892781853 := by
  unfold tailWord_512214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167623710396477001983481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12454652910895754687823797 1167623710396477001983481)
  ·
    refine ⟨875717782797357751487611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1167623710396477001983481 875717782797357751487611)
    ·
      refine ⟨1313576674196036627231417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875717782797357751487611 1313576674196036627231417)
      ·
        refine ⟨985182505647027470423563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1313576674196036627231417 985182505647027470423563)
        ·
          refine ⟨1477773758470541205635345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985182505647027470423563 1477773758470541205635345)
          ·
            refine ⟨1108330318852905904226509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477773758470541205635345 1108330318852905904226509)
            ·
              refine ⟨415623869569839714084941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1108330318852905904226509 415623869569839714084941)
              ·
                refine ⟨155858951088689892781853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415623869569839714084941 155858951088689892781853)
                ·
                  rfl

theorem cell19_512214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_512214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512214 prefixEnd_512214 := by exact prefixLift 512214
  have htrace : WordTrace (prefixWord ++ tailWord_512214) baseStart_512214 baseEnd_512214 := by
    simpa [prefixWord, tailWord_512214, baseEnd_512214] using wordTrace_append hprefix tailTrace_512214
  have hstable : (prefixWord ++ tailWord_512214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512214).length < 2 ^ (prefixWord ++ tailWord_512214).sum := by decide
  have hdescent : baseEnd_512214 < baseStart_512214 := by decide
  rcases family_descends (prefixWord ++ tailWord_512214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512237 : List Nat := [1, 5, 1, 2, 3, 1, 6]
def baseStart_512237 : Nat := 118140960795 + 512237 * 2 ^ 59
def prefixEnd_512237 : Nat := 4983230072969 + 3 ^ 40 * 512237 * 2
def baseEnd_512237 : Nat := 51955316546610884756893

theorem tailTrace_512237 : CollatzResearch.WordTrace tailWord_512237 prefixEnd_512237 51955316546610884756893 := by
  unfold tailWord_512237
  simp only [CollatzResearch.WordTrace]
  refine ⟨18682818245260306959822965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12455212163506871306548643 18682818245260306959822965)
  ·
    refine ⟨1751514210493153777483403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18682818245260306959822965 1751514210493153777483403)
    ·
      refine ⟨2627271315739730666225105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1751514210493153777483403 2627271315739730666225105)
      ·
        refine ⟨1970453486804797999668829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2627271315739730666225105 1970453486804797999668829)
        ·
          refine ⟨738920057551799249875811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1970453486804797999668829 738920057551799249875811)
          ·
            refine ⟨1108380086327698874813717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738920057551799249875811 1108380086327698874813717)
            ·
              refine ⟨51955316546610884756893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1108380086327698874813717 51955316546610884756893)
              ·
                rfl

theorem cell19_512237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_512237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512237 prefixEnd_512237 := by exact prefixLift 512237
  have htrace : WordTrace (prefixWord ++ tailWord_512237) baseStart_512237 baseEnd_512237 := by
    simpa [prefixWord, tailWord_512237, baseEnd_512237] using wordTrace_append hprefix tailTrace_512237
  have hstable : (prefixWord ++ tailWord_512237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512237).length < 2 ^ (prefixWord ++ tailWord_512237).sum := by decide
  have hdescent : baseEnd_512237 < baseStart_512237 := by decide
  rcases family_descends (prefixWord ++ tailWord_512237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512239 : List Nat := [1, 1, 2, 1, 6, 2, 6]
def baseStart_512239 : Nat := 118140960795 + 512239 * 2 ^ 59
def prefixEnd_512239 : Nat := 4983230072969 + 3 ^ 40 * 512239 * 2
def baseEnd_512239 : Nat := 51955519403165747408743

theorem tailTrace_512239 : CollatzResearch.WordTrace tailWord_512239 prefixEnd_512239 51955519403165747408743 := by
  unfold tailWord_512239
  simp only [CollatzResearch.WordTrace]
  refine ⟨18682891191253061301395771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12455260794168707534263847 18682891191253061301395771)
  ·
    refine ⟨28024336786879591952093657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18682891191253061301395771 28024336786879591952093657)
    ·
      refine ⟨21018252590159693964070243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28024336786879591952093657 21018252590159693964070243)
      ·
        refine ⟨31527378885239540946105365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21018252590159693964070243 31527378885239540946105365)
        ·
          refine ⟨1477845885245603481848689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31527378885239540946105365 1477845885245603481848689)
          ·
            refine ⟨1108384413934202611386517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477845885245603481848689 1108384413934202611386517)
            ·
              refine ⟨51955519403165747408743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1108384413934202611386517 51955519403165747408743)
              ·
                rfl

theorem cell19_512239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_512239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512239 prefixEnd_512239 := by exact prefixLift 512239
  have htrace : WordTrace (prefixWord ++ tailWord_512239) baseStart_512239 baseEnd_512239 := by
    simpa [prefixWord, tailWord_512239, baseEnd_512239] using wordTrace_append hprefix tailTrace_512239
  have hstable : (prefixWord ++ tailWord_512239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512239).length < 2 ^ (prefixWord ++ tailWord_512239).sum := by decide
  have hdescent : baseEnd_512239 < baseStart_512239 := by decide
  rcases family_descends (prefixWord ++ tailWord_512239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512313 : List Nat := [1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_512313 : Nat := 118140960795 + 512313 * 2 ^ 59
def prefixEnd_512313 : Nat := 4983230072969 + 3 ^ 40 * 512313 * 2
def baseEnd_512313 : Nat := 155889075287086996581583

theorem tailTrace_512313 : CollatzResearch.WordTrace tailWord_512313 prefixEnd_512313 155889075287086996581583 := by
  unfold tailWord_512313
  simp only [CollatzResearch.WordTrace]
  refine ⟨18685590192984971939589593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12457060128656647959726395 18685590192984971939589593)
  ·
    refine ⟨14014192644738728954692195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18685590192984971939589593 14014192644738728954692195)
    ·
      refine ⟨21021288967108093432038293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14014192644738728954692195 21021288967108093432038293)
      ·
        refine ⟨985372920333191879626795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21021288967108093432038293 985372920333191879626795)
        ·
          refine ⟨1478059380499787819440193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985372920333191879626795 1478059380499787819440193)
          ·
            refine ⟨1108544535374840864580145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1478059380499787819440193 1108544535374840864580145)
            ·
              refine ⟨831408401531130648435109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108544535374840864580145 831408401531130648435109)
              ·
                refine ⟨155889075287086996581583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831408401531130648435109 155889075287086996581583)
                ·
                  rfl

theorem cell19_512313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_512313 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512313 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512313 prefixEnd_512313 := by exact prefixLift 512313
  have htrace : WordTrace (prefixWord ++ tailWord_512313) baseStart_512313 baseEnd_512313 := by
    simpa [prefixWord, tailWord_512313, baseEnd_512313] using wordTrace_append hprefix tailTrace_512313
  have hstable : (prefixWord ++ tailWord_512313).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512313).length < 2 ^ (prefixWord ++ tailWord_512313).sum := by decide
  have hdescent : baseEnd_512313 < baseStart_512313 := by decide
  rcases family_descends (prefixWord ++ tailWord_512313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512370 : List Nat := [3, 2, 1, 2, 1, 5, 1, 4]
def baseStart_512370 : Nat := 118140960795 + 512370 * 2 ^ 59
def prefixEnd_512370 : Nat := 4983230072969 + 3 ^ 40 * 512370 * 2
def baseEnd_512370 : Nat := 155906419522527753314761

theorem tailTrace_512370 : CollatzResearch.WordTrace tailWord_512370 prefixEnd_512370 155906419522527753314761 := by
  unfold tailWord_512370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671917288444617668603641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12458446102518980449609709 4671917288444617668603641)
  ·
    refine ⟨3503937966333463251452731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4671917288444617668603641 3503937966333463251452731)
    ·
      refine ⟨5255906949500194877179097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3503937966333463251452731 5255906949500194877179097)
      ·
        refine ⟨3941930212125146157884323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5255906949500194877179097 3941930212125146157884323)
        ·
          refine ⟨5912895318187719236826485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941930212125146157884323 5912895318187719236826485)
          ·
            refine ⟨554333936080098678452483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5912895318187719236826485 554333936080098678452483)
            ·
              refine ⟨831500904120148017678725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554333936080098678452483 831500904120148017678725)
              ·
                refine ⟨155906419522527753314761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831500904120148017678725 155906419522527753314761)
                ·
                  rfl

theorem cell19_512370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_512370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512370 prefixEnd_512370 := by exact prefixLift 512370
  have htrace : WordTrace (prefixWord ++ tailWord_512370) baseStart_512370 baseEnd_512370 := by
    simpa [prefixWord, tailWord_512370, baseEnd_512370] using wordTrace_append hprefix tailTrace_512370
  have hstable : (prefixWord ++ tailWord_512370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512370).length < 2 ^ (prefixWord ++ tailWord_512370).sum := by decide
  have hdescent : baseEnd_512370 < baseStart_512370 := by decide
  rcases family_descends (prefixWord ++ tailWord_512370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512410 : List Nat := [3, 1, 1, 4, 1, 3, 6]
def baseStart_512410 : Nat := 118140960795 + 512410 * 2 ^ 59
def prefixEnd_512410 : Nat := 4983230072969 + 3 ^ 40 * 512410 * 2
def baseEnd_512410 : Nat := 51972863638606504141921

theorem tailTrace_512410 : CollatzResearch.WordTrace tailWord_512410 prefixEnd_512410 51972863638606504141921 := by
  unfold tailWord_512410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4672282018408389376467671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12459418715755705003913789 4672282018408389376467671)
  ·
    refine ⟨7008423027612584064701507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4672282018408389376467671 7008423027612584064701507)
    ·
      refine ⟨10512634541418876097052261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7008423027612584064701507 10512634541418876097052261)
      ·
        refine ⟨1971118976516039268197299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10512634541418876097052261 1971118976516039268197299)
        ·
          refine ⟨2956678464774058902295949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971118976516039268197299 2956678464774058902295949)
          ·
            refine ⟨1108754424290272088360981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2956678464774058902295949 1108754424290272088360981)
            ·
              refine ⟨51972863638606504141921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1108754424290272088360981 51972863638606504141921)
              ·
                rfl

theorem cell19_512410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_512410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512410 prefixEnd_512410 := by exact prefixLift 512410
  have htrace : WordTrace (prefixWord ++ tailWord_512410) baseStart_512410 baseEnd_512410 := by
    simpa [prefixWord, tailWord_512410, baseEnd_512410] using wordTrace_append hprefix tailTrace_512410
  have hstable : (prefixWord ++ tailWord_512410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512410).length < 2 ^ (prefixWord ++ tailWord_512410).sum := by decide
  have hdescent : baseEnd_512410 < baseStart_512410 := by decide
  rcases family_descends (prefixWord ++ tailWord_512410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512444 : List Nat := [2, 2, 2, 4, 1, 3, 2, 3]
def baseStart_512444 : Nat := 118140960795 + 512444 * 2 ^ 59
def prefixEnd_512444 : Nat := 4983230072969 + 3 ^ 40 * 512444 * 2
def baseEnd_512444 : Nat := 155928936600117507670115

theorem tailTrace_512444 : CollatzResearch.WordTrace tailWord_512444 prefixEnd_512444 155928936600117507670115 := by
  unfold tailWord_512444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9345184077755190656304193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12460245437006920875072257 9345184077755190656304193)
  ·
    refine ⟨7008888058316392992228145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9345184077755190656304193 7008888058316392992228145)
    ·
      refine ⟨5256666043737294744171109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7008888058316392992228145 5256666043737294744171109)
      ·
        refine ⟨985624883200742764532083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5256666043737294744171109 985624883200742764532083)
        ·
          refine ⟨1478437324801114146798125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985624883200742764532083 1478437324801114146798125)
          ·
            refine ⟨554413996800417805049297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1478437324801114146798125 554413996800417805049297)
            ·
              refine ⟨415810497600313353786973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554413996800417805049297 415810497600313353786973)
              ·
                refine ⟨155928936600117507670115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415810497600313353786973 155928936600117507670115)
                ·
                  rfl

theorem cell19_512444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_512444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512444 prefixEnd_512444 := by exact prefixLift 512444
  have htrace : WordTrace (prefixWord ++ tailWord_512444) baseStart_512444 baseEnd_512444 := by
    simpa [prefixWord, tailWord_512444, baseEnd_512444] using wordTrace_append hprefix tailTrace_512444
  have hstable : (prefixWord ++ tailWord_512444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512444).length < 2 ^ (prefixWord ++ tailWord_512444).sum := by decide
  have hdescent : baseEnd_512444 < baseStart_512444 := by decide
  rcases family_descends (prefixWord ++ tailWord_512444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512446 : List Nat := [4, 2, 1, 1, 1, 1, 6, 3]
def baseStart_512446 : Nat := 118140960795 + 512446 * 2 ^ 59
def prefixEnd_512446 : Nat := 4983230072969 + 3 ^ 40 * 512446 * 2
def baseEnd_512446 : Nat := 155929545169782095625665

theorem tailTrace_512446 : CollatzResearch.WordTrace tailWord_512446 prefixEnd_512446 155929545169782095625665 := by
  unfold tailWord_512446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336305137687891956772649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12460294067668757102787461 2336305137687891956772649)
  ·
    refine ⟨1752228853265918967579487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2336305137687891956772649 1752228853265918967579487)
    ·
      refine ⟨2628343279898878451369231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1752228853265918967579487 2628343279898878451369231)
      ·
        refine ⟨3942514919848317677053847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628343279898878451369231 3942514919848317677053847)
        ·
          refine ⟨5913772379772476515580771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942514919848317677053847 5913772379772476515580771)
          ·
            refine ⟨8870658569658714773371157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5913772379772476515580771 8870658569658714773371157)
            ·
              refine ⟨415812120452752255001773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8870658569658714773371157 415812120452752255001773)
              ·
                refine ⟨155929545169782095625665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415812120452752255001773 155929545169782095625665)
                ·
                  rfl

theorem cell19_512446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_512446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512446 prefixEnd_512446 := by exact prefixLift 512446
  have htrace : WordTrace (prefixWord ++ tailWord_512446) baseStart_512446 baseEnd_512446 := by
    simpa [prefixWord, tailWord_512446, baseEnd_512446] using wordTrace_append hprefix tailTrace_512446
  have hstable : (prefixWord ++ tailWord_512446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512446).length < 2 ^ (prefixWord ++ tailWord_512446).sum := by decide
  have hdescent : baseEnd_512446 < baseStart_512446 := by decide
  rcases family_descends (prefixWord ++ tailWord_512446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512541 : List Nat := [1, 4, 2, 2, 1, 4, 1, 4]
def baseStart_512541 : Nat := 118140960795 + 512541 * 2 ^ 59
def prefixEnd_512541 : Nat := 4983230072969 + 3 ^ 40 * 512541 * 2
def baseEnd_512541 : Nat := 155958452228850023514295

theorem tailTrace_512541 : CollatzResearch.WordTrace tailWord_512541 prefixEnd_512541 155958452228850023514295 := by
  unfold tailWord_512541
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693906036158966878889477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12462604024105977919259651 18693906036158966878889477)
  ·
    refine ⟨3505107381779806289791777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18693906036158966878889477 3505107381779806289791777)
    ·
      refine ⟨2628830536334854717343833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3505107381779806289791777 2628830536334854717343833)
      ·
        refine ⟨1971622902251141038007875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2628830536334854717343833 1971622902251141038007875)
        ·
          refine ⟨2957434353376711557011813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971622902251141038007875 2957434353376711557011813)
          ·
            refine ⟨554518941258133416939715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2957434353376711557011813 554518941258133416939715)
            ·
              refine ⟨831778411887200125409573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554518941258133416939715 831778411887200125409573)
              ·
                refine ⟨155958452228850023514295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831778411887200125409573 155958452228850023514295)
                ·
                  rfl

theorem cell19_512541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_512541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512541 prefixEnd_512541 := by exact prefixLift 512541
  have htrace : WordTrace (prefixWord ++ tailWord_512541) baseStart_512541 baseEnd_512541 := by
    simpa [prefixWord, tailWord_512541, baseEnd_512541] using wordTrace_append hprefix tailTrace_512541
  have hstable : (prefixWord ++ tailWord_512541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512541).length < 2 ^ (prefixWord ++ tailWord_512541).sum := by decide
  have hdescent : baseEnd_512541 < baseStart_512541 := by decide
  rcases family_descends (prefixWord ++ tailWord_512541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512558 : List Nat := [4, 1, 3, 1, 3, 1, 3, 3]
def baseStart_512558 : Nat := 118140960795 + 512558 * 2 ^ 59
def prefixEnd_512558 : Nat := 4983230072969 + 3 ^ 40 * 512558 * 2
def baseEnd_512558 : Nat := 155963625070999021136471

theorem tailTrace_512558 : CollatzResearch.WordTrace tailWord_512558 prefixEnd_512558 155963625070999021136471 := by
  unfold tailWord_512558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336815759637172347782291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12463017384731585854838885 2336815759637172347782291)
  ·
    refine ⟨3505223639455758521673437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2336815759637172347782291 3505223639455758521673437)
    ·
      refine ⟨1314458864795909445627539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3505223639455758521673437 1314458864795909445627539)
      ·
        refine ⟨1971688297193864168441309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1314458864795909445627539 1971688297193864168441309)
        ·
          refine ⟨739383111447699063165491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1971688297193864168441309 739383111447699063165491)
          ·
            refine ⟨1109074667171548594748237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739383111447699063165491 1109074667171548594748237)
            ·
              refine ⟨415903000189330723030589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1109074667171548594748237 415903000189330723030589)
              ·
                refine ⟨155963625070999021136471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415903000189330723030589 155963625070999021136471)
                ·
                  rfl

theorem cell19_512558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_512558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512558 prefixEnd_512558 := by exact prefixLift 512558
  have htrace : WordTrace (prefixWord ++ tailWord_512558) baseStart_512558 baseEnd_512558 := by
    simpa [prefixWord, tailWord_512558, baseEnd_512558] using wordTrace_append hprefix tailTrace_512558
  have hstable : (prefixWord ++ tailWord_512558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512558).length < 2 ^ (prefixWord ++ tailWord_512558).sum := by decide
  have hdescent : baseEnd_512558 < baseStart_512558 := by decide
  rcases family_descends (prefixWord ++ tailWord_512558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512640 : List Nat := [2, 1, 1, 2, 1, 5, 7]
def baseStart_512640 : Nat := 118140960795 + 512640 * 2 ^ 59
def prefixEnd_512640 : Nat := 4983230072969 + 3 ^ 40 * 512640 * 2
def baseEnd_512640 : Nat := 51996192142415709104675

theorem tailTrace_512640 : CollatzResearch.WordTrace tailWord_512640 prefixEnd_512640 51996192142415709104675 := by
  unfold tailWord_512640
  simp only [CollatzResearch.WordTrace]
  refine ⟨9348758431400153393371687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12465011241866871191162249 9348758431400153393371687)
  ·
    refine ⟨14023137647100230090057531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9348758431400153393371687 14023137647100230090057531)
    ·
      refine ⟨21034706470650345135086297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14023137647100230090057531 21034706470650345135086297)
      ·
        refine ⟨15776029852987758851314723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21034706470650345135086297 15776029852987758851314723)
        ·
          refine ⟨23664044779481638276972085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15776029852987758851314723 23664044779481638276972085)
          ·
            refine ⟨2218504198076403588466133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23664044779481638276972085 2218504198076403588466133)
            ·
              refine ⟨51996192142415709104675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2218504198076403588466133 51996192142415709104675)
              ·
                rfl

theorem cell19_512640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_512640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512640 prefixEnd_512640 := by exact prefixLift 512640
  have htrace : WordTrace (prefixWord ++ tailWord_512640) baseStart_512640 baseEnd_512640 := by
    simpa [prefixWord, tailWord_512640, baseEnd_512640] using wordTrace_append hprefix tailTrace_512640
  have hstable : (prefixWord ++ tailWord_512640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512640).length < 2 ^ (prefixWord ++ tailWord_512640).sum := by decide
  have hdescent : baseEnd_512640 < baseStart_512640 := by decide
  rcases family_descends (prefixWord ++ tailWord_512640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512695 : List Nat := [1, 1, 3, 1, 7, 6]
def baseStart_512695 : Nat := 118140960795 + 512695 * 2 ^ 59
def prefixEnd_512695 : Nat := 4983230072969 + 3 ^ 40 * 512695 * 2
def baseEnd_512695 : Nat := 17333923565891477343517

theorem tailTrace_512695 : CollatzResearch.WordTrace tailWord_512695 prefixEnd_512695 17333923565891477343517 := by
  unfold tailWord_512695
  simp only [CollatzResearch.WordTrace]
  refine ⟨18699522877601051179995539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12466348585067367453330359 18699522877601051179995539)
  ·
    refine ⟨28049284316401576769993309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18699522877601051179995539 28049284316401576769993309)
    ·
      refine ⟨10518481618650591288747491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28049284316401576769993309 10518481618650591288747491)
      ·
        refine ⟨15777722427975886933121237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10518481618650591288747491 15777722427975886933121237)
        ·
          refine ⟨369790369405684849995029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15777722427975886933121237 369790369405684849995029)
          ·
            refine ⟨17333923565891477343517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 369790369405684849995029 17333923565891477343517)
            ·
              rfl

theorem cell19_512695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 6].length) (baseStart_512695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512695 prefixEnd_512695 := by exact prefixLift 512695
  have htrace : WordTrace (prefixWord ++ tailWord_512695) baseStart_512695 baseEnd_512695 := by
    simpa [prefixWord, tailWord_512695, baseEnd_512695] using wordTrace_append hprefix tailTrace_512695
  have hstable : (prefixWord ++ tailWord_512695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512695).length < 2 ^ (prefixWord ++ tailWord_512695).sum := by decide
  have hdescent : baseEnd_512695 < baseStart_512695 := by decide
  rcases family_descends (prefixWord ++ tailWord_512695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512714 : List Nat := [3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_512714 : Nat := 118140960795 + 512714 * 2 ^ 59
def prefixEnd_512714 : Nat := 4983230072969 + 3 ^ 40 * 512714 * 2
def baseEnd_512714 : Nat := 156011093504836881669379

theorem tailTrace_512714 : CollatzResearch.WordTrace tailWord_512714 prefixEnd_512714 156011093504836881669379 := by
  unfold tailWord_512714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4675053966133054356234299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12466810576354811616624797 4675053966133054356234299)
  ·
    refine ⟨7012580949199581534351449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4675053966133054356234299 7012580949199581534351449)
    ·
      refine ⟨5259435711899686150763587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7012580949199581534351449 5259435711899686150763587)
      ·
        refine ⟨7889153567849529226145381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5259435711899686150763587 7889153567849529226145381)
        ·
          refine ⟨1479216293971786729902259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7889153567849529226145381 1479216293971786729902259)
          ·
            refine ⟨2218824440957680094853389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479216293971786729902259 2218824440957680094853389)
            ·
              refine ⟨832059165359130035570021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2218824440957680094853389 832059165359130035570021)
              ·
                refine ⟨156011093504836881669379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832059165359130035570021 156011093504836881669379)
                ·
                  rfl

theorem cell19_512714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_512714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512714 prefixEnd_512714 := by exact prefixLift 512714
  have htrace : WordTrace (prefixWord ++ tailWord_512714) baseStart_512714 baseEnd_512714 := by
    simpa [prefixWord, tailWord_512714, baseEnd_512714] using wordTrace_append hprefix tailTrace_512714
  have hstable : (prefixWord ++ tailWord_512714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512714).length < 2 ^ (prefixWord ++ tailWord_512714).sum := by decide
  have hdescent : baseEnd_512714 < baseStart_512714 := by decide
  rcases family_descends (prefixWord ++ tailWord_512714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512866 : List Nat := [3, 3, 2, 1, 3, 7]
def baseStart_512866 : Nat := 118140960795 + 512866 * 2 ^ 59
def prefixEnd_512866 : Nat := 4983230072969 + 3 ^ 40 * 512866 * 2
def baseEnd_512866 : Nat := 17339704977705062921243

theorem tailTrace_512866 : CollatzResearch.WordTrace tailWord_512866 prefixEnd_512866 17339704977705062921243 := by
  unfold tailWord_512866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676439939995386846117613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12470506506654364922980301 4676439939995386846117613)
  ·
    refine ⟨1753664977498270067294105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4676439939995386846117613 1753664977498270067294105)
    ·
      refine ⟨1315248733123702550470579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1753664977498270067294105 1315248733123702550470579)
      ·
        refine ⟨1972873099685553825705869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1315248733123702550470579 1972873099685553825705869)
        ·
          refine ⟨739827412382082684639701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1972873099685553825705869 739827412382082684639701)
          ·
            refine ⟨17339704977705062921243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 739827412382082684639701 17339704977705062921243)
            ·
              rfl

theorem cell19_512866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 7].length) (baseStart_512866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512866 prefixEnd_512866 := by exact prefixLift 512866
  have htrace : WordTrace (prefixWord ++ tailWord_512866) baseStart_512866 baseEnd_512866 := by
    simpa [prefixWord, tailWord_512866, baseEnd_512866] using wordTrace_append hprefix tailTrace_512866
  have hstable : (prefixWord ++ tailWord_512866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512866).length < 2 ^ (prefixWord ++ tailWord_512866).sum := by decide
  have hdescent : baseEnd_512866 < baseStart_512866 := by decide
  rcases family_descends (prefixWord ++ tailWord_512866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512868 : List Nat := [2, 3, 1, 1, 4, 8]
def baseStart_512868 : Nat := 118140960795 + 512868 * 2 ^ 59
def prefixEnd_512868 : Nat := 4983230072969 + 3 ^ 40 * 512868 * 2
def baseEnd_512868 : Nat := 17339772596556683805193

theorem tailTrace_512868 : CollatzResearch.WordTrace tailWord_512868 prefixEnd_512868 17339772596556683805193 := by
  unfold tailWord_512868
  simp only [CollatzResearch.WordTrace]
  refine ⟨9352916352987150863021629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12470555137316201150695505 9352916352987150863021629)
  ·
    refine ⟨3507343632370181573633111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9352916352987150863021629 3507343632370181573633111)
    ·
      refine ⟨5261015448555272360449667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3507343632370181573633111 5261015448555272360449667)
      ·
        refine ⟨7891523172832908540674501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5261015448555272360449667 7891523172832908540674501)
        ·
          refine ⟨1479660594906170351376469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7891523172832908540674501 1479660594906170351376469)
          ·
            refine ⟨17339772596556683805193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1479660594906170351376469 17339772596556683805193)
            ·
              rfl

theorem cell19_512868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 8].length) (baseStart_512868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512868 prefixEnd_512868 := by exact prefixLift 512868
  have htrace : WordTrace (prefixWord ++ tailWord_512868) baseStart_512868 baseEnd_512868 := by
    simpa [prefixWord, tailWord_512868, baseEnd_512868] using wordTrace_append hprefix tailTrace_512868
  have hstable : (prefixWord ++ tailWord_512868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512868).length < 2 ^ (prefixWord ++ tailWord_512868).sum := by decide
  have hdescent : baseEnd_512868 < baseStart_512868 := by decide
  rcases family_descends (prefixWord ++ tailWord_512868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512885 : List Nat := [1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_512885 : Nat := 118140960795 + 512885 * 2 ^ 59
def prefixEnd_512885 : Nat := 4983230072969 + 3 ^ 40 * 512885 * 2
def baseEnd_512885 : Nat := 156063126211159151868913

theorem tailTrace_512885 : CollatzResearch.WordTrace tailWord_512885 prefixEnd_512885 156063126211159151868913 := by
  unfold tailWord_512885
  simp only [CollatzResearch.WordTrace]
  refine ⟨18706452746912713629412109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12470968497941809086274739 18706452746912713629412109)
  ·
    refine ⟨7014919780092267611029541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18706452746912713629412109 7014919780092267611029541)
    ·
      refine ⟨1315297458767300177068039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7014919780092267611029541 1315297458767300177068039)
      ·
        refine ⟨1972946188150950265602059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1315297458767300177068039 1972946188150950265602059)
        ·
          refine ⟨2959419282226425398403089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1972946188150950265602059 2959419282226425398403089)
          ·
            refine ⟨2219564461669819048802317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2959419282226425398403089 2219564461669819048802317)
            ·
              refine ⟨832336673126182143300869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2219564461669819048802317 832336673126182143300869)
              ·
                refine ⟨156063126211159151868913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832336673126182143300869 156063126211159151868913)
                ·
                  rfl

theorem cell19_512885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_512885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512885 prefixEnd_512885 := by exact prefixLift 512885
  have htrace : WordTrace (prefixWord ++ tailWord_512885) baseStart_512885 baseEnd_512885 := by
    simpa [prefixWord, tailWord_512885, baseEnd_512885] using wordTrace_append hprefix tailTrace_512885
  have hstable : (prefixWord ++ tailWord_512885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512885).length < 2 ^ (prefixWord ++ tailWord_512885).sum := by decide
  have hdescent : baseEnd_512885 < baseStart_512885 := by decide
  rcases family_descends (prefixWord ++ tailWord_512885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512898 : List Nat := [3, 4, 2, 2, 1, 1, 3, 3]
def baseStart_512898 : Nat := 118140960795 + 512898 * 2 ^ 59
def prefixEnd_512898 : Nat := 4983230072969 + 3 ^ 40 * 512898 * 2
def baseEnd_512898 : Nat := 156067081913978973579989

theorem tailTrace_512898 : CollatzResearch.WordTrace tailWord_512898 prefixEnd_512898 156067081913978973579989 := by
  unfold tailWord_512898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676731723966404212408837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12471284597243744566423565 4676731723966404212408837)
  ·
    refine ⟨876887198243700789826657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4676731723966404212408837 876887198243700789826657)
    ·
      refine ⟨657665398682775592369993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 876887198243700789826657 657665398682775592369993)
      ·
        refine ⟨493249049012081694277495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657665398682775592369993 493249049012081694277495)
        ·
          refine ⟨739873573518122541416243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493249049012081694277495 739873573518122541416243)
          ·
            refine ⟨1109810360277183812124365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739873573518122541416243 1109810360277183812124365)
            ·
              refine ⟨416178885103943929546637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1109810360277183812124365 416178885103943929546637)
              ·
                refine ⟨156067081913978973579989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416178885103943929546637 156067081913978973579989)
                ·
                  rfl

theorem cell19_512898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_512898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512898 prefixEnd_512898 := by exact prefixLift 512898
  have htrace : WordTrace (prefixWord ++ tailWord_512898) baseStart_512898 baseEnd_512898 := by
    simpa [prefixWord, tailWord_512898, baseEnd_512898] using wordTrace_append hprefix tailTrace_512898
  have hstable : (prefixWord ++ tailWord_512898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512898).length < 2 ^ (prefixWord ++ tailWord_512898).sum := by decide
  have hdescent : baseEnd_512898 < baseStart_512898 := by decide
  rcases family_descends (prefixWord ++ tailWord_512898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512925 : List Nat := [1, 4, 2, 1, 2, 1, 8]
def baseStart_512925 : Nat := 118140960795 + 512925 * 2 ^ 59
def prefixEnd_512925 : Nat := 4983230072969 + 3 ^ 40 * 512925 * 2
def baseEnd_512925 : Nat := 52025099201483636993305

theorem tailTrace_512925 : CollatzResearch.WordTrace tailWord_512925 prefixEnd_512925 52025099201483636993305 := by
  unfold tailWord_512925
  simp only [CollatzResearch.WordTrace]
  refine ⟨18707911666767800460868229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12471941111178533640578819 18707911666767800460868229)
  ·
    refine ⟨3507733437518962586412793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18707911666767800460868229 3507733437518962586412793)
    ·
      refine ⟨2630800078139221939809595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3507733437518962586412793 2630800078139221939809595)
      ·
        refine ⟨3946200117208832909714393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2630800078139221939809595 3946200117208832909714393)
        ·
          refine ⟨2959650087906624682285795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3946200117208832909714393 2959650087906624682285795)
          ·
            refine ⟨4439475131859937023428693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959650087906624682285795 4439475131859937023428693)
            ·
              refine ⟨52025099201483636993305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4439475131859937023428693 52025099201483636993305)
              ·
                rfl

theorem cell19_512925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_512925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512925 prefixEnd_512925 := by exact prefixLift 512925
  have htrace : WordTrace (prefixWord ++ tailWord_512925) baseStart_512925 baseEnd_512925 := by
    simpa [prefixWord, tailWord_512925, baseEnd_512925] using wordTrace_append hprefix tailTrace_512925
  have hstable : (prefixWord ++ tailWord_512925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512925).length < 2 ^ (prefixWord ++ tailWord_512925).sum := by decide
  have hdescent : baseEnd_512925 < baseStart_512925 := by decide
  rcases family_descends (prefixWord ++ tailWord_512925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512957 : List Nat := [1, 4, 1, 2, 5, 1, 2, 3]
def baseStart_512957 : Nat := 118140960795 + 512957 * 2 ^ 59
def prefixEnd_512957 : Nat := 4983230072969 + 3 ^ 40 * 512957 * 2
def baseEnd_512957 : Nat := 156085034719084318268717

theorem tailTrace_512957 : CollatzResearch.WordTrace tailWord_512957 prefixEnd_512957 156085034719084318268717 := by
  unfold tailWord_512957
  simp only [CollatzResearch.WordTrace]
  refine ⟨18709078802651869926033125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12472719201767913284022083 18709078802651869926033125)
  ·
    refine ⟨3507952275497225611131211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18709078802651869926033125 3507952275497225611131211)
    ·
      refine ⟨5261928413245838416696817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3507952275497225611131211 5261928413245838416696817)
      ·
        refine ⟨3946446309934378812522613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5261928413245838416696817 3946446309934378812522613)
        ·
          refine ⟨369979341556348013673995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3946446309934378812522613 369979341556348013673995)
          ·
            refine ⟨554969012334522020510993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369979341556348013673995 554969012334522020510993)
            ·
              refine ⟨416226759250891515383245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554969012334522020510993 416226759250891515383245)
              ·
                refine ⟨156085034719084318268717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416226759250891515383245 156085034719084318268717)
                ·
                  rfl

theorem cell19_512957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 3].length) (baseStart_512957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512957 prefixEnd_512957 := by exact prefixLift 512957
  have htrace : WordTrace (prefixWord ++ tailWord_512957) baseStart_512957 baseEnd_512957 := by
    simpa [prefixWord, tailWord_512957, baseEnd_512957] using wordTrace_append hprefix tailTrace_512957
  have hstable : (prefixWord ++ tailWord_512957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512957).length < 2 ^ (prefixWord ++ tailWord_512957).sum := by decide
  have hdescent : baseEnd_512957 < baseStart_512957 := by decide
  rcases family_descends (prefixWord ++ tailWord_512957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512980 : List Nat := [2, 4, 1, 2, 1, 4, 5]
def baseStart_512980 : Nat := 118140960795 + 512980 * 2 ^ 59
def prefixEnd_512980 : Nat := 4983230072969 + 3 ^ 40 * 512980 * 2
def baseEnd_512980 : Nat := 52030677756742359919181

theorem tailTrace_512980 : CollatzResearch.WordTrace tailWord_512980 prefixEnd_512980 52030677756742359919181 := by
  unfold tailWord_512980
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354958840784272427060197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12473278454379029902746929 9354958840784272427060197)
  ·
    refine ⟨1754054782647051080073787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9354958840784272427060197 1754054782647051080073787)
    ·
      refine ⟨2631082173970576620110681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1754054782647051080073787 2631082173970576620110681)
      ·
        refine ⟨1973311630477932465083011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2631082173970576620110681 1973311630477932465083011)
        ·
          refine ⟨2959967445716898697624517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973311630477932465083011 2959967445716898697624517)
          ·
            refine ⟨554993896071918505804597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2959967445716898697624517 554993896071918505804597)
            ·
              refine ⟨52030677756742359919181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 554993896071918505804597 52030677756742359919181)
              ·
                rfl

theorem cell19_512980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_512980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512980 prefixEnd_512980 := by exact prefixLift 512980
  have htrace : WordTrace (prefixWord ++ tailWord_512980) baseStart_512980 baseEnd_512980 := by
    simpa [prefixWord, tailWord_512980, baseEnd_512980] using wordTrace_append hprefix tailTrace_512980
  have hstable : (prefixWord ++ tailWord_512980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512980).length < 2 ^ (prefixWord ++ tailWord_512980).sum := by decide
  have hdescent : baseEnd_512980 < baseStart_512980 := by decide
  rcases family_descends (prefixWord ++ tailWord_512980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512997 : List Nat := [1, 3, 1, 6, 1, 1, 2, 4]
def baseStart_512997 : Nat := 118140960795 + 512997 * 2 ^ 59
def prefixEnd_512997 : Nat := 4983230072969 + 3 ^ 40 * 512997 * 2
def baseEnd_512997 : Nat := 156097206112376077379719

theorem tailTrace_512997 : CollatzResearch.WordTrace tailWord_512997 prefixEnd_512997 156097206112376077379719 := by
  unfold tailWord_512997
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710537722506956757489245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12473691815004637838326163 18710537722506956757489245)
  ·
    refine ⟨7016451645940108784058467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18710537722506956757489245 7016451645940108784058467)
    ·
      refine ⟨10524677468910163176087701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7016451645940108784058467 10524677468910163176087701)
      ·
        refine ⟨493344256355163898879111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10524677468910163176087701 493344256355163898879111)
        ·
          refine ⟨740016384532745848318667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493344256355163898879111 740016384532745848318667)
          ·
            refine ⟨1110024576799118772478001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740016384532745848318667 1110024576799118772478001)
            ·
              refine ⟨832518432599339079358501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110024576799118772478001 832518432599339079358501)
              ·
                refine ⟨156097206112376077379719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832518432599339079358501 156097206112376077379719)
                ·
                  rfl

theorem cell19_512997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 4].length) (baseStart_512997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512997 prefixEnd_512997 := by exact prefixLift 512997
  have htrace : WordTrace (prefixWord ++ tailWord_512997) baseStart_512997 baseEnd_512997 := by
    simpa [prefixWord, tailWord_512997, baseEnd_512997] using wordTrace_append hprefix tailTrace_512997
  have hstable : (prefixWord ++ tailWord_512997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512997).length < 2 ^ (prefixWord ++ tailWord_512997).sum := by decide
  have hdescent : baseEnd_512997 < baseStart_512997 := by decide
  rcases family_descends (prefixWord ++ tailWord_512997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512999 : List Nat := [1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_512999 : Nat := 118140960795 + 512999 * 2 ^ 59
def prefixEnd_512999 : Nat := 4983230072969 + 3 ^ 40 * 512999 * 2
def baseEnd_512999 : Nat := 156097814682040665335269

theorem tailTrace_512999 : CollatzResearch.WordTrace tailWord_512999 prefixEnd_512999 156097814682040665335269 := by
  unfold tailWord_512999
  simp only [CollatzResearch.WordTrace]
  refine ⟨18710610668499711099062051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12473740445666474066041367 18710610668499711099062051)
  ·
    refine ⟨28065916002749566648593077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18710610668499711099062051 28065916002749566648593077)
    ·
      refine ⟨2631179625257771873305601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28065916002749566648593077 2631179625257771873305601)
      ·
        refine ⟨1973384718943328904979201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2631179625257771873305601 1973384718943328904979201)
        ·
          refine ⟨1480038539207496678734401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1973384718943328904979201 1480038539207496678734401)
          ·
            refine ⟨1110028904405622509050801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1480038539207496678734401 1110028904405622509050801)
            ·
              refine ⟨832521678304216881788101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110028904405622509050801 832521678304216881788101)
              ·
                refine ⟨156097814682040665335269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832521678304216881788101 156097814682040665335269)
                ·
                  rfl

theorem cell19_512999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_512999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_512999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_512999 prefixEnd_512999 := by exact prefixLift 512999
  have htrace : WordTrace (prefixWord ++ tailWord_512999) baseStart_512999 baseEnd_512999 := by
    simpa [prefixWord, tailWord_512999, baseEnd_512999] using wordTrace_append hprefix tailTrace_512999
  have hstable : (prefixWord ++ tailWord_512999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512999).length < 2 ^ (prefixWord ++ tailWord_512999).sum := by decide
  have hdescent : baseEnd_512999 < baseStart_512999 := by decide
  rcases family_descends (prefixWord ++ tailWord_512999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513020 : List Nat := [2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_513020 : Nat := 118140960795 + 513020 * 2 ^ 59
def prefixEnd_513020 : Nat := 4983230072969 + 3 ^ 40 * 513020 * 2
def baseEnd_513020 : Nat := 156104204663518838868545

theorem tailTrace_513020 : CollatzResearch.WordTrace tailWord_513020 prefixEnd_513020 156104204663518838868545 := by
  unfold tailWord_513020
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355688300711815842788257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12474251067615754457051009 9355688300711815842788257)
  ·
    refine ⟨7016766225533861882091193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9355688300711815842788257 7016766225533861882091193)
    ·
      refine ⟨5262574669150396411568395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7016766225533861882091193 5262574669150396411568395)
      ·
        refine ⟨7893862003725594617352593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5262574669150396411568395 7893862003725594617352593)
        ·
          refine ⟨5920396502794195963014445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7893862003725594617352593 5920396502794195963014445)
          ·
            refine ⟨2220148688547823486130417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5920396502794195963014445 2220148688547823486130417)
            ·
              refine ⟨1665111516410867614597813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220148688547823486130417 1665111516410867614597813)
              ·
                refine ⟨156104204663518838868545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1665111516410867614597813 156104204663518838868545)
                ·
                  rfl

theorem cell19_513020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_513020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513020 prefixEnd_513020 := by exact prefixLift 513020
  have htrace : WordTrace (prefixWord ++ tailWord_513020) baseStart_513020 baseEnd_513020 := by
    simpa [prefixWord, tailWord_513020, baseEnd_513020] using wordTrace_append hprefix tailTrace_513020
  have hstable : (prefixWord ++ tailWord_513020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513020).length < 2 ^ (prefixWord ++ tailWord_513020).sum := by decide
  have hdescent : baseEnd_513020 < baseStart_513020 := by decide
  rcases family_descends (prefixWord ++ tailWord_513020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513037 : List Nat := [1, 7, 1, 10]
def baseStart_513037 : Nat := 118140960795 + 513037 * 2 ^ 59
def prefixEnd_513037 : Nat := 4983230072969 + 3 ^ 40 * 513037 * 2
def baseEnd_513037 : Nat := 1927276265502072055441

theorem tailTrace_513037 : CollatzResearch.WordTrace tailWord_513037 prefixEnd_513037 1927276265502072055441 := by
  unfold tailWord_513037
  simp only [CollatzResearch.WordTrace]
  refine ⟨18711996642362043588945365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12474664428241362392630243 18711996642362043588945365)
  ·
    refine ⟨438562421305360396615907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 18711996642362043588945365 438562421305360396615907)
    ·
      refine ⟨657843631958040594923861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438562421305360396615907 657843631958040594923861)
      ·
        refine ⟨1927276265502072055441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 657843631958040594923861 1927276265502072055441)
        ·
          rfl

theorem cell19_513037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 10].length) (baseStart_513037 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513037 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513037 prefixEnd_513037 := by exact prefixLift 513037
  have htrace : WordTrace (prefixWord ++ tailWord_513037) baseStart_513037 baseEnd_513037 := by
    simpa [prefixWord, tailWord_513037, baseEnd_513037] using wordTrace_append hprefix tailTrace_513037
  have hstable : (prefixWord ++ tailWord_513037).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513037).length < 2 ^ (prefixWord ++ tailWord_513037).sum := by decide
  have hdescent : baseEnd_513037 < baseStart_513037 := by decide
  rcases family_descends (prefixWord ++ tailWord_513037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513128 : List Nat := [2, 1, 4, 4, 1, 2, 2, 3]
def baseStart_513128 : Nat := 118140960795 + 513128 * 2 ^ 59
def prefixEnd_513128 : Nat := 4983230072969 + 3 ^ 40 * 513128 * 2
def baseEnd_513128 : Nat := 156137067425406588468251

theorem tailTrace_513128 : CollatzResearch.WordTrace tailWord_513128 prefixEnd_513128 156137067425406588468251 := by
  unfold tailWord_513128
  simp only [CollatzResearch.WordTrace]
  refine ⟨9357657842516183065254019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12476877123354910753672025 9357657842516183065254019)
  ·
    refine ⟨14036486763774274597881029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9357657842516183065254019 14036486763774274597881029)
    ·
      refine ⟨2631841268207676487102693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14036486763774274597881029 2631841268207676487102693)
      ·
        refine ⟨493470237788939341331755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2631841268207676487102693 493470237788939341331755)
        ·
          refine ⟨740205356683409011997633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493470237788939341331755 740205356683409011997633)
          ·
            refine ⟨555154017512556758998225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740205356683409011997633 555154017512556758998225)
            ·
              refine ⟨416365513134417569248669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555154017512556758998225 416365513134417569248669)
              ·
                refine ⟨156137067425406588468251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416365513134417569248669 156137067425406588468251)
                ·
                  rfl

theorem cell19_513128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_513128 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513128 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513128 prefixEnd_513128 := by exact prefixLift 513128
  have htrace : WordTrace (prefixWord ++ tailWord_513128) baseStart_513128 baseEnd_513128 := by
    simpa [prefixWord, tailWord_513128, baseEnd_513128] using wordTrace_append hprefix tailTrace_513128
  have hstable : (prefixWord ++ tailWord_513128).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513128).length < 2 ^ (prefixWord ++ tailWord_513128).sum := by decide
  have hdescent : baseEnd_513128 < baseStart_513128 := by decide
  rcases family_descends (prefixWord ++ tailWord_513128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513130 : List Nat := [3, 1, 3, 2, 2, 3, 2, 3]
def baseStart_513130 : Nat := 118140960795 + 513130 * 2 ^ 59
def prefixEnd_513130 : Nat := 4983230072969 + 3 ^ 40 * 513130 * 2
def baseEnd_513130 : Nat := 156137675995071176423801

theorem tailTrace_513130 : CollatzResearch.WordTrace tailWord_513130 prefixEnd_513130 156137675995071176423801 := by
  unfold tailWord_513130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678847157756280118020211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12476925754016746981387229 4678847157756280118020211)
  ·
    refine ⟨7018270736634420177030317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4678847157756280118020211 7018270736634420177030317)
    ·
      refine ⟨2631851526237907566386369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7018270736634420177030317 2631851526237907566386369)
      ·
        refine ⟨1973888644678430674789777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2631851526237907566386369 1973888644678430674789777)
        ·
          refine ⟨1480416483508823006092333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1973888644678430674789777 1480416483508823006092333)
          ·
            refine ⟨555156181315808627284625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1480416483508823006092333 555156181315808627284625)
            ·
              refine ⟨416367135986856470463469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555156181315808627284625 416367135986856470463469)
              ·
                refine ⟨156137675995071176423801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416367135986856470463469 156137675995071176423801)
                ·
                  rfl

theorem cell19_513130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_513130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513130 prefixEnd_513130 := by exact prefixLift 513130
  have htrace : WordTrace (prefixWord ++ tailWord_513130) baseStart_513130 baseEnd_513130 := by
    simpa [prefixWord, tailWord_513130, baseEnd_513130] using wordTrace_append hprefix tailTrace_513130
  have hstable : (prefixWord ++ tailWord_513130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513130).length < 2 ^ (prefixWord ++ tailWord_513130).sum := by decide
  have hdescent : baseEnd_513130 < baseStart_513130 := by decide
  rcases family_descends (prefixWord ++ tailWord_513130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513153 : List Nat := [1, 2, 4, 2, 2, 1, 7]
def baseStart_513153 : Nat := 118140960795 + 513153 * 2 ^ 59
def prefixEnd_513153 : Nat := 4983230072969 + 3 ^ 40 * 513153 * 2
def baseEnd_513153 : Nat := 52048224848737979304209

theorem tailTrace_513153 : CollatzResearch.WordTrace tailWord_513153 prefixEnd_513153 52048224848737979304209 := by
  unfold tailWord_513153
  simp only [CollatzResearch.WordTrace]
  refine ⟨18716227509941795400168113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12477485006627863600112075 18716227509941795400168113)
  ·
    refine ⟨14037170632456346550126085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18716227509941795400168113 14037170632456346550126085)
    ·
      refine ⟨2631969493585564978148641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14037170632456346550126085 2631969493585564978148641)
      ·
        refine ⟨1973977120189173733611481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2631969493585564978148641 1973977120189173733611481)
        ·
          refine ⟨1480482840141880300208611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1973977120189173733611481 1480482840141880300208611)
          ·
            refine ⟨2220724260212820450312917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480482840141880300208611 2220724260212820450312917)
            ·
              refine ⟨52048224848737979304209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2220724260212820450312917 52048224848737979304209)
              ·
                rfl

theorem cell19_513153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_513153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513153 prefixEnd_513153 := by exact prefixLift 513153
  have htrace : WordTrace (prefixWord ++ tailWord_513153) baseStart_513153 baseEnd_513153 := by
    simpa [prefixWord, tailWord_513153, baseEnd_513153] using wordTrace_append hprefix tailTrace_513153
  have hstable : (prefixWord ++ tailWord_513153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513153).length < 2 ^ (prefixWord ++ tailWord_513153).sum := by decide
  have hdescent : baseEnd_513153 < baseStart_513153 := by decide
  rcases family_descends (prefixWord ++ tailWord_513153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513170 : List Nat := [3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_513170 : Nat := 118140960795 + 513170 * 2 ^ 59
def prefixEnd_513170 : Nat := 4983230072969 + 3 ^ 40 * 513170 * 2
def baseEnd_513170 : Nat := 156149847388362935534803

theorem tailTrace_513170 : CollatzResearch.WordTrace tailWord_513170 prefixEnd_513170 156149847388362935534803 := by
  unfold tailWord_513170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4679211887720051825884241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12477898367253471535691309 4679211887720051825884241)
  ·
    refine ⟨3509408915790038869413181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4679211887720051825884241 3509408915790038869413181)
    ·
      refine ⟨1316028343421264576029943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3509408915790038869413181 1316028343421264576029943)
      ·
        refine ⟨1974042515131896864044915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316028343421264576029943 1974042515131896864044915)
        ·
          refine ⟨2961063772697845296067373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974042515131896864044915 2961063772697845296067373)
          ·
            refine ⟨1110398914761691986025265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2961063772697845296067373 1110398914761691986025265)
            ·
              refine ⟨832799186071268989518949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110398914761691986025265 832799186071268989518949)
              ·
                refine ⟨156149847388362935534803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832799186071268989518949 156149847388362935534803)
                ·
                  rfl

theorem cell19_513170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_513170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513170 prefixEnd_513170 := by exact prefixLift 513170
  have htrace : WordTrace (prefixWord ++ tailWord_513170) baseStart_513170 baseEnd_513170 := by
    simpa [prefixWord, tailWord_513170, baseEnd_513170] using wordTrace_append hprefix tailTrace_513170
  have hstable : (prefixWord ++ tailWord_513170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513170).length < 2 ^ (prefixWord ++ tailWord_513170).sum := by decide
  have hdescent : baseEnd_513170 < baseStart_513170 := by decide
  rcases family_descends (prefixWord ++ tailWord_513170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513206 : List Nat := [5, 1, 3, 2, 1, 7]
def baseStart_513206 : Nat := 118140960795 + 513206 * 2 ^ 59
def prefixEnd_513206 : Nat := 4983230072969 + 3 ^ 40 * 513206 * 2
def baseEnd_513206 : Nat := 17351200182480613192745

theorem tailTrace_513206 : CollatzResearch.WordTrace tailWord_513206 prefixEnd_513206 17351200182480613192745 := by
  unfold tailWord_513206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1169885036171861590740467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12478773719166523634564981 1169885036171861590740467)
  ·
    refine ⟨1754827554257792386110701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1169885036171861590740467 1754827554257792386110701)
    ·
      refine ⟨658060332846672144791513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1754827554257792386110701 658060332846672144791513)
      ·
        refine ⟨493545249635004108593635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658060332846672144791513 493545249635004108593635)
        ·
          refine ⟨740317874452506162890453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493545249635004108593635 740317874452506162890453)
          ·
            refine ⟨17351200182480613192745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 740317874452506162890453 17351200182480613192745)
            ·
              rfl

theorem cell19_513206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 7].length) (baseStart_513206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513206 prefixEnd_513206 := by exact prefixLift 513206
  have htrace : WordTrace (prefixWord ++ tailWord_513206) baseStart_513206 baseEnd_513206 := by
    simpa [prefixWord, tailWord_513206, baseEnd_513206] using wordTrace_append hprefix tailTrace_513206
  have hstable : (prefixWord ++ tailWord_513206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513206).length < 2 ^ (prefixWord ++ tailWord_513206).sum := by decide
  have hdescent : baseEnd_513206 < baseStart_513206 := by decide
  rcases family_descends (prefixWord ++ tailWord_513206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513231 : List Nat := [1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_513231 : Nat := 118140960795 + 513231 * 2 ^ 59
def prefixEnd_513231 : Nat := 4983230072969 + 3 ^ 40 * 513231 * 2
def baseEnd_513231 : Nat := 156168408763132868179081

theorem tailTrace_513231 : CollatzResearch.WordTrace tailWord_513231 prefixEnd_513231 156168408763132868179081 := by
  unfold tailWord_513231
  simp only [CollatzResearch.WordTrace]
  refine ⟨18719072403659214721507547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12479381602439476481005031 18719072403659214721507547)
  ·
    refine ⟨28078608605488822082261321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18719072403659214721507547 28078608605488822082261321)
    ·
      refine ⟨21058956454116616561695991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28078608605488822082261321 21058956454116616561695991)
      ·
        refine ⟨31588434681174924842543987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21058956454116616561695991 31588434681174924842543987)
        ·
          refine ⟨47382652021762387263815981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31588434681174924842543987 47382652021762387263815981)
          ·
            refine ⟨17768494508160895223930993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47382652021762387263815981 17768494508160895223930993)
            ·
              refine ⟨13326370881120671417948245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17768494508160895223930993 13326370881120671417948245)
              ·
                refine ⟨156168408763132868179081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13326370881120671417948245 156168408763132868179081)
                ·
                  rfl

theorem cell19_513231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_513231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513231 prefixEnd_513231 := by exact prefixLift 513231
  have htrace : WordTrace (prefixWord ++ tailWord_513231) baseStart_513231 baseEnd_513231 := by
    simpa [prefixWord, tailWord_513231, baseEnd_513231] using wordTrace_append hprefix tailTrace_513231
  have hstable : (prefixWord ++ tailWord_513231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513231).length < 2 ^ (prefixWord ++ tailWord_513231).sum := by decide
  have hdescent : baseEnd_513231 < baseStart_513231 := by decide
  rcases family_descends (prefixWord ++ tailWord_513231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513322 : List Nat := [3, 1, 4, 2, 1, 3, 5]
def baseStart_513322 : Nat := 118140960795 + 513322 * 2 ^ 59
def prefixEnd_513322 : Nat := 4983230072969 + 3 ^ 40 * 513322 * 2
def baseEnd_513322 : Nat := 52065366227623873385537

theorem tailTrace_513322 : CollatzResearch.WordTrace tailWord_513322 prefixEnd_513322 52065366227623873385537 := by
  unfold tailWord_513322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680597861582384315767555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12481594297553024842046813 4680597861582384315767555)
  ·
    refine ⟨7020896792373576473651333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4680597861582384315767555 7020896792373576473651333)
    ·
      refine ⟨1316418148570045588809625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7020896792373576473651333 1316418148570045588809625)
      ·
        refine ⟨987313611427534191607219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1316418148570045588809625 987313611427534191607219)
        ·
          refine ⟨1480970417141301287410829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987313611427534191607219 1480970417141301287410829)
          ·
            refine ⟨555363906427987982779061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1480970417141301287410829 555363906427987982779061)
            ·
              refine ⟨52065366227623873385537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 555363906427987982779061 52065366227623873385537)
              ·
                rfl

theorem cell19_513322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_513322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513322 prefixEnd_513322 := by exact prefixLift 513322
  have htrace : WordTrace (prefixWord ++ tailWord_513322) baseStart_513322 baseEnd_513322 := by
    simpa [prefixWord, tailWord_513322, baseEnd_513322] using wordTrace_append hprefix tailTrace_513322
  have hstable : (prefixWord ++ tailWord_513322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513322).length < 2 ^ (prefixWord ++ tailWord_513322).sum := by decide
  have hdescent : baseEnd_513322 < baseStart_513322 := by decide
  rcases family_descends (prefixWord ++ tailWord_513322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513343 : List Nat := [1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_513343 : Nat := 118140960795 + 513343 * 2 ^ 59
def prefixEnd_513343 : Nat := 4983230072969 + 3 ^ 40 * 513343 * 2
def baseEnd_513343 : Nat := 156202488664349793689887

theorem tailTrace_513343 : CollatzResearch.WordTrace tailWord_513343 prefixEnd_513343 156202488664349793689887 := by
  unfold tailWord_513343
  simp only [CollatzResearch.WordTrace]
  refine ⟨18723157379253457849584683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12482104919502305233056455 18723157379253457849584683)
  ·
    refine ⟨28084736068880186774377025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18723157379253457849584683 28084736068880186774377025)
    ·
      refine ⟨21063552051660140080782769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28084736068880186774377025 21063552051660140080782769)
      ·
        refine ⟨15797664038745105060587077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21063552051660140080782769 15797664038745105060587077)
        ·
          refine ⟨2962062007264707198860077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15797664038745105060587077 2962062007264707198860077)
          ·
            refine ⟨1110773252724265199572529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2962062007264707198860077 1110773252724265199572529)
            ·
              refine ⟨833079939543198899679397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110773252724265199572529 833079939543198899679397)
              ·
                refine ⟨156202488664349793689887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 833079939543198899679397 156202488664349793689887)
                ·
                  rfl

theorem cell19_513343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_513343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513343 prefixEnd_513343 := by exact prefixLift 513343
  have htrace : WordTrace (prefixWord ++ tailWord_513343) baseStart_513343 baseEnd_513343 := by
    simpa [prefixWord, tailWord_513343, baseEnd_513343] using wordTrace_append hprefix tailTrace_513343
  have hstable : (prefixWord ++ tailWord_513343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513343).length < 2 ^ (prefixWord ++ tailWord_513343).sum := by decide
  have hdescent : baseEnd_513343 < baseStart_513343 := by decide
  rcases family_descends (prefixWord ++ tailWord_513343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513383 : List Nat := [1, 1, 5, 1, 11]
def baseStart_513383 : Nat := 118140960795 + 513383 * 2 ^ 59
def prefixEnd_513383 : Nat := 4983230072969 + 3 ^ 40 * 513383 * 2
def baseEnd_513383 : Nat := 5785728150283020474107

theorem tailTrace_513383 : CollatzResearch.WordTrace tailWord_513383 prefixEnd_513383 5785728150283020474107 := by
  unfold tailWord_513383
  simp only [CollatzResearch.WordTrace]
  refine ⟨18724616299108544681040803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12483077532739029787360535 18724616299108544681040803)
  ·
    refine ⟨28086924448662817021561205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18724616299108544681040803 28086924448662817021561205)
    ·
      refine ⟨2633149167062139095771363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28086924448662817021561205 2633149167062139095771363)
      ·
        refine ⟨3949723750593208643657045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2633149167062139095771363 3949723750593208643657045)
        ·
          refine ⟨5785728150283020474107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3949723750593208643657045 5785728150283020474107)
          ·
            rfl

theorem cell19_513383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 11].length) (baseStart_513383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513383 prefixEnd_513383 := by exact prefixLift 513383
  have htrace : WordTrace (prefixWord ++ tailWord_513383) baseStart_513383 baseEnd_513383 := by
    simpa [prefixWord, tailWord_513383, baseEnd_513383] using wordTrace_append hprefix tailTrace_513383
  have hstable : (prefixWord ++ tailWord_513383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513383).length < 2 ^ (prefixWord ++ tailWord_513383).sum := by decide
  have hdescent : baseEnd_513383 < baseStart_513383 := by decide
  rcases family_descends (prefixWord ++ tailWord_513383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513417 : List Nat := [1, 2, 1, 1, 7, 1, 3, 3]
def baseStart_513417 : Nat := 118140960795 + 513417 * 2 ^ 59
def prefixEnd_513417 : Nat := 4983230072969 + 3 ^ 40 * 513417 * 2
def baseEnd_513417 : Nat := 156225005741939548045241

theorem tailTrace_513417 : CollatzResearch.WordTrace tailWord_513417 prefixEnd_513417 156225005741939548045241 := by
  unfold tailWord_513417
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725856380985368487778505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12483904253990245658519003 18725856380985368487778505)
  ·
    refine ⟨14044392285739026365833879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18725856380985368487778505 14044392285739026365833879)
    ·
      refine ⟨21066588428608539548750819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14044392285739026365833879 21066588428608539548750819)
      ·
        refine ⟨31599882642912809323126229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21066588428608539548750819 31599882642912809323126229)
        ·
          refine ⟨740622249443268968510771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31599882642912809323126229 740622249443268968510771)
          ·
            refine ⟨1110933374164903452766157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740622249443268968510771 1110933374164903452766157)
            ·
              refine ⟨416600015311838794787309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1110933374164903452766157 416600015311838794787309)
              ·
                refine ⟨156225005741939548045241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416600015311838794787309 156225005741939548045241)
                ·
                  rfl

theorem cell19_513417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 3].length) (baseStart_513417 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513417 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513417 prefixEnd_513417 := by exact prefixLift 513417
  have htrace : WordTrace (prefixWord ++ tailWord_513417) baseStart_513417 baseEnd_513417 := by
    simpa [prefixWord, tailWord_513417, baseEnd_513417] using wordTrace_append hprefix tailTrace_513417
  have hstable : (prefixWord ++ tailWord_513417).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513417).length < 2 ^ (prefixWord ++ tailWord_513417).sum := by decide
  have hdescent : baseEnd_513417 < baseStart_513417 := by decide
  rcases family_descends (prefixWord ++ tailWord_513417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513419 : List Nat := [1, 1, 1, 1, 4, 3, 5, 3]
def baseStart_513419 : Nat := 118140960795 + 513419 * 2 ^ 59
def prefixEnd_513419 : Nat := 4983230072969 + 3 ^ 40 * 513419 * 2
def baseEnd_513419 : Nat := 156225614311604136000791

theorem tailTrace_513419 : CollatzResearch.WordTrace tailWord_513419 prefixEnd_513419 156225614311604136000791 := by
  unfold tailWord_513419
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725929326978122829351311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12483952884652081886234207 18725929326978122829351311)
  ·
    refine ⟨28088893990467184244026967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18725929326978122829351311 28088893990467184244026967)
    ·
      refine ⟨42133340985700776366040451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28088893990467184244026967 42133340985700776366040451)
      ·
        refine ⟨63200011478551164549060677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42133340985700776366040451 63200011478551164549060677)
        ·
          refine ⟨11850002152228343352948877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63200011478551164549060677 11850002152228343352948877)
          ·
            refine ⟨4443750807085628757355829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11850002152228343352948877 4443750807085628757355829)
            ·
              refine ⟨416601638164277696002109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4443750807085628757355829 416601638164277696002109)
              ·
                refine ⟨156225614311604136000791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416601638164277696002109 156225614311604136000791)
                ·
                  rfl

theorem cell19_513419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 3].length) (baseStart_513419 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513419 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513419 prefixEnd_513419 := by exact prefixLift 513419
  have htrace : WordTrace (prefixWord ++ tailWord_513419) baseStart_513419 baseEnd_513419 := by
    simpa [prefixWord, tailWord_513419, baseEnd_513419] using wordTrace_append hprefix tailTrace_513419
  have hstable : (prefixWord ++ tailWord_513419).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513419).length < 2 ^ (prefixWord ++ tailWord_513419).sum := by decide
  have hdescent : baseEnd_513419 < baseStart_513419 := by decide
  rcases family_descends (prefixWord ++ tailWord_513419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513436 : List Nat := [2, 2, 3, 4, 1, 1, 6]
def baseStart_513436 : Nat := 118140960795 + 513436 * 2 ^ 59
def prefixEnd_513436 : Nat := 4983230072969 + 3 ^ 40 * 513436 * 2
def baseEnd_513436 : Nat := 52076929051251044540989

theorem tailTrace_513436 : CollatzResearch.WordTrace tailWord_513436 prefixEnd_513436 52076929051251044540989 := by
  unfold tailWord_513436
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363274683958267366360081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12484366245277689821813441 9363274683958267366360081)
  ·
    refine ⟨7022456012968700524770061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9363274683958267366360081 7022456012968700524770061)
    ·
      refine ⟨2633421004863262696788773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7022456012968700524770061 2633421004863262696788773)
      ·
        refine ⟨493766438411861755647895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2633421004863262696788773 493766438411861755647895)
        ·
          refine ⟨740649657617792633471843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493766438411861755647895 740649657617792633471843)
          ·
            refine ⟨1110974486426688950207765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740649657617792633471843 1110974486426688950207765)
            ·
              refine ⟨52076929051251044540989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1110974486426688950207765 52076929051251044540989)
              ·
                rfl

theorem cell19_513436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 6].length) (baseStart_513436 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513436 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513436 prefixEnd_513436 := by exact prefixLift 513436
  have htrace : WordTrace (prefixWord ++ tailWord_513436) baseStart_513436 baseEnd_513436 := by
    simpa [prefixWord, tailWord_513436, baseEnd_513436] using wordTrace_append hprefix tailTrace_513436
  have hstable : (prefixWord ++ tailWord_513436).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513436).length < 2 ^ (prefixWord ++ tailWord_513436).sum := by decide
  have hdescent : baseEnd_513436 < baseStart_513436 := by decide
  rcases family_descends (prefixWord ++ tailWord_513436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513440 : List Nat := [2, 1, 1, 4, 1, 2, 8]
def baseStart_513440 : Nat := 118140960795 + 513440 * 2 ^ 59
def prefixEnd_513440 : Nat := 4983230072969 + 3 ^ 40 * 513440 * 2
def baseEnd_513440 : Nat := 52077334764360769844689

theorem tailTrace_513440 : CollatzResearch.WordTrace tailWord_513440 prefixEnd_513440 52077334764360769844689 := by
  unfold tailWord_513440
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363347629951021707932887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12484463506601362277243849 9363347629951021707932887)
  ·
    refine ⟨14045021444926532561899331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9363347629951021707932887 14045021444926532561899331)
    ·
      refine ⟨21067532167389798842848997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14045021444926532561899331 21067532167389798842848997)
      ·
        refine ⟨3950162281385587283034187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21067532167389798842848997 3950162281385587283034187)
        ·
          refine ⟨5925243422078380924551281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950162281385587283034187 5925243422078380924551281)
          ·
            refine ⟨4443932566558785693413461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5925243422078380924551281 4443932566558785693413461)
            ·
              refine ⟨52077334764360769844689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4443932566558785693413461 52077334764360769844689)
              ·
                rfl

theorem cell19_513440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_513440 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513440 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513440 prefixEnd_513440 := by exact prefixLift 513440
  have htrace : WordTrace (prefixWord ++ tailWord_513440) baseStart_513440 baseEnd_513440 := by
    simpa [prefixWord, tailWord_513440, baseEnd_513440] using wordTrace_append hprefix tailTrace_513440
  have hstable : (prefixWord ++ tailWord_513440).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513440).length < 2 ^ (prefixWord ++ tailWord_513440).sum := by decide
  have hdescent : baseEnd_513440 < baseStart_513440 := by decide
  rcases family_descends (prefixWord ++ tailWord_513440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513497 : List Nat := [1, 2, 1, 2, 4, 2, 7]
def baseStart_513497 : Nat := 118140960795 + 513497 * 2 ^ 59
def prefixEnd_513497 : Nat := 4983230072969 + 3 ^ 40 * 513497 * 2
def baseEnd_513497 : Nat := 52083116176174355422415

theorem tailTrace_513497 : CollatzResearch.WordTrace tailWord_513497 prefixEnd_513497 52083116176174355422415 := by
  unfold tailWord_513497
  simp only [CollatzResearch.WordTrace]
  refine ⟨18728774220695542150690745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12485849480463694767127163 18728774220695542150690745)
  ·
    refine ⟨14046580665521656613018059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18728774220695542150690745 14046580665521656613018059)
    ·
      refine ⟨21069870998282484919527089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14046580665521656613018059 21069870998282484919527089)
      ·
        refine ⟨15802403248711863689645317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21069870998282484919527089 15802403248711863689645317)
        ·
          refine ⟨2962950609133474441808497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15802403248711863689645317 2962950609133474441808497)
          ·
            refine ⟨2222212956850105831356373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2962950609133474441808497 2222212956850105831356373)
            ·
              refine ⟨52083116176174355422415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2222212956850105831356373 52083116176174355422415)
              ·
                rfl

theorem cell19_513497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_513497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513497 prefixEnd_513497 := by exact prefixLift 513497
  have htrace : WordTrace (prefixWord ++ tailWord_513497) baseStart_513497 baseEnd_513497 := by
    simpa [prefixWord, tailWord_513497, baseEnd_513497] using wordTrace_append hprefix tailTrace_513497
  have hstable : (prefixWord ++ tailWord_513497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513497).length < 2 ^ (prefixWord ++ tailWord_513497).sum := by decide
  have hdescent : baseEnd_513497 < baseStart_513497 := by decide
  rcases family_descends (prefixWord ++ tailWord_513497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513687 : List Nat := [1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_513687 : Nat := 118140960795 + 513687 * 2 ^ 59
def prefixEnd_513687 : Nat := 4983230072969 + 3 ^ 40 * 513687 * 2
def baseEnd_513687 : Nat := 156307162646658922044505

theorem tailTrace_513687 : CollatzResearch.WordTrace tailWord_513687 prefixEnd_513687 156307162646658922044505 := by
  unfold tailWord_513687
  simp only [CollatzResearch.WordTrace]
  refine ⟨18735704090007204600107315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12490469393338136400071543 18735704090007204600107315)
  ·
    refine ⟨28103556135010806900160973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18735704090007204600107315 28103556135010806900160973)
    ·
      refine ⟨10538833550629052587560365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28103556135010806900160973 10538833550629052587560365)
      ·
        refine ⟨3952062581485894720335137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10538833550629052587560365 3952062581485894720335137)
        ·
          refine ⟨2964046936114421040251353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3952062581485894720335137 2964046936114421040251353)
          ·
            refine ⟨2223035202085815780188515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2964046936114421040251353 2223035202085815780188515)
            ·
              refine ⟨3334552803128723670282773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223035202085815780188515 3334552803128723670282773)
              ·
                refine ⟨156307162646658922044505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3334552803128723670282773 156307162646658922044505)
                ·
                  rfl

theorem cell19_513687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_513687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513687 prefixEnd_513687 := by exact prefixLift 513687
  have htrace : WordTrace (prefixWord ++ tailWord_513687) baseStart_513687 baseEnd_513687 := by
    simpa [prefixWord, tailWord_513687, baseEnd_513687] using wordTrace_append hprefix tailTrace_513687
  have hstable : (prefixWord ++ tailWord_513687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513687).length < 2 ^ (prefixWord ++ tailWord_513687).sum := by decide
  have hdescent : baseEnd_513687 < baseStart_513687 := by decide
  rcases family_descends (prefixWord ++ tailWord_513687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513740 : List Nat := [2, 2, 1, 5, 2, 2, 1, 4]
def baseStart_513740 : Nat := 118140960795 + 513740 * 2 ^ 59
def prefixEnd_513740 : Nat := 4983230072969 + 3 ^ 40 * 513740 * 2
def baseEnd_513740 : Nat := 156323289742770502866583

theorem tailTrace_513740 : CollatzResearch.WordTrace tailWord_513740 prefixEnd_513740 156323289742770502866583 := by
  unfold tailWord_513740
  simp only [CollatzResearch.WordTrace]
  refine ⟨9368818579407597325893337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12491758105876796434524449 9368818579407597325893337)
  ·
    refine ⟨7026613934555697994420003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9368818579407597325893337 7026613934555697994420003)
    ·
      refine ⟨10539920901833546991630005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7026613934555697994420003 10539920901833546991630005)
      ·
        refine ⟨988117584546895030465313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10539920901833546991630005 988117584546895030465313)
        ·
          refine ⟨741088188410171272848985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988117584546895030465313 741088188410171272848985)
          ·
            refine ⟨555816141307628454636739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741088188410171272848985 555816141307628454636739)
            ·
              refine ⟨833724211961442681955109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555816141307628454636739 833724211961442681955109)
              ·
                refine ⟨156323289742770502866583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 833724211961442681955109 156323289742770502866583)
                ·
                  rfl

theorem cell19_513740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_513740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513740 prefixEnd_513740 := by exact prefixLift 513740
  have htrace : WordTrace (prefixWord ++ tailWord_513740) baseStart_513740 baseEnd_513740 := by
    simpa [prefixWord, tailWord_513740, baseEnd_513740] using wordTrace_append hprefix tailTrace_513740
  have hstable : (prefixWord ++ tailWord_513740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513740).length < 2 ^ (prefixWord ++ tailWord_513740).sum := by decide
  have hdescent : baseEnd_513740 < baseStart_513740 := by decide
  rcases family_descends (prefixWord ++ tailWord_513740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513757 : List Nat := [1, 4, 3, 3, 1, 1, 3, 3]
def baseStart_513757 : Nat := 118140960795 + 513757 * 2 ^ 59
def prefixEnd_513757 : Nat := 4983230072969 + 3 ^ 40 * 513757 * 2
def baseEnd_513757 : Nat := 156328462584919500488759

theorem tailTrace_513757 : CollatzResearch.WordTrace tailWord_513757 prefixEnd_513757 156328462584919500488759 := by
  unfold tailWord_513757
  simp only [CollatzResearch.WordTrace]
  refine ⟨18738257199753606555155525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12492171466502404370103683 18738257199753606555155525)
  ·
    refine ⟨3513423224953801229091661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18738257199753606555155525 3513423224953801229091661)
    ·
      refine ⟨1317533709357675460909373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3513423224953801229091661 1317533709357675460909373)
      ·
        refine ⟨494075141009128297841015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1317533709357675460909373 494075141009128297841015)
        ·
          refine ⟨741112711513692446761523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494075141009128297841015 741112711513692446761523)
          ·
            refine ⟨1111669067270538670142285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741112711513692446761523 1111669067270538670142285)
            ·
              refine ⟨416875900226452001303357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1111669067270538670142285 416875900226452001303357)
              ·
                refine ⟨156328462584919500488759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416875900226452001303357 156328462584919500488759)
                ·
                  rfl

theorem cell19_513757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 3].length) (baseStart_513757 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513757 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513757 prefixEnd_513757 := by exact prefixLift 513757
  have htrace : WordTrace (prefixWord ++ tailWord_513757) baseStart_513757 baseEnd_513757 := by
    simpa [prefixWord, tailWord_513757, baseEnd_513757] using wordTrace_append hprefix tailTrace_513757
  have hstable : (prefixWord ++ tailWord_513757).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513757).length < 2 ^ (prefixWord ++ tailWord_513757).sum := by decide
  have hdescent : baseEnd_513757 < baseStart_513757 := by decide
  rcases family_descends (prefixWord ++ tailWord_513757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513818 : List Nat := [3, 1, 1, 3, 2, 2, 4, 3]
def baseStart_513818 : Nat := 118140960795 + 513818 * 2 ^ 59
def prefixEnd_513818 : Nat := 4983230072969 + 3 ^ 40 * 513818 * 2
def baseEnd_513818 : Nat := 156347023959689433133037

theorem tailTrace_513818 : CollatzResearch.WordTrace tailWord_513818 prefixEnd_513818 156347023959689433133037 := by
  unfold tailWord_513818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685120513133153493281527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12493654701688409315417405 4685120513133153493281527)
  ·
    refine ⟨7027680769699730239922291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685120513133153493281527 7027680769699730239922291)
    ·
      refine ⟨10541521154549595359883437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7027680769699730239922291 10541521154549595359883437)
      ·
        refine ⟨3953070432956098259956289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10541521154549595359883437 3953070432956098259956289)
        ·
          refine ⟨2964802824717073694967217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3953070432956098259956289 2964802824717073694967217)
          ·
            refine ⟨2223602118537805271225413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2964802824717073694967217 2223602118537805271225413)
            ·
              refine ⟨416925397225838488354765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2223602118537805271225413 416925397225838488354765)
              ·
                refine ⟨156347023959689433133037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416925397225838488354765 156347023959689433133037)
                ·
                  rfl

theorem cell19_513818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_513818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513818 prefixEnd_513818 := by exact prefixLift 513818
  have htrace : WordTrace (prefixWord ++ tailWord_513818) baseStart_513818 baseEnd_513818 := by
    simpa [prefixWord, tailWord_513818, baseEnd_513818] using wordTrace_append hprefix tailTrace_513818
  have hstable : (prefixWord ++ tailWord_513818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513818).length < 2 ^ (prefixWord ++ tailWord_513818).sum := by decide
  have hdescent : baseEnd_513818 < baseStart_513818 := by decide
  rcases family_descends (prefixWord ++ tailWord_513818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513820 : List Nat := [2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_513820 : Nat := 118140960795 + 513820 * 2 ^ 59
def prefixEnd_513820 : Nat := 4983230072969 + 3 ^ 40 * 513820 * 2
def baseEnd_513820 : Nat := 156347632529354021088587

theorem tailTrace_513820 : CollatzResearch.WordTrace tailWord_513820 prefixEnd_513820 156347632529354021088587 := by
  unfold tailWord_513820
  simp only [CollatzResearch.WordTrace]
  refine ⟨9370277499262684157349457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12493703332350245543132609 9370277499262684157349457)
  ·
    refine ⟨7027708124447013118012093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9370277499262684157349457 7027708124447013118012093)
    ·
      refine ⟨2635390546667629919254535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7027708124447013118012093 2635390546667629919254535)
      ·
        refine ⟨3953085820001444878881803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2635390546667629919254535 3953085820001444878881803)
        ·
          refine ⟨5929628730002167318322705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3953085820001444878881803 5929628730002167318322705)
          ·
            refine ⟨4447221547501625488742029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5929628730002167318322705 4447221547501625488742029)
            ·
              refine ⟨1667708080313109558278261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4447221547501625488742029 1667708080313109558278261)
              ·
                refine ⟨156347632529354021088587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1667708080313109558278261 156347632529354021088587)
                ·
                  rfl

theorem cell19_513820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_513820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513820 prefixEnd_513820 := by exact prefixLift 513820
  have htrace : WordTrace (prefixWord ++ tailWord_513820) baseStart_513820 baseEnd_513820 := by
    simpa [prefixWord, tailWord_513820, baseEnd_513820] using wordTrace_append hprefix tailTrace_513820
  have hstable : (prefixWord ++ tailWord_513820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513820).length < 2 ^ (prefixWord ++ tailWord_513820).sum := by decide
  have hdescent : baseEnd_513820 < baseStart_513820 := by decide
  rcases family_descends (prefixWord ++ tailWord_513820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513877 : List Nat := [1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_513877 : Nat := 118140960795 + 513877 * 2 ^ 59
def prefixEnd_513877 : Nat := 4983230072969 + 3 ^ 40 * 513877 * 2
def baseEnd_513877 : Nat := 156364976764794777821765

theorem tailTrace_513877 : CollatzResearch.WordTrace tailWord_513877 prefixEnd_513877 156364976764794777821765 := by
  unfold tailWord_513877
  simp only [CollatzResearch.WordTrace]
  refine ⟨18742633959318867049523885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12495089306212578033015923 18742633959318867049523885)
  ·
    refine ⟨7028487734744575143571457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18742633959318867049523885 7028487734744575143571457)
    ·
      refine ⟨5271365801058431357678593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7028487734744575143571457 5271365801058431357678593)
      ·
        refine ⟨3953524350793823518258945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5271365801058431357678593 3953524350793823518258945)
        ·
          refine ⟨2965143263095367638694209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3953524350793823518258945 2965143263095367638694209)
          ·
            refine ⟨2223857447321525729020657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2965143263095367638694209 2223857447321525729020657)
            ·
              refine ⟨1667893085491144296765493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223857447321525729020657 1667893085491144296765493)
              ·
                refine ⟨156364976764794777821765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1667893085491144296765493 156364976764794777821765)
                ·
                  rfl

theorem cell19_513877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_513877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513877 prefixEnd_513877 := by exact prefixLift 513877
  have htrace : WordTrace (prefixWord ++ tailWord_513877) baseStart_513877 baseEnd_513877 := by
    simpa [prefixWord, tailWord_513877, baseEnd_513877] using wordTrace_append hprefix tailTrace_513877
  have hstable : (prefixWord ++ tailWord_513877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513877).length < 2 ^ (prefixWord ++ tailWord_513877).sum := by decide
  have hdescent : baseEnd_513877 < baseStart_513877 := by decide
  rcases family_descends (prefixWord ++ tailWord_513877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513930 : List Nat := [3, 1, 2, 4, 2, 1, 3, 3]
def baseStart_513930 : Nat := 118140960795 + 513930 * 2 ^ 59
def prefixEnd_513930 : Nat := 4983230072969 + 3 ^ 40 * 513930 * 2
def baseEnd_513930 : Nat := 156381103860906358643843

theorem tailTrace_513930 : CollatzResearch.WordTrace tailWord_513930 prefixEnd_513930 156381103860906358643843 := by
  unfold tailWord_513930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686141757031714275300811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12496378018751238067468829 4686141757031714275300811)
  ·
    refine ⟨7029212635547571412951217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4686141757031714275300811 7029212635547571412951217)
    ·
      refine ⟨5271909476660678559713413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7029212635547571412951217 5271909476660678559713413)
      ·
        refine ⟨988483026873877229946265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5271909476660678559713413 988483026873877229946265)
        ·
          refine ⟨741362270155407922459699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988483026873877229946265 741362270155407922459699)
          ·
            refine ⟨1112043405233111883689549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741362270155407922459699 1112043405233111883689549)
            ·
              refine ⟨417016276962416956383581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1112043405233111883689549 417016276962416956383581)
              ·
                refine ⟨156381103860906358643843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417016276962416956383581 156381103860906358643843)
                ·
                  rfl

theorem cell19_513930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_513930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513930 prefixEnd_513930 := by exact prefixLift 513930
  have htrace : WordTrace (prefixWord ++ tailWord_513930) baseStart_513930 baseEnd_513930 := by
    simpa [prefixWord, tailWord_513930, baseEnd_513930] using wordTrace_append hprefix tailTrace_513930
  have hstable : (prefixWord ++ tailWord_513930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513930).length < 2 ^ (prefixWord ++ tailWord_513930).sum := by decide
  have hdescent : baseEnd_513930 < baseStart_513930 := by decide
  rcases family_descends (prefixWord ++ tailWord_513930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_513993 : List Nat := [1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_513993 : Nat := 118140960795 + 513993 * 2 ^ 59
def prefixEnd_513993 : Nat := 4983230072969 + 3 ^ 40 * 513993 * 2
def baseEnd_513993 : Nat := 156400273805340879243671

theorem tailTrace_513993 : CollatzResearch.WordTrace tailWord_513993 prefixEnd_513993 156400273805340879243671 := by
  unfold tailWord_513993
  simp only [CollatzResearch.WordTrace]
  refine ⟨18746864826898618860746633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12497909884599079240497755 18746864826898618860746633)
  ·
    refine ⟨14060148620173964145559975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18746864826898618860746633 14060148620173964145559975)
    ·
      refine ⟨21090222930260946218339963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14060148620173964145559975 21090222930260946218339963)
      ·
        refine ⟨31635334395391419327509945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21090222930260946218339963 31635334395391419327509945)
        ·
          refine ⟨23726500796543564495632459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31635334395391419327509945 23726500796543564495632459)
          ·
            refine ⟨35589751194815346743448689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23726500796543564495632459 35589751194815346743448689)
            ·
              refine ⟨26692313396111510057586517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35589751194815346743448689 26692313396111510057586517)
              ·
                refine ⟨156400273805340879243671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26692313396111510057586517 156400273805340879243671)
                ·
                  rfl

theorem cell19_513993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_513993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_513993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_513993 prefixEnd_513993 := by exact prefixLift 513993
  have htrace : WordTrace (prefixWord ++ tailWord_513993) baseStart_513993 baseEnd_513993 := by
    simpa [prefixWord, tailWord_513993, baseEnd_513993] using wordTrace_append hprefix tailTrace_513993
  have hstable : (prefixWord ++ tailWord_513993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_513993).length < 2 ^ (prefixWord ++ tailWord_513993).sum := by decide
  have hdescent : baseEnd_513993 < baseStart_513993 := by decide
  rcases family_descends (prefixWord ++ tailWord_513993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514006 : List Nat := [5, 2, 1, 1, 3, 2, 5]
def baseStart_514006 : Nat := 118140960795 + 514006 * 2 ^ 59
def prefixEnd_514006 : Nat := 4983230072969 + 3 ^ 40 * 514006 * 2
def baseEnd_514006 : Nat := 52134743169386900318249

theorem tailTrace_514006 : CollatzResearch.WordTrace tailWord_514006 prefixEnd_514006 52134743169386900318249 := by
  unfold tailWord_514006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171708685990720130060617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12498225983901014720646581 1171708685990720130060617)
  ·
    refine ⟨878781514493040097545463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1171708685990720130060617 878781514493040097545463)
    ·
      refine ⟨1318172271739560146318195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878781514493040097545463 1318172271739560146318195)
      ·
        refine ⟨1977258407609340219477293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318172271739560146318195 1977258407609340219477293)
        ·
          refine ⟨741471902853502582303985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1977258407609340219477293 741471902853502582303985)
          ·
            refine ⟨556103927140126936727989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741471902853502582303985 556103927140126936727989)
            ·
              refine ⟨52134743169386900318249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 556103927140126936727989 52134743169386900318249)
              ·
                rfl

theorem cell19_514006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_514006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514006 prefixEnd_514006 := by exact prefixLift 514006
  have htrace : WordTrace (prefixWord ++ tailWord_514006) baseStart_514006 baseEnd_514006 := by
    simpa [prefixWord, tailWord_514006, baseEnd_514006] using wordTrace_append hprefix tailTrace_514006
  have hstable : (prefixWord ++ tailWord_514006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514006).length < 2 ^ (prefixWord ++ tailWord_514006).sum := by decide
  have hdescent : baseEnd_514006 < baseStart_514006 := by decide
  rcases family_descends (prefixWord ++ tailWord_514006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514046 : List Nat := [4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_514046 : Nat := 118140960795 + 514046 * 2 ^ 59
def prefixEnd_514046 : Nat := 4983230072969 + 3 ^ 40 * 514046 * 2
def baseEnd_514046 : Nat := 156416400901452460065749

theorem tailTrace_514046 : CollatzResearch.WordTrace tailWord_514046 prefixEnd_514046 156416400901452460065749 := by
  unfold tailWord_514046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343599736963326114053249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12499198597137739274950661 2343599736963326114053249)
  ·
    refine ⟨1757699802722494585539937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2343599736963326114053249 1757699802722494585539937)
    ·
      refine ⟨1318274852041870939154953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1757699802722494585539937 1318274852041870939154953)
      ·
        refine ⟨988706139031403204366215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1318274852041870939154953 988706139031403204366215)
        ·
          refine ⟨1483059208547104806549323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988706139031403204366215 1483059208547104806549323)
          ·
            refine ⟨2224588812820657209823985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483059208547104806549323 2224588812820657209823985)
            ·
              refine ⟨1668441609615492907367989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224588812820657209823985 1668441609615492907367989)
              ·
                refine ⟨156416400901452460065749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1668441609615492907367989 156416400901452460065749)
                ·
                  rfl

theorem cell19_514046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_514046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514046 prefixEnd_514046 := by exact prefixLift 514046
  have htrace : WordTrace (prefixWord ++ tailWord_514046) baseStart_514046 baseEnd_514046 := by
    simpa [prefixWord, tailWord_514046, baseEnd_514046] using wordTrace_append hprefix tailTrace_514046
  have hstable : (prefixWord ++ tailWord_514046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514046).length < 2 ^ (prefixWord ++ tailWord_514046).sum := by decide
  have hdescent : baseEnd_514046 < baseStart_514046 := by decide
  rcases family_descends (prefixWord ++ tailWord_514046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514061 : List Nat := [1, 7, 1, 2, 2, 6]
def baseStart_514061 : Nat := 118140960795 + 514061 * 2 ^ 59
def prefixEnd_514061 : Nat := 4983230072969 + 3 ^ 40 * 514061 * 2
def baseEnd_514061 : Nat := 17380107241548541081375

theorem tailTrace_514061 : CollatzResearch.WordTrace tailWord_514061 prefixEnd_514061 17380107241548541081375 := by
  unfold tailWord_514061
  simp only [CollatzResearch.WordTrace]
  refine ⟨18749344990652266474222037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12499563327101510982814691 18749344990652266474222037)
  ·
    refine ⟨439437773218412495489579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 18749344990652266474222037 439437773218412495489579)
    ·
      refine ⟨659156659827618743234369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439437773218412495489579 659156659827618743234369)
      ·
        refine ⟨494367494870714057425777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659156659827618743234369 494367494870714057425777)
        ·
          refine ⟨370775621153035543069333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494367494870714057425777 370775621153035543069333)
          ·
            refine ⟨17380107241548541081375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 370775621153035543069333 17380107241548541081375)
            ·
              rfl

theorem cell19_514061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 6].length) (baseStart_514061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514061 prefixEnd_514061 := by exact prefixLift 514061
  have htrace : WordTrace (prefixWord ++ tailWord_514061) baseStart_514061 baseEnd_514061 := by
    simpa [prefixWord, tailWord_514061, baseEnd_514061] using wordTrace_append hprefix tailTrace_514061
  have hstable : (prefixWord ++ tailWord_514061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514061).length < 2 ^ (prefixWord ++ tailWord_514061).sum := by decide
  have hdescent : baseEnd_514061 < baseStart_514061 := by decide
  rcases family_descends (prefixWord ++ tailWord_514061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514069 : List Nat := [1, 3, 2, 1, 12]
def baseStart_514069 : Nat := 118140960795 + 514069 * 2 ^ 59
def prefixEnd_514069 : Nat := 4983230072969 + 3 ^ 40 * 514069 * 2
def baseEnd_514069 : Nat := 5793459238985008205725

theorem tailTrace_514069 : CollatzResearch.WordTrace tailWord_514069 prefixEnd_514069 5793459238985008205725 := by
  unfold tailWord_514069
  simp only [CollatzResearch.WordTrace]
  refine ⟨18749636774623283840513261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12499757849748855893675507 18749636774623283840513261)
  ·
    refine ⟨7031113790483731440192473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18749636774623283840513261 7031113790483731440192473)
    ·
      refine ⟨5273335342862798580144355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7031113790483731440192473 5273335342862798580144355)
      ·
        refine ⟨7910003014294197870216533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5273335342862798580144355 7910003014294197870216533)
        ·
          refine ⟨5793459238985008205725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7910003014294197870216533 5793459238985008205725)
          ·
            rfl

theorem cell19_514069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 12].length) (baseStart_514069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514069 prefixEnd_514069 := by exact prefixLift 514069
  have htrace : WordTrace (prefixWord ++ tailWord_514069) baseStart_514069 baseEnd_514069 := by
    simpa [prefixWord, tailWord_514069, baseEnd_514069] using wordTrace_append hprefix tailTrace_514069
  have hstable : (prefixWord ++ tailWord_514069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514069).length < 2 ^ (prefixWord ++ tailWord_514069).sum := by decide
  have hdescent : baseEnd_514069 < baseStart_514069 := by decide
  rcases family_descends (prefixWord ++ tailWord_514069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514145 : List Nat := [1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_514145 : Nat := 118140960795 + 514145 * 2 ^ 59
def prefixEnd_514145 : Nat := 4983230072969 + 3 ^ 40 * 514145 * 2
def baseEnd_514145 : Nat := 156446525099849563865479

theorem tailTrace_514145 : CollatzResearch.WordTrace tailWord_514145 prefixEnd_514145 156446525099849563865479 := by
  unfold tailWord_514145
  simp only [CollatzResearch.WordTrace]
  refine ⟨18752408722347948820279889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12501605814898632546853259 18752408722347948820279889)
  ·
    refine ⟨14064306541760961615209917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18752408722347948820279889 14064306541760961615209917)
    ·
      refine ⟨5274114953160360605703719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14064306541760961615209917 5274114953160360605703719)
      ·
        refine ⟨7911172429740540908555579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5274114953160360605703719 7911172429740540908555579)
        ·
          refine ⟨11866758644610811362833369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7911172429740540908555579 11866758644610811362833369)
          ·
            refine ⟨8900068983458108522125027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11866758644610811362833369 8900068983458108522125027)
            ·
              refine ⟨13350103475187162783187541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900068983458108522125027 13350103475187162783187541)
              ·
                refine ⟨156446525099849563865479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13350103475187162783187541 156446525099849563865479)
                ·
                  rfl

theorem cell19_514145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_514145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514145 prefixEnd_514145 := by exact prefixLift 514145
  have htrace : WordTrace (prefixWord ++ tailWord_514145) baseStart_514145 baseEnd_514145 := by
    simpa [prefixWord, tailWord_514145, baseEnd_514145] using wordTrace_append hprefix tailTrace_514145
  have hstable : (prefixWord ++ tailWord_514145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514145).length < 2 ^ (prefixWord ++ tailWord_514145).sum := by decide
  have hdescent : baseEnd_514145 < baseStart_514145 := by decide
  rcases family_descends (prefixWord ++ tailWord_514145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514160 : List Nat := [2, 1, 1, 1, 5, 4, 2, 3]
def baseStart_514160 : Nat := 118140960795 + 514160 * 2 ^ 59
def prefixEnd_514160 : Nat := 4983230072969 + 3 ^ 40 * 514160 * 2
def baseEnd_514160 : Nat := 156451089372333973532105

theorem tailTrace_514160 : CollatzResearch.WordTrace tailWord_514160 prefixEnd_514160 156451089372333973532105 := by
  unfold tailWord_514160
  simp only [CollatzResearch.WordTrace]
  refine ⟨9376477908646803191037967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12501970544862404254717289 9376477908646803191037967)
  ·
    refine ⟨14064716862970204786556951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9376477908646803191037967 14064716862970204786556951)
    ·
      refine ⟨21097075294455307179835427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14064716862970204786556951 21097075294455307179835427)
      ·
        refine ⟨31645612941682960769753141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21097075294455307179835427 31645612941682960769753141)
        ·
          refine ⟨2966776213282777572164357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31645612941682960769753141 2966776213282777572164357)
          ·
            refine ⟨556270539990520794780817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2966776213282777572164357 556270539990520794780817)
            ·
              refine ⟨417202904992890596085613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556270539990520794780817 417202904992890596085613)
              ·
                refine ⟨156451089372333973532105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417202904992890596085613 156451089372333973532105)
                ·
                  rfl

theorem cell19_514160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_514160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514160 prefixEnd_514160 := by exact prefixLift 514160
  have htrace : WordTrace (prefixWord ++ tailWord_514160) baseStart_514160 baseEnd_514160 := by
    simpa [prefixWord, tailWord_514160, baseEnd_514160] using wordTrace_append hprefix tailTrace_514160
  have hstable : (prefixWord ++ tailWord_514160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514160).length < 2 ^ (prefixWord ++ tailWord_514160).sum := by decide
  have hdescent : baseEnd_514160 < baseStart_514160 := by decide
  rcases family_descends (prefixWord ++ tailWord_514160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514162 : List Nat := [3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_514162 : Nat := 118140960795 + 514162 * 2 ^ 59
def prefixEnd_514162 : Nat := 4983230072969 + 3 ^ 40 * 514162 * 2
def baseEnd_514162 : Nat := 156451697941998561487655

theorem tailTrace_514162 : CollatzResearch.WordTrace tailWord_514162 prefixEnd_514162 156451697941998561487655 := by
  unfold tailWord_514162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4688257190821590180912185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12502019175524240482432493 4688257190821590180912185)
  ·
    refine ⟨3516192893116192635684139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4688257190821590180912185 3516192893116192635684139)
    ·
      refine ⟨5274289339674288953526209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3516192893116192635684139 5274289339674288953526209)
      ·
        refine ⟨3955717004755716715144657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5274289339674288953526209 3955717004755716715144657)
        ·
          refine ⟨2966787753566787536358493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3955717004755716715144657 2966787753566787536358493)
          ·
            refine ⟨1112545407587545326134435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2966787753566787536358493 1112545407587545326134435)
            ·
              refine ⟨1668818111381317989201653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1112545407587545326134435 1668818111381317989201653)
              ·
                refine ⟨156451697941998561487655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1668818111381317989201653 156451697941998561487655)
                ·
                  rfl

theorem cell19_514162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_514162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514162 prefixEnd_514162 := by exact prefixLift 514162
  have htrace : WordTrace (prefixWord ++ tailWord_514162) baseStart_514162 baseEnd_514162 := by
    simpa [prefixWord, tailWord_514162, baseEnd_514162] using wordTrace_append hprefix tailTrace_514162
  have hstable : (prefixWord ++ tailWord_514162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514162).length < 2 ^ (prefixWord ++ tailWord_514162).sum := by decide
  have hdescent : baseEnd_514162 < baseStart_514162 := by decide
  rcases family_descends (prefixWord ++ tailWord_514162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514181 : List Nat := [1, 3, 1, 1, 5, 3, 5]
def baseStart_514181 : Nat := 118140960795 + 514181 * 2 ^ 59
def prefixEnd_514181 : Nat := 4983230072969 + 3 ^ 40 * 514181 * 2
def baseEnd_514181 : Nat := 52152493117937382355127

theorem tailTrace_514181 : CollatzResearch.WordTrace tailWord_514181 prefixEnd_514181 52152493117937382355127 := by
  unfold tailWord_514181
  simp only [CollatzResearch.WordTrace]
  refine ⟨18753721750217526968590397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12502481166811684645726931 18753721750217526968590397)
  ·
    refine ⟨7032645656331572613221399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18753721750217526968590397 7032645656331572613221399)
    ·
      refine ⟨10548968484497358919832099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032645656331572613221399 10548968484497358919832099)
      ·
        refine ⟨15823452726746038379748149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10548968484497358919832099 15823452726746038379748149)
        ·
          refine ⟨1483448693132441098101389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15823452726746038379748149 1483448693132441098101389)
          ·
            refine ⟨556293259924665411788021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1483448693132441098101389 556293259924665411788021)
            ·
              refine ⟨52152493117937382355127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 556293259924665411788021 52152493117937382355127)
              ·
                rfl

theorem cell19_514181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_514181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514181 prefixEnd_514181 := by exact prefixLift 514181
  have htrace : WordTrace (prefixWord ++ tailWord_514181) baseStart_514181 baseEnd_514181 := by
    simpa [prefixWord, tailWord_514181, baseEnd_514181] using wordTrace_append hprefix tailTrace_514181
  have hstable : (prefixWord ++ tailWord_514181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514181).length < 2 ^ (prefixWord ++ tailWord_514181).sum := by decide
  have hdescent : baseEnd_514181 < baseStart_514181 := by decide
  rcases family_descends (prefixWord ++ tailWord_514181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514183 : List Nat := [1, 1, 4, 2, 1, 1, 9]
def baseStart_514183 : Nat := 118140960795 + 514183 * 2 ^ 59
def prefixEnd_514183 : Nat := 4983230072969 + 3 ^ 40 * 514183 * 2
def baseEnd_514183 : Nat := 52152695974492245006977

theorem tailTrace_514183 : CollatzResearch.WordTrace tailWord_514183 prefixEnd_514183 52152695974492245006977 := by
  unfold tailWord_514183
  simp only [CollatzResearch.WordTrace]
  refine ⟨18753794696210281310163203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12502529797473520873442135 18753794696210281310163203)
  ·
    refine ⟨28130692044315421965244805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18753794696210281310163203 28130692044315421965244805)
    ·
      refine ⟨5274504758309141618483401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28130692044315421965244805 5274504758309141618483401)
      ·
        refine ⟨3955878568731856213862551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5274504758309141618483401 3955878568731856213862551)
        ·
          refine ⟨5933817853097784320793827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955878568731856213862551 5933817853097784320793827)
          ·
            refine ⟨8900726779646676481190741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933817853097784320793827 8900726779646676481190741)
            ·
              refine ⟨52152695974492245006977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8900726779646676481190741 52152695974492245006977)
              ·
                rfl

theorem cell19_514183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_514183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514183 prefixEnd_514183 := by exact prefixLift 514183
  have htrace : WordTrace (prefixWord ++ tailWord_514183) baseStart_514183 baseEnd_514183 := by
    simpa [prefixWord, tailWord_514183, baseEnd_514183] using wordTrace_append hprefix tailTrace_514183
  have hstable : (prefixWord ++ tailWord_514183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514183).length < 2 ^ (prefixWord ++ tailWord_514183).sum := by decide
  have hdescent : baseEnd_514183 < baseStart_514183 := by decide
  rcases family_descends (prefixWord ++ tailWord_514183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514196 : List Nat := [2, 4, 2, 3, 1, 1, 2, 4]
def baseStart_514196 : Nat := 118140960795 + 514196 * 2 ^ 59
def prefixEnd_514196 : Nat := 4983230072969 + 3 ^ 40 * 514196 * 2
def baseEnd_514196 : Nat := 156462043626296556732007

theorem tailTrace_514196 : CollatzResearch.WordTrace tailWord_514196 prefixEnd_514196 156462043626296556732007 := by
  unfold tailWord_514196
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377134422581592265193221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12502845896775456353590961 9377134422581592265193221)
  ·
    refine ⟨1758212704234048549723729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9377134422581592265193221 1758212704234048549723729)
    ·
      refine ⟨1318659528175536412292797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1758212704234048549723729 1318659528175536412292797)
      ·
        refine ⟨494497323065826154609799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1318659528175536412292797 494497323065826154609799)
        ·
          refine ⟨741745984598739231914699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494497323065826154609799 741745984598739231914699)
          ·
            refine ⟨1112618976898108847872049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741745984598739231914699 1112618976898108847872049)
            ·
              refine ⟨834464232673581635904037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112618976898108847872049 834464232673581635904037)
              ·
                refine ⟨156462043626296556732007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 834464232673581635904037 156462043626296556732007)
                ·
                  rfl

theorem cell19_514196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_514196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514196 prefixEnd_514196 := by exact prefixLift 514196
  have htrace : WordTrace (prefixWord ++ tailWord_514196) baseStart_514196 baseEnd_514196 := by
    simpa [prefixWord, tailWord_514196, baseEnd_514196] using wordTrace_append hprefix tailTrace_514196
  have hstable : (prefixWord ++ tailWord_514196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514196).length < 2 ^ (prefixWord ++ tailWord_514196).sum := by decide
  have hdescent : baseEnd_514196 < baseStart_514196 := by decide
  rcases family_descends (prefixWord ++ tailWord_514196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514238 : List Nat := [4, 2, 1, 1, 4, 7]
def baseStart_514238 : Nat := 118140960795 + 514238 * 2 ^ 59
def prefixEnd_514238 : Nat := 4983230072969 + 3 ^ 40 * 514238 * 2
def baseEnd_514238 : Nat := 17386091509916989310951

theorem tailTrace_514238 : CollatzResearch.WordTrace tailWord_514238 prefixEnd_514238 17386091509916989310951 := by
  unfold tailWord_514238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2344475088876378212926921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12503867140674017135610245 2344475088876378212926921)
  ·
    refine ⟨1758356316657283659695191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2344475088876378212926921 1758356316657283659695191)
    ·
      refine ⟨2637534474985925489542787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1758356316657283659695191 2637534474985925489542787)
      ·
        refine ⟨3956301712478888234314181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2637534474985925489542787 3956301712478888234314181)
        ·
          refine ⟨741806571089791543933909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3956301712478888234314181 741806571089791543933909)
          ·
            refine ⟨17386091509916989310951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 741806571089791543933909 17386091509916989310951)
            ·
              rfl

theorem cell19_514238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 7].length) (baseStart_514238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514238 prefixEnd_514238 := by exact prefixLift 514238
  have htrace : WordTrace (prefixWord ++ tailWord_514238) baseStart_514238 baseEnd_514238 := by
    simpa [prefixWord, tailWord_514238, baseEnd_514238] using wordTrace_append hprefix tailTrace_514238
  have hstable : (prefixWord ++ tailWord_514238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514238).length < 2 ^ (prefixWord ++ tailWord_514238).sum := by decide
  have hdescent : baseEnd_514238 < baseStart_514238 := by decide
  rcases family_descends (prefixWord ++ tailWord_514238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514240 : List Nat := [2, 1, 1, 2, 5, 8]
def baseStart_514240 : Nat := 118140960795 + 514240 * 2 ^ 59
def prefixEnd_514240 : Nat := 4983230072969 + 3 ^ 40 * 514240 * 2
def baseEnd_514240 : Nat := 17386159128768610194901

theorem tailTrace_514240 : CollatzResearch.WordTrace tailWord_514240 prefixEnd_514240 17386159128768610194901 := by
  unfold tailWord_514240
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377936828501890022494087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12503915771335853363325449 9377936828501890022494087)
  ·
    refine ⟨14066905242752835033741131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9377936828501890022494087 14066905242752835033741131)
    ·
      refine ⟨21100357864129252550611697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14066905242752835033741131 21100357864129252550611697)
      ·
        refine ⟨15825268398096939412958773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21100357864129252550611697 15825268398096939412958773)
        ·
          refine ⟨1483618912321588069964885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15825268398096939412958773 1483618912321588069964885)
          ·
            refine ⟨17386159128768610194901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1483618912321588069964885 17386159128768610194901)
            ·
              rfl

theorem cell19_514240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 8].length) (baseStart_514240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514240 prefixEnd_514240 := by exact prefixLift 514240
  have htrace : WordTrace (prefixWord ++ tailWord_514240) baseStart_514240 baseEnd_514240 := by
    simpa [prefixWord, tailWord_514240, baseEnd_514240] using wordTrace_append hprefix tailTrace_514240
  have hstable : (prefixWord ++ tailWord_514240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514240).length < 2 ^ (prefixWord ++ tailWord_514240).sum := by decide
  have hdescent : baseEnd_514240 < baseStart_514240 := by decide
  rcases family_descends (prefixWord ++ tailWord_514240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514316 : List Nat := [2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_514316 : Nat := 118140960795 + 514316 * 2 ^ 59
def prefixEnd_514316 : Nat := 4983230072969 + 3 ^ 40 * 514316 * 2
def baseEnd_514316 : Nat := 156498557806171834065013

theorem tailTrace_514316 : CollatzResearch.WordTrace tailWord_514316 prefixEnd_514316 156498557806171834065013 := by
  unfold tailWord_514316
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379322802364222512377401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12505763736485630016503201 9379322802364222512377401)
  ·
    refine ⟨7034492101773166884283051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9379322802364222512377401 7034492101773166884283051)
    ·
      refine ⟨10551738152659750326424577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7034492101773166884283051 10551738152659750326424577)
      ·
        refine ⟨7913803614494812744818433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10551738152659750326424577 7913803614494812744818433)
        ·
          refine ⟨5935352710871109558613825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7913803614494812744818433 5935352710871109558613825)
          ·
            refine ⟨4451514533153332168960369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5935352710871109558613825 4451514533153332168960369)
            ·
              refine ⟨3338635899864999126720277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4451514533153332168960369 3338635899864999126720277)
              ·
                refine ⟨156498557806171834065013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3338635899864999126720277 156498557806171834065013)
                ·
                  rfl

theorem cell19_514316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_514316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514316 prefixEnd_514316 := by exact prefixLift 514316
  have htrace : WordTrace (prefixWord ++ tailWord_514316) baseStart_514316 baseEnd_514316 := by
    simpa [prefixWord, tailWord_514316, baseEnd_514316] using wordTrace_append hprefix tailTrace_514316
  have hstable : (prefixWord ++ tailWord_514316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514316).length < 2 ^ (prefixWord ++ tailWord_514316).sum := by decide
  have hdescent : baseEnd_514316 < baseStart_514316 := by decide
  rcases family_descends (prefixWord ++ tailWord_514316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514369 : List Nat := [1, 2, 5, 2, 2, 1, 2, 4]
def baseStart_514369 : Nat := 118140960795 + 514369 * 2 ^ 59
def prefixEnd_514369 : Nat := 4983230072969 + 3 ^ 40 * 514369 * 2
def baseEnd_514369 : Nat := 156514684902283414887091

theorem tailTrace_514369 : CollatzResearch.WordTrace tailWord_514369 prefixEnd_514369 156514684902283414887091 := by
  unfold tailWord_514369
  simp only [CollatzResearch.WordTrace]
  refine ⟨18760578673536435076434161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12507052449024290050956107 18760578673536435076434161)
  ·
    refine ⟨14070434005152326307325621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18760578673536435076434161 14070434005152326307325621)
    ·
      refine ⟨1319103187983030591311777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14070434005152326307325621 1319103187983030591311777)
      ·
        refine ⟨989327390987272943483833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1319103187983030591311777 989327390987272943483833)
        ·
          refine ⟨741995543240454707612875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989327390987272943483833 741995543240454707612875)
          ·
            refine ⟨1112993314860682061419313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741995543240454707612875 1112993314860682061419313)
            ·
              refine ⟨834744986145511546064485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112993314860682061419313 834744986145511546064485)
              ·
                refine ⟨156514684902283414887091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 834744986145511546064485 156514684902283414887091)
                ·
                  rfl

theorem cell19_514369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_514369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514369 prefixEnd_514369 := by exact prefixLift 514369
  have htrace : WordTrace (prefixWord ++ tailWord_514369) baseStart_514369 baseEnd_514369 := by
    simpa [prefixWord, tailWord_514369, baseEnd_514369] using wordTrace_append hprefix tailTrace_514369
  have hstable : (prefixWord ++ tailWord_514369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514369).length < 2 ^ (prefixWord ++ tailWord_514369).sum := by decide
  have hdescent : baseEnd_514369 < baseStart_514369 := by decide
  rcases family_descends (prefixWord ++ tailWord_514369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514422 : List Nat := [5, 1, 1, 4, 2, 1, 1, 4]
def baseStart_514422 : Nat := 118140960795 + 514422 * 2 ^ 59
def prefixEnd_514422 : Nat := 4983230072969 + 3 ^ 40 * 514422 * 2
def baseEnd_514422 : Nat := 156530811998394995709169

theorem tailTrace_514422 : CollatzResearch.WordTrace tailWord_514422 prefixEnd_514422 156530811998394995709169 := by
  unfold tailWord_514422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172656983896526570507095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12508341161562950085409013 1172656983896526570507095)
  ·
    refine ⟨1758985475844789855760643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1172656983896526570507095 1758985475844789855760643)
    ·
      refine ⟨2638478213767184783640965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1758985475844789855760643 2638478213767184783640965)
      ·
        refine ⟨494714665081347146932681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2638478213767184783640965 494714665081347146932681)
        ·
          refine ⟨371035998811010360199511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494714665081347146932681 371035998811010360199511)
          ·
            refine ⟨556553998216515540299267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371035998811010360199511 556553998216515540299267)
            ·
              refine ⟨834830997324773310448901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556553998216515540299267 834830997324773310448901)
              ·
                refine ⟨156530811998394995709169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 834830997324773310448901 156530811998394995709169)
                ·
                  rfl

theorem cell19_514422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_514422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514422 prefixEnd_514422 := by exact prefixLift 514422
  have htrace : WordTrace (prefixWord ++ tailWord_514422) baseStart_514422 baseEnd_514422 := by
    simpa [prefixWord, tailWord_514422, baseEnd_514422] using wordTrace_append hprefix tailTrace_514422
  have hstable : (prefixWord ++ tailWord_514422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514422).length < 2 ^ (prefixWord ++ tailWord_514422).sum := by decide
  have hdescent : baseEnd_514422 < baseStart_514422 := by decide
  rcases family_descends (prefixWord ++ tailWord_514422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514500 : List Nat := [2, 3, 3, 2, 2, 2, 2, 3]
def baseStart_514500 : Nat := 118140960795 + 514500 * 2 ^ 59
def prefixEnd_514500 : Nat := 4983230072969 + 3 ^ 40 * 514500 * 2
def baseEnd_514500 : Nat := 156554546215313925975623

theorem tailTrace_514500 : CollatzResearch.WordTrace tailWord_514500 prefixEnd_514500 156554546215313925975623 := by
  unfold tailWord_514500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9382678318030922224726477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12510237757374562966301969 9382678318030922224726477)
  ·
    refine ⟨3518504369261595834272429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9382678318030922224726477 3518504369261595834272429)
    ·
      refine ⟨1319439138473098437852161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3518504369261595834272429 1319439138473098437852161)
      ·
        refine ⟨989579353854823828389121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1319439138473098437852161 989579353854823828389121)
        ·
          refine ⟨742184515391117871291841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989579353854823828389121 742184515391117871291841)
          ·
            refine ⟨556638386543338403468881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742184515391117871291841 556638386543338403468881)
            ·
              refine ⟨417478789907503802601661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556638386543338403468881 417478789907503802601661)
              ·
                refine ⟨156554546215313925975623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417478789907503802601661 156554546215313925975623)
                ·
                  rfl

theorem cell19_514500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_514500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514500 prefixEnd_514500 := by exact prefixLift 514500
  have htrace : WordTrace (prefixWord ++ tailWord_514500) baseStart_514500 baseEnd_514500 := by
    simpa [prefixWord, tailWord_514500, baseEnd_514500] using wordTrace_append hprefix tailTrace_514500
  have hstable : (prefixWord ++ tailWord_514500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514500).length < 2 ^ (prefixWord ++ tailWord_514500).sum := by decide
  have hdescent : baseEnd_514500 < baseStart_514500 := by decide
  rcases family_descends (prefixWord ++ tailWord_514500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514504 : List Nat := [2, 1, 3, 1, 3, 2, 4, 3]
def baseStart_514504 : Nat := 118140960795 + 514504 * 2 ^ 59
def prefixEnd_514504 : Nat := 4983230072969 + 3 ^ 40 * 514504 * 2
def baseEnd_514504 : Nat := 156555763354643101886723

theorem tailTrace_514504 : CollatzResearch.WordTrace tailWord_514504 prefixEnd_514504 156555763354643101886723 := by
  unfold tailWord_514504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9382751264023676566299283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12510335018698235421732377 9382751264023676566299283)
  ·
    refine ⟨14074126896035514849448925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9382751264023676566299283 14074126896035514849448925)
    ·
      refine ⟨5277797586013318068543347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14074126896035514849448925 5277797586013318068543347)
      ·
        refine ⟨7916696379019977102815021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5277797586013318068543347 7916696379019977102815021)
        ·
          refine ⟨2968761142132491413555633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7916696379019977102815021 2968761142132491413555633)
          ·
            refine ⟨2226570856599368560166725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2968761142132491413555633 2226570856599368560166725)
            ·
              refine ⟨417482035612381605031261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2226570856599368560166725 417482035612381605031261)
              ·
                refine ⟨156555763354643101886723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417482035612381605031261 156555763354643101886723)
                ·
                  rfl

theorem cell19_514504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_514504 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514504 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514504 prefixEnd_514504 := by exact prefixLift 514504
  have htrace : WordTrace (prefixWord ++ tailWord_514504) baseStart_514504 baseEnd_514504 := by
    simpa [prefixWord, tailWord_514504, baseEnd_514504] using wordTrace_append hprefix tailTrace_514504
  have hstable : (prefixWord ++ tailWord_514504).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514504).length < 2 ^ (prefixWord ++ tailWord_514504).sum := by decide
  have hdescent : baseEnd_514504 < baseStart_514504 := by decide
  rcases family_descends (prefixWord ++ tailWord_514504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514506 : List Nat := [3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_514506 : Nat := 118140960795 + 514506 * 2 ^ 59
def prefixEnd_514506 : Nat := 4983230072969 + 3 ^ 40 * 514506 * 2
def baseEnd_514506 : Nat := 156556371924307689842273

theorem tailTrace_514506 : CollatzResearch.WordTrace tailWord_514506 prefixEnd_514506 156556371924307689842273 := by
  unfold tailWord_514506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691393868510026868542843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12510383649360071649447581 4691393868510026868542843)
  ·
    refine ⟨7037090802765040302814265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4691393868510026868542843 7037090802765040302814265)
    ·
      refine ⟨5277818102073780227110699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7037090802765040302814265 5277818102073780227110699)
      ·
        refine ⟨7916727153110670340666049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5277818102073780227110699 7916727153110670340666049)
        ·
          refine ⟨5937545364833002755499537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7916727153110670340666049 5937545364833002755499537)
          ·
            refine ⟨4453159023624752066624653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5937545364833002755499537 4453159023624752066624653)
            ·
              refine ⟨1669934633859282024984245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4453159023624752066624653 1669934633859282024984245)
              ·
                refine ⟨156556371924307689842273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1669934633859282024984245 156556371924307689842273)
                ·
                  rfl

theorem cell19_514506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_514506 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514506 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514506 prefixEnd_514506 := by exact prefixLift 514506
  have htrace : WordTrace (prefixWord ++ tailWord_514506) baseStart_514506 baseEnd_514506 := by
    simpa [prefixWord, tailWord_514506, baseEnd_514506] using wordTrace_append hprefix tailTrace_514506
  have hstable : (prefixWord ++ tailWord_514506).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514506).length < 2 ^ (prefixWord ++ tailWord_514506).sum := by decide
  have hdescent : baseEnd_514506 < baseStart_514506 := by decide
  rcases family_descends (prefixWord ++ tailWord_514506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514542 : List Nat := [4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_514542 : Nat := 118140960795 + 514542 * 2 ^ 59
def prefixEnd_514542 : Nat := 4983230072969 + 3 ^ 40 * 514542 * 2
def baseEnd_514542 : Nat := 156567326178270273042175

theorem tailTrace_514542 : CollatzResearch.WordTrace tailWord_514542 prefixEnd_514542 156567326178270273042175 := by
  unfold tailWord_514542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2345861062738710702810235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12511259001273123748321253 2345861062738710702810235)
  ·
    refine ⟨3518791594108066054215353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2345861062738710702810235 3518791594108066054215353)
    ·
      refine ⟨2639093695581049540661515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3518791594108066054215353 2639093695581049540661515)
      ·
        refine ⟨3958640543371574310992273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2639093695581049540661515 3958640543371574310992273)
        ·
          refine ⟨2968980407528680733244205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3958640543371574310992273 2968980407528680733244205)
          ·
            refine ⟨1113367652823255274966577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2968980407528680733244205 1113367652823255274966577)
            ·
              refine ⟨835025739617441456224933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113367652823255274966577 835025739617441456224933)
              ·
                refine ⟨156567326178270273042175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 835025739617441456224933 156567326178270273042175)
                ·
                  rfl

theorem cell19_514542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_514542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514542 prefixEnd_514542 := by exact prefixLift 514542
  have htrace : WordTrace (prefixWord ++ tailWord_514542) baseStart_514542 baseEnd_514542 := by
    simpa [prefixWord, tailWord_514542, baseEnd_514542] using wordTrace_append hprefix tailTrace_514542
  have hstable : (prefixWord ++ tailWord_514542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514542).length < 2 ^ (prefixWord ++ tailWord_514542).sum := by decide
  have hdescent : baseEnd_514542 < baseStart_514542 := by decide
  rcases family_descends (prefixWord ++ tailWord_514542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514544 : List Nat := [2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_514544 : Nat := 118140960795 + 514544 * 2 ^ 59
def prefixEnd_514544 : Nat := 4983230072969 + 3 ^ 40 * 514544 * 2
def baseEnd_514544 : Nat := 156567934747934860997725

theorem tailTrace_514544 : CollatzResearch.WordTrace tailWord_514544 prefixEnd_514544 156567934747934860997725 := by
  unfold tailWord_514544
  simp only [CollatzResearch.WordTrace]
  refine ⟨9383480723951219982027343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12511307631934959976036457 9383480723951219982027343)
  ·
    refine ⟨14075221085926829973041015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9383480723951219982027343 14075221085926829973041015)
    ·
      refine ⟨21112831628890244959561523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14075221085926829973041015 21112831628890244959561523)
      ·
        refine ⟨31669247443335367439342285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21112831628890244959561523 31669247443335367439342285)
        ·
          refine ⟨11875967791250762789753357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31669247443335367439342285 11875967791250762789753357)
          ·
            refine ⟨4453487921719036046157509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11875967791250762789753357 4453487921719036046157509)
            ·
              refine ⟨835028985322319258654533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4453487921719036046157509 835028985322319258654533)
              ·
                refine ⟨156567934747934860997725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 835028985322319258654533 156567934747934860997725)
                ·
                  rfl

theorem cell19_514544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_514544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514544 prefixEnd_514544 := by exact prefixLift 514544
  have htrace : WordTrace (prefixWord ++ tailWord_514544) baseStart_514544 baseEnd_514544 := by
    simpa [prefixWord, tailWord_514544, baseEnd_514544] using wordTrace_append hprefix tailTrace_514544
  have hstable : (prefixWord ++ tailWord_514544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514544).length < 2 ^ (prefixWord ++ tailWord_514544).sum := by decide
  have hdescent : baseEnd_514544 < baseStart_514544 := by decide
  rcases family_descends (prefixWord ++ tailWord_514544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514580 : List Nat := [2, 4, 3, 1, 1, 8]
def baseStart_514580 : Nat := 118140960795 + 514580 * 2 ^ 59
def prefixEnd_514580 : Nat := 4983230072969 + 3 ^ 40 * 514580 * 2
def baseEnd_514580 : Nat := 17397654333544160466403

theorem tailTrace_514580 : CollatzResearch.WordTrace tailWord_514580 prefixEnd_514580 17397654333544160466403 := by
  unfold tailWord_514580
  simp only [CollatzResearch.WordTrace]
  refine ⟨9384137237886009056182597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12512182983848012074910129 9384137237886009056182597)
  ·
    refine ⟨1759525732103626698034237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9384137237886009056182597 1759525732103626698034237)
    ·
      refine ⟨659822149538860011762839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1759525732103626698034237 659822149538860011762839)
      ·
        refine ⟨989733224308290017644259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659822149538860011762839 989733224308290017644259)
        ·
          refine ⟨1484599836462435026466389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989733224308290017644259 1484599836462435026466389)
          ·
            refine ⟨17397654333544160466403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1484599836462435026466389 17397654333544160466403)
            ·
              rfl

theorem cell19_514580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 8].length) (baseStart_514580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514580 prefixEnd_514580 := by exact prefixLift 514580
  have htrace : WordTrace (prefixWord ++ tailWord_514580) baseStart_514580 baseEnd_514580 := by
    simpa [prefixWord, tailWord_514580, baseEnd_514580] using wordTrace_append hprefix tailTrace_514580
  have hstable : (prefixWord ++ tailWord_514580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514580).length < 2 ^ (prefixWord ++ tailWord_514580).sum := by decide
  have hdescent : baseEnd_514580 < baseStart_514580 := by decide
  rcases family_descends (prefixWord ++ tailWord_514580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514618 : List Nat := [3, 1, 1, 1, 3, 4, 3, 3]
def baseStart_514618 : Nat := 118140960795 + 514618 * 2 ^ 59
def prefixEnd_514618 : Nat := 4983230072969 + 3 ^ 40 * 514618 * 2
def baseEnd_514618 : Nat := 156590451825524615353079

theorem tailTrace_514618 : CollatzResearch.WordTrace tailWord_514618 prefixEnd_514618 156590451825524615353079 := by
  unfold tailWord_514618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4692415112408587650562127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12513106966422900401499005 4692415112408587650562127)
  ·
    refine ⟨7038622668612881475843191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4692415112408587650562127 7038622668612881475843191)
    ·
      refine ⟨10557934002919322213764787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7038622668612881475843191 10557934002919322213764787)
      ·
        refine ⟨15836901004378983320647181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10557934002919322213764787 15836901004378983320647181)
        ·
          refine ⟨5938837876642118745242693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15836901004378983320647181 5938837876642118745242693)
          ·
            refine ⟨1113532101870397264733005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5938837876642118745242693 1113532101870397264733005)
            ·
              refine ⟨417574538201398974274877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1113532101870397264733005 417574538201398974274877)
              ·
                refine ⟨156590451825524615353079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417574538201398974274877 156590451825524615353079)
                ·
                  rfl

theorem cell19_514618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_514618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514618 prefixEnd_514618 := by exact prefixLift 514618
  have htrace : WordTrace (prefixWord ++ tailWord_514618) baseStart_514618 baseEnd_514618 := by
    simpa [prefixWord, tailWord_514618, baseEnd_514618] using wordTrace_append hprefix tailTrace_514618
  have hstable : (prefixWord ++ tailWord_514618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514618).length < 2 ^ (prefixWord ++ tailWord_514618).sum := by decide
  have hdescent : baseEnd_514618 < baseStart_514618 := by decide
  rcases family_descends (prefixWord ++ tailWord_514618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514637 : List Nat := [1, 6, 1, 1, 2, 2, 6]
def baseStart_514637 : Nat := 118140960795 + 514637 * 2 ^ 59
def prefixEnd_514637 : Nat := 4983230072969 + 3 ^ 40 * 514637 * 2
def baseEnd_514637 : Nat := 52198744412446066976935

theorem tailTrace_514637 : CollatzResearch.WordTrace tailWord_514637 prefixEnd_514637 52198744412446066976935 := by
  unfold tailWord_514637
  simp only [CollatzResearch.WordTrace]
  refine ⟨18770353436565516847190165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12513568957710344564793443 18770353436565516847190165)
  ·
    refine ⟨879860317339008602212039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18770353436565516847190165 879860317339008602212039)
    ·
      refine ⟨1319790476008512903318059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 879860317339008602212039 1319790476008512903318059)
      ·
        refine ⟨1979685714012769354977089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319790476008512903318059 1979685714012769354977089)
        ·
          refine ⟨1484764285509577016232817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1979685714012769354977089 1484764285509577016232817)
          ·
            refine ⟨1113573214132182762174613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484764285509577016232817 1113573214132182762174613)
            ·
              refine ⟨52198744412446066976935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1113573214132182762174613 52198744412446066976935)
              ·
                rfl

theorem cell19_514637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_514637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514637 prefixEnd_514637 := by exact prefixLift 514637
  have htrace : WordTrace (prefixWord ++ tailWord_514637) baseStart_514637 baseEnd_514637 := by
    simpa [prefixWord, tailWord_514637, baseEnd_514637] using wordTrace_append hprefix tailTrace_514637
  have hstable : (prefixWord ++ tailWord_514637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514637).length < 2 ^ (prefixWord ++ tailWord_514637).sum := by decide
  have hdescent : baseEnd_514637 < baseStart_514637 := by decide
  rcases family_descends (prefixWord ++ tailWord_514637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514789 : List Nat := [1, 3, 1, 4, 1, 3, 3, 3]
def baseStart_514789 : Nat := 118140960795 + 514789 * 2 ^ 59
def prefixEnd_514789 : Nat := 4983230072969 + 3 ^ 40 * 514789 * 2
def baseEnd_514789 : Nat := 156642484531846885552613

theorem tailTrace_514789 : CollatzResearch.WordTrace tailWord_514789 prefixEnd_514789 156642484531846885552613 := by
  unfold tailWord_514789
  simp only [CollatzResearch.WordTrace]
  refine ⟨18775897332014846806723421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12517264888009897871148947 18775897332014846806723421)
  ·
    refine ⟨7040961499505567552521283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18775897332014846806723421 7040961499505567552521283)
    ·
      refine ⟨10561442249258351328781925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7040961499505567552521283 10561442249258351328781925)
      ·
        refine ⟨1980270421735940874146611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10561442249258351328781925 1980270421735940874146611)
        ·
          refine ⟨2970405632603911311219917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980270421735940874146611 2970405632603911311219917)
          ·
            refine ⟨1113902112226466741707469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2970405632603911311219917 1113902112226466741707469)
            ·
              refine ⟨417713292084925028140301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1113902112226466741707469 417713292084925028140301)
              ·
                refine ⟨156642484531846885552613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417713292084925028140301 156642484531846885552613)
                ·
                  rfl

theorem cell19_514789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 3].length) (baseStart_514789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514789 prefixEnd_514789 := by exact prefixLift 514789
  have htrace : WordTrace (prefixWord ++ tailWord_514789) baseStart_514789 baseEnd_514789 := by
    simpa [prefixWord, tailWord_514789, baseEnd_514789] using wordTrace_append hprefix tailTrace_514789
  have hstable : (prefixWord ++ tailWord_514789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514789).length < 2 ^ (prefixWord ++ tailWord_514789).sum := by decide
  have hdescent : baseEnd_514789 < baseStart_514789 := by decide
  rcases family_descends (prefixWord ++ tailWord_514789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514793 : List Nat := [1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_514793 : Nat := 118140960795 + 514793 * 2 ^ 59
def prefixEnd_514793 : Nat := 4983230072969 + 3 ^ 40 * 514793 * 2
def baseEnd_514793 : Nat := 156643701671176061463713

theorem tailTrace_514793 : CollatzResearch.WordTrace tailWord_514793 prefixEnd_514793 156643701671176061463713 := by
  unfold tailWord_514793
  simp only [CollatzResearch.WordTrace]
  refine ⟨18776043224000355489869033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12517362149333570326579355 18776043224000355489869033)
  ·
    refine ⟨14082032418000266617401775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18776043224000355489869033 14082032418000266617401775)
    ·
      refine ⟨21123048627000399926102663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14082032418000266617401775 21123048627000399926102663)
      ·
        refine ⟨31684572940500599889153995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21123048627000399926102663 31684572940500599889153995)
        ·
          refine ⟨47526859410750899833730993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31684572940500599889153995 47526859410750899833730993)
          ·
            refine ⟨35645144558063174875298245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47526859410750899833730993 35645144558063174875298245)
            ·
              refine ⟨6683464604636845289118421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35645144558063174875298245 6683464604636845289118421)
              ·
                refine ⟨156643701671176061463713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6683464604636845289118421 156643701671176061463713)
                ·
                  rfl

theorem cell19_514793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_514793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514793 prefixEnd_514793 := by exact prefixLift 514793
  have htrace : WordTrace (prefixWord ++ tailWord_514793) baseStart_514793 baseEnd_514793 := by
    simpa [prefixWord, tailWord_514793, baseEnd_514793] using wordTrace_append hprefix tailTrace_514793
  have hstable : (prefixWord ++ tailWord_514793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514793).length < 2 ^ (prefixWord ++ tailWord_514793).sum := by decide
  have hdescent : baseEnd_514793 < baseStart_514793 := by decide
  rcases family_descends (prefixWord ++ tailWord_514793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514831 : List Nat := [1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_514831 : Nat := 118140960795 + 514831 * 2 ^ 59
def prefixEnd_514831 : Nat := 4983230072969 + 3 ^ 40 * 514831 * 2
def baseEnd_514831 : Nat := 156655264494803232619165

theorem tailTrace_514831 : CollatzResearch.WordTrace tailWord_514831 prefixEnd_514831 156655264494803232619165 := by
  unfold tailWord_514831
  simp only [CollatzResearch.WordTrace]
  refine ⟨18777429197862687979752347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12518286131908458653168231 18777429197862687979752347)
  ·
    refine ⟨28166143796794031969628521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18777429197862687979752347 28166143796794031969628521)
    ·
      refine ⟨21124607847595523977221391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28166143796794031969628521 21124607847595523977221391)
      ·
        refine ⟨31686911771393285965832087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21124607847595523977221391 31686911771393285965832087)
        ·
          refine ⟨47530367657089928948748131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31686911771393285965832087 47530367657089928948748131)
          ·
            refine ⟨71295551485634893423122197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47530367657089928948748131 71295551485634893423122197)
            ·
              refine ⟨3341978975889135629208853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71295551485634893423122197 3341978975889135629208853)
              ·
                refine ⟨156655264494803232619165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3341978975889135629208853 156655264494803232619165)
                ·
                  rfl

theorem cell19_514831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_514831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514831 prefixEnd_514831 := by exact prefixLift 514831
  have htrace : WordTrace (prefixWord ++ tailWord_514831) baseStart_514831 baseEnd_514831 := by
    simpa [prefixWord, tailWord_514831, baseEnd_514831] using wordTrace_append hprefix tailTrace_514831
  have hstable : (prefixWord ++ tailWord_514831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514831).length < 2 ^ (prefixWord ++ tailWord_514831).sum := by decide
  have hdescent : baseEnd_514831 < baseStart_514831 := by decide
  rcases family_descends (prefixWord ++ tailWord_514831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514848 : List Nat := [2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_514848 : Nat := 118140960795 + 514848 * 2 ^ 59
def prefixEnd_514848 : Nat := 4983230072969 + 3 ^ 40 * 514848 * 2
def baseEnd_514848 : Nat := 156660437336952230241341

theorem tailTrace_514848 : CollatzResearch.WordTrace tailWord_514848 prefixEnd_514848 156660437336952230241341 := by
  unfold tailWord_514848
  simp only [CollatzResearch.WordTrace]
  refine ⟨9389024619400549941560599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12518699492534066588747465 9389024619400549941560599)
  ·
    refine ⟨14083536929100824912340899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9389024619400549941560599 14083536929100824912340899)
    ·
      refine ⟨21125305393651237368511349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14083536929100824912340899 21125305393651237368511349)
      ·
        refine ⟨1980497380654803503297939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21125305393651237368511349 1980497380654803503297939)
        ·
          refine ⟨2970746070982205254946909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980497380654803503297939 2970746070982205254946909)
          ·
            refine ⟨1114029776618326970605091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2970746070982205254946909 1114029776618326970605091)
            ·
              refine ⟨1671044664927490455907637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114029776618326970605091 1671044664927490455907637)
              ·
                refine ⟨156660437336952230241341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1671044664927490455907637 156660437336952230241341)
                ·
                  rfl

theorem cell19_514848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_514848 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514848 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514848 prefixEnd_514848 := by exact prefixLift 514848
  have htrace : WordTrace (prefixWord ++ tailWord_514848) baseStart_514848 baseEnd_514848 := by
    simpa [prefixWord, tailWord_514848, baseEnd_514848] using wordTrace_append hprefix tailTrace_514848
  have hstable : (prefixWord ++ tailWord_514848).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514848).length < 2 ^ (prefixWord ++ tailWord_514848).sum := by decide
  have hdescent : baseEnd_514848 < baseStart_514848 := by decide
  rcases family_descends (prefixWord ++ tailWord_514848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514861 : List Nat := [1, 5, 3, 2, 2, 1, 5]
def baseStart_514861 : Nat := 118140960795 + 514861 * 2 ^ 59
def prefixEnd_514861 : Nat := 4983230072969 + 3 ^ 40 * 514861 * 2
def baseEnd_514861 : Nat := 52221464346590683984139

theorem tailTrace_514861 : CollatzResearch.WordTrace tailWord_514861 prefixEnd_514861 52221464346590683984139 := by
  unfold tailWord_514861
  simp only [CollatzResearch.WordTrace]
  refine ⟨18778523387754003103344437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12519015591836002068896291 18778523387754003103344437)
  ·
    refine ⟨1760486567601937790938541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18778523387754003103344437 1760486567601937790938541)
    ·
      refine ⟨660182462850726671601953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1760486567601937790938541 660182462850726671601953)
      ·
        refine ⟨495136847138045003701465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660182462850726671601953 495136847138045003701465)
        ·
          refine ⟨371352635353533752776099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495136847138045003701465 371352635353533752776099)
          ·
            refine ⟨557028953030300629164149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371352635353533752776099 557028953030300629164149)
            ·
              refine ⟨52221464346590683984139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 557028953030300629164149 52221464346590683984139)
              ·
                rfl

theorem cell19_514861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 5].length) (baseStart_514861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514861 prefixEnd_514861 := by exact prefixLift 514861
  have htrace : WordTrace (prefixWord ++ tailWord_514861) baseStart_514861 baseEnd_514861 := by
    simpa [prefixWord, tailWord_514861, baseEnd_514861] using wordTrace_append hprefix tailTrace_514861
  have hstable : (prefixWord ++ tailWord_514861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514861).length < 2 ^ (prefixWord ++ tailWord_514861).sum := by decide
  have hdescent : baseEnd_514861 < baseStart_514861 := by decide
  rcases family_descends (prefixWord ++ tailWord_514861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_514867 : List Nat := [1, 1, 1, 2, 6, 3, 5]
def baseStart_514867 : Nat := 118140960795 + 514867 * 2 ^ 59
def prefixEnd_514867 : Nat := 4983230072969 + 3 ^ 40 * 514867 * 2
def baseEnd_514867 : Nat := 52222072916255271939689

theorem tailTrace_514867 : CollatzResearch.WordTrace tailWord_514867 prefixEnd_514867 52222072916255271939689 := by
  unfold tailWord_514867
  simp only [CollatzResearch.WordTrace]
  refine ⟨18778742225732266128062855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12519161483821510752041903 18778742225732266128062855)
  ·
    refine ⟨28168113338598399192094283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18778742225732266128062855 28168113338598399192094283)
    ·
      refine ⟨42252170007897598788141425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28168113338598399192094283 42252170007897598788141425)
      ·
        refine ⟨31689127505923199091106069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42252170007897598788141425 31689127505923199091106069)
        ·
          refine ⟨1485427851840149957395597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31689127505923199091106069 1485427851840149957395597)
          ·
            refine ⟨557035444440056234023349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1485427851840149957395597 557035444440056234023349)
            ·
              refine ⟨52222072916255271939689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 557035444440056234023349 52222072916255271939689)
              ·
                rfl

theorem cell19_514867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_514867 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_514867 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_514867 prefixEnd_514867 := by exact prefixLift 514867
  have htrace : WordTrace (prefixWord ++ tailWord_514867) baseStart_514867 baseEnd_514867 := by
    simpa [prefixWord, tailWord_514867, baseEnd_514867] using wordTrace_append hprefix tailTrace_514867
  have hstable : (prefixWord ++ tailWord_514867).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_514867).length < 2 ^ (prefixWord ++ tailWord_514867).sum := by decide
  have hdescent : baseEnd_514867 < baseStart_514867 := by decide
  rcases family_descends (prefixWord ++ tailWord_514867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515002 : List Nat := [3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_515002 : Nat := 118140960795 + 515002 * 2 ^ 59
def prefixEnd_515002 : Nat := 4983230072969 + 3 ^ 40 * 515002 * 2
def baseEnd_515002 : Nat := 156707297201125502818699

theorem tailTrace_515002 : CollatzResearch.WordTrace tailWord_515002 prefixEnd_515002 156707297201125502818699 := by
  unfold tailWord_515002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4695916520060796046056815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12522444053495456122818173 4695916520060796046056815)
  ·
    refine ⟨7043874780091194069085223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4695916520060796046056815 7043874780091194069085223)
    ·
      refine ⟨10565812170136791103627835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7043874780091194069085223 10565812170136791103627835)
      ·
        refine ⟨15848718255205186655441753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10565812170136791103627835 15848718255205186655441753)
        ·
          refine ⟨11886538691403889991581315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15848718255205186655441753 11886538691403889991581315)
          ·
            refine ⟨17829808037105834987371973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11886538691403889991581315 17829808037105834987371973)
            ·
              refine ⟨3343089006957344060132245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17829808037105834987371973 3343089006957344060132245)
              ·
                refine ⟨156707297201125502818699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3343089006957344060132245 156707297201125502818699)
                ·
                  rfl

theorem cell19_515002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_515002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515002 prefixEnd_515002 := by exact prefixLift 515002
  have htrace : WordTrace (prefixWord ++ tailWord_515002) baseStart_515002 baseEnd_515002 := by
    simpa [prefixWord, tailWord_515002, baseEnd_515002] using wordTrace_append hprefix tailTrace_515002
  have hstable : (prefixWord ++ tailWord_515002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515002).length < 2 ^ (prefixWord ++ tailWord_515002).sum := by decide
  have hdescent : baseEnd_515002 < baseStart_515002 := by decide
  rcases family_descends (prefixWord ++ tailWord_515002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515019 : List Nat := [1, 1, 1, 1, 3, 5, 4, 3]
def baseStart_515019 : Nat := 118140960795 + 515019 * 2 ^ 59
def prefixEnd_515019 : Nat := 4983230072969 + 3 ^ 40 * 515019 * 2
def baseEnd_515019 : Nat := 156712470043274500440875

theorem tailTrace_515019 : CollatzResearch.WordTrace tailWord_515019 prefixEnd_515019 156712470043274500440875 := by
  unfold tailWord_515019
  simp only [CollatzResearch.WordTrace]
  refine ⟨18784286121181596087596111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12522857414121064058397407 18784286121181596087596111)
  ·
    refine ⟨28176429181772394131394167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18784286121181596087596111 28176429181772394131394167)
    ·
      refine ⟨42264643772658591197091251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28176429181772394131394167 42264643772658591197091251)
      ·
        refine ⟨63396965658987886795636877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42264643772658591197091251 63396965658987886795636877)
        ·
          refine ⟨23773862122120457548363829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63396965658987886795636877 23773862122120457548363829)
          ·
            refine ⟨2228799573948792895159109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23773862122120457548363829 2228799573948792895159109)
            ·
              refine ⟨417899920115398667842333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2228799573948792895159109 417899920115398667842333)
              ·
                refine ⟨156712470043274500440875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417899920115398667842333 156712470043274500440875)
                ·
                  rfl

theorem cell19_515019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 3].length) (baseStart_515019 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515019 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515019 prefixEnd_515019 := by exact prefixLift 515019
  have htrace : WordTrace (prefixWord ++ tailWord_515019) baseStart_515019 baseEnd_515019 := by
    simpa [prefixWord, tailWord_515019, baseEnd_515019] using wordTrace_append hprefix tailTrace_515019
  have hstable : (prefixWord ++ tailWord_515019).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515019).length < 2 ^ (prefixWord ++ tailWord_515019).sum := by decide
  have hdescent : baseEnd_515019 < baseStart_515019 := by decide
  rcases family_descends (prefixWord ++ tailWord_515019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515057 : List Nat := [1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_515057 : Nat := 118140960795 + 515057 * 2 ^ 59
def prefixEnd_515057 : Nat := 4983230072969 + 3 ^ 40 * 515057 * 2
def baseEnd_515057 : Nat := 156724032866901671596327

theorem tailTrace_515057 : CollatzResearch.WordTrace tailWord_515057 prefixEnd_515057 156724032866901671596327 := by
  unfold tailWord_515057
  simp only [CollatzResearch.WordTrace]
  refine ⟨18785672095043928577479425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12523781396695952384986283 18785672095043928577479425)
  ·
    refine ⟨14089254071282946433109569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18785672095043928577479425 14089254071282946433109569)
    ·
      refine ⟨10566940553462209824832177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14089254071282946433109569 10566940553462209824832177)
      ·
        refine ⟨7925205415096657368624133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10566940553462209824832177 7925205415096657368624133)
        ·
          refine ⟨1485976015330623256617025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7925205415096657368624133 1485976015330623256617025)
          ·
            refine ⟨1114482011497967442462769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1485976015330623256617025 1114482011497967442462769)
            ·
              refine ⟨835861508623475581847077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114482011497967442462769 835861508623475581847077)
              ·
                refine ⟨156724032866901671596327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 835861508623475581847077 156724032866901671596327)
                ·
                  rfl

theorem cell19_515057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_515057 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515057 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515057 prefixEnd_515057 := by exact prefixLift 515057
  have htrace : WordTrace (prefixWord ++ tailWord_515057) baseStart_515057 baseEnd_515057 := by
    simpa [prefixWord, tailWord_515057, baseEnd_515057] using wordTrace_append hprefix tailTrace_515057
  have hstable : (prefixWord ++ tailWord_515057).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515057).length < 2 ^ (prefixWord ++ tailWord_515057).sum := by decide
  have hdescent : baseEnd_515057 < baseStart_515057 := by decide
  rcases family_descends (prefixWord ++ tailWord_515057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515173 : List Nat := [1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_515173 : Nat := 118140960795 + 515173 * 2 ^ 59
def prefixEnd_515173 : Nat := 4983230072969 + 3 ^ 40 * 515173 * 2
def baseEnd_515173 : Nat := 156759329907447773018233

theorem tailTrace_515173 : CollatzResearch.WordTrace tailWord_515173 prefixEnd_515173 156759329907447773018233 := by
  unfold tailWord_515173
  simp only [CollatzResearch.WordTrace]
  refine ⟨18789902962623680388702173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12526601975082453592468115 18789902962623680388702173)
  ·
    refine ⟨7046213610983880145763315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18789902962623680388702173 7046213610983880145763315)
    ·
      refine ⟨10569320416475820218644973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7046213610983880145763315 10569320416475820218644973)
      ·
        refine ⟨3963495156178432581991865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10569320416475820218644973 3963495156178432581991865)
        ·
          refine ⟨2972621367133824436493899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3963495156178432581991865 2972621367133824436493899)
          ·
            refine ⟨4458932050700736654740849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972621367133824436493899 4458932050700736654740849)
            ·
              refine ⟨3344199038025552491055637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458932050700736654740849 3344199038025552491055637)
              ·
                refine ⟨156759329907447773018233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3344199038025552491055637 156759329907447773018233)
                ·
                  rfl

theorem cell19_515173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_515173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515173 prefixEnd_515173 := by exact prefixLift 515173
  have htrace : WordTrace (prefixWord ++ tailWord_515173) baseStart_515173 baseEnd_515173 := by
    simpa [prefixWord, tailWord_515173, baseEnd_515173] using wordTrace_append hprefix tailTrace_515173
  have hstable : (prefixWord ++ tailWord_515173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515173).length < 2 ^ (prefixWord ++ tailWord_515173).sum := by decide
  have hdescent : baseEnd_515173 < baseStart_515173 := by decide
  rcases family_descends (prefixWord ++ tailWord_515173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515190 : List Nat := [5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_515190 : Nat := 118140960795 + 515190 * 2 ^ 59
def prefixEnd_515190 : Nat := 4983230072969 + 3 ^ 40 * 515190 * 2
def baseEnd_515190 : Nat := 156764502749596770640409

theorem tailTrace_515190 : CollatzResearch.WordTrace tailWord_515190 prefixEnd_515190 156764502749596770640409 := by
  unfold tailWord_515190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1174407687722630768254439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12527015335708061528047349 1174407687722630768254439)
  ·
    refine ⟨1761611531583946152381659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1174407687722630768254439 1761611531583946152381659)
    ·
      refine ⟨2642417297375919228572489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1761611531583946152381659 2642417297375919228572489)
      ·
        refine ⟨1981812973031939421429367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2642417297375919228572489 1981812973031939421429367)
        ·
          refine ⟨2972719459547909132144051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981812973031939421429367 2972719459547909132144051)
          ·
            refine ⟨4459079189321863698216077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972719459547909132144051 4459079189321863698216077)
            ·
              refine ⟨1672154695995698886831029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4459079189321863698216077 1672154695995698886831029)
              ·
                refine ⟨156764502749596770640409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1672154695995698886831029 156764502749596770640409)
                ·
                  rfl

theorem cell19_515190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_515190 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515190 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515190 prefixEnd_515190 := by exact prefixLift 515190
  have htrace : WordTrace (prefixWord ++ tailWord_515190) baseStart_515190 baseEnd_515190 := by
    simpa [prefixWord, tailWord_515190, baseEnd_515190] using wordTrace_append hprefix tailTrace_515190
  have hstable : (prefixWord ++ tailWord_515190).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515190).length < 2 ^ (prefixWord ++ tailWord_515190).sum := by decide
  have hdescent : baseEnd_515190 < baseStart_515190 := by decide
  rcases family_descends (prefixWord ++ tailWord_515190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515228 : List Nat := [2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_515228 : Nat := 118140960795 + 515228 * 2 ^ 59
def prefixEnd_515228 : Nat := 4983230072969 + 3 ^ 40 * 515228 * 2
def baseEnd_515228 : Nat := 156776065573223941795861

theorem tailTrace_515228 : CollatzResearch.WordTrace tailWord_515228 prefixEnd_515228 156776065573223941795861 := by
  unfold tailWord_515228
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395954488712212390977169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12527939318282949854636225 9395954488712212390977169)
  ·
    refine ⟨7046965866534159293232877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9395954488712212390977169 7046965866534159293232877)
    ·
      refine ⟨2642612199950309734962329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7046965866534159293232877 2642612199950309734962329)
      ·
        refine ⟨1981959149962732301221747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2642612199950309734962329 1981959149962732301221747)
        ·
          refine ⟨2972938724944098451832621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981959149962732301221747 2972938724944098451832621)
          ·
            refine ⟨1114852021854036919437233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2972938724944098451832621 1114852021854036919437233)
            ·
              refine ⟨836139016390527689577925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114852021854036919437233 836139016390527689577925)
              ·
                refine ⟨156776065573223941795861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836139016390527689577925 156776065573223941795861)
                ·
                  rfl

theorem cell19_515228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_515228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515228 prefixEnd_515228 := by exact prefixLift 515228
  have htrace : WordTrace (prefixWord ++ tailWord_515228) baseStart_515228 baseEnd_515228 := by
    simpa [prefixWord, tailWord_515228, baseEnd_515228] using wordTrace_append hprefix tailTrace_515228
  have hstable : (prefixWord ++ tailWord_515228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515228).length < 2 ^ (prefixWord ++ tailWord_515228).sum := by decide
  have hdescent : baseEnd_515228 < baseStart_515228 := by decide
  rcases family_descends (prefixWord ++ tailWord_515228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515268 : List Nat := [2, 3, 3, 1, 10]
def baseStart_515268 : Nat := 118140960795 + 515268 * 2 ^ 59
def prefixEnd_515268 : Nat := 4983230072969 + 3 ^ 40 * 515268 * 2
def baseEnd_515268 : Nat := 5806971739500581515069

theorem tailTrace_515268 : CollatzResearch.WordTrace tailWord_515268 prefixEnd_515268 5806971739500581515069 := by
  unfold tailWord_515268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9396683948639755806705229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12528911931519674408940305 9396683948639755806705229)
  ·
    refine ⟨3523756480739908427514461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9396683948639755806705229 3523756480739908427514461)
    ·
      refine ⟨1321408680277465660317923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3523756480739908427514461 1321408680277465660317923)
      ·
        refine ⟨1982113020416198490476885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321408680277465660317923 1982113020416198490476885)
        ·
          refine ⟨5806971739500581515069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1982113020416198490476885 5806971739500581515069)
          ·
            rfl

theorem cell19_515268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 10].length) (baseStart_515268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515268 prefixEnd_515268 := by exact prefixLift 515268
  have htrace : WordTrace (prefixWord ++ tailWord_515268) baseStart_515268 baseEnd_515268 := by
    simpa [prefixWord, tailWord_515268, baseEnd_515268] using wordTrace_append hprefix tailTrace_515268
  have hstable : (prefixWord ++ tailWord_515268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515268).length < 2 ^ (prefixWord ++ tailWord_515268).sum := by decide
  have hdescent : baseEnd_515268 < baseStart_515268 := by decide
  rcases family_descends (prefixWord ++ tailWord_515268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515285 : List Nat := [1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_515285 : Nat := 118140960795 + 515285 * 2 ^ 59
def prefixEnd_515285 : Nat := 4983230072969 + 3 ^ 40 * 515285 * 2
def baseEnd_515285 : Nat := 156793409808664698529039

theorem tailTrace_515285 : CollatzResearch.WordTrace tailWord_515285 prefixEnd_515285 156793409808664698529039 := by
  unfold tailWord_515285
  simp only [CollatzResearch.WordTrace]
  refine ⟨18793987938217923516779309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12529325292145282344519539 18793987938217923516779309)
  ·
    refine ⟨7047745476831721318792241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18793987938217923516779309 7047745476831721318792241)
    ·
      refine ⟨5285809107623790989094181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7047745476831721318792241 5285809107623790989094181)
      ·
        refine ⟨991089207679460810455159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5285809107623790989094181 991089207679460810455159)
        ·
          refine ⟨1486633811519191215682739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991089207679460810455159 1486633811519191215682739)
          ·
            refine ⟨2229950717278786823524109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486633811519191215682739 2229950717278786823524109)
            ·
              refine ⟨836231518979545058821541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2229950717278786823524109 836231518979545058821541)
              ·
                refine ⟨156793409808664698529039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836231518979545058821541 156793409808664698529039)
                ·
                  rfl

theorem cell19_515285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_515285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515285 prefixEnd_515285 := by exact prefixLift 515285
  have htrace : WordTrace (prefixWord ++ tailWord_515285) baseStart_515285 baseEnd_515285 := by
    simpa [prefixWord, tailWord_515285, baseEnd_515285] using wordTrace_append hprefix tailTrace_515285
  have hstable : (prefixWord ++ tailWord_515285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515285).length < 2 ^ (prefixWord ++ tailWord_515285).sum := by decide
  have hdescent : baseEnd_515285 < baseStart_515285 := by decide
  rcases family_descends (prefixWord ++ tailWord_515285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515287 : List Nat := [1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_515287 : Nat := 118140960795 + 515287 * 2 ^ 59
def prefixEnd_515287 : Nat := 4983230072969 + 3 ^ 40 * 515287 * 2
def baseEnd_515287 : Nat := 156794018378329286484589

theorem tailTrace_515287 : CollatzResearch.WordTrace tailWord_515287 prefixEnd_515287 156794018378329286484589 := by
  unfold tailWord_515287
  simp only [CollatzResearch.WordTrace]
  refine ⟨18794060884210677858352115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12529373922807118572234743 18794060884210677858352115)
  ·
    refine ⟨28191091326316016787528173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18794060884210677858352115 28191091326316016787528173)
    ·
      refine ⟨10571659247368506295323065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28191091326316016787528173 10571659247368506295323065)
      ·
        refine ⟨7928744435526379721492299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10571659247368506295323065 7928744435526379721492299)
        ·
          refine ⟨11893116653289569582238449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7928744435526379721492299 11893116653289569582238449)
          ·
            refine ⟨8919837489967177186678837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11893116653289569582238449 8919837489967177186678837)
            ·
              refine ⟨836234764684422861251141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8919837489967177186678837 836234764684422861251141)
              ·
                refine ⟨156794018378329286484589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836234764684422861251141 156794018378329286484589)
                ·
                  rfl

theorem cell19_515287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_515287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515287 prefixEnd_515287 := by exact prefixLift 515287
  have htrace : WordTrace (prefixWord ++ tailWord_515287) baseStart_515287 baseEnd_515287 := by
    simpa [prefixWord, tailWord_515287, baseEnd_515287] using wordTrace_append hprefix tailTrace_515287
  have hstable : (prefixWord ++ tailWord_515287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515287).length < 2 ^ (prefixWord ++ tailWord_515287).sum := by decide
  have hdescent : baseEnd_515287 < baseStart_515287 := by decide
  rcases family_descends (prefixWord ++ tailWord_515287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515304 : List Nat := [2, 1, 4, 1, 2, 1, 5, 3]
def baseStart_515304 : Nat := 118140960795 + 515304 * 2 ^ 59
def prefixEnd_515304 : Nat := 4983230072969 + 3 ^ 40 * 515304 * 2
def baseEnd_515304 : Nat := 156799191220478284106765

theorem tailTrace_515304 : CollatzResearch.WordTrace tailWord_515304 prefixEnd_515304 156799191220478284106765 := by
  unfold tailWord_515304
  simp only [CollatzResearch.WordTrace]
  refine ⟨9397340462574544880860483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12529787283432726507813977 9397340462574544880860483)
  ·
    refine ⟨14096010693861817321290725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9397340462574544880860483 14096010693861817321290725)
    ·
      refine ⟨2643002005099090747742011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14096010693861817321290725 2643002005099090747742011)
      ·
        refine ⟨3964503007648636121613017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643002005099090747742011 3964503007648636121613017)
        ·
          refine ⟨2973377255736477091209763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3964503007648636121613017 2973377255736477091209763)
          ·
            refine ⟨4460065883604715636814645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973377255736477091209763 4460065883604715636814645)
            ·
              refine ⟨418131176587942090951373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4460065883604715636814645 418131176587942090951373)
              ·
                refine ⟨156799191220478284106765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418131176587942090951373 156799191220478284106765)
                ·
                  rfl

theorem cell19_515304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_515304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515304 prefixEnd_515304 := by exact prefixLift 515304
  have htrace : WordTrace (prefixWord ++ tailWord_515304) baseStart_515304 baseEnd_515304 := by
    simpa [prefixWord, tailWord_515304, baseEnd_515304] using wordTrace_append hprefix tailTrace_515304
  have hstable : (prefixWord ++ tailWord_515304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515304).length < 2 ^ (prefixWord ++ tailWord_515304).sum := by decide
  have hdescent : baseEnd_515304 < baseStart_515304 := by decide
  rcases family_descends (prefixWord ++ tailWord_515304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515359 : List Nat := [1, 1, 2, 4, 4, 2, 2, 3]
def baseStart_515359 : Nat := 118140960795 + 515359 * 2 ^ 59
def prefixEnd_515359 : Nat := 4983230072969 + 3 ^ 40 * 515359 * 2
def baseEnd_515359 : Nat := 156815926886254452884393

theorem tailTrace_515359 : CollatzResearch.WordTrace tailWord_515359 prefixEnd_515359 156815926886254452884393 := by
  unfold tailWord_515359
  simp only [CollatzResearch.WordTrace]
  refine ⟨18796686939949834154973131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12531124626633222769982087 18796686939949834154973131)
  ·
    refine ⟨28195030409924751232459697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18796686939949834154973131 28195030409924751232459697)
    ·
      refine ⟨21146272807443563424344773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28195030409924751232459697 21146272807443563424344773)
      ·
        refine ⟨3964926151395668142064645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21146272807443563424344773 3964926151395668142064645)
        ·
          refine ⟨743423653386687776637121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3964926151395668142064645 743423653386687776637121)
          ·
            refine ⟨557567740040015832477841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743423653386687776637121 557567740040015832477841)
            ·
              refine ⟨418175805030011874358381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557567740040015832477841 418175805030011874358381)
              ·
                refine ⟨156815926886254452884393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418175805030011874358381 156815926886254452884393)
                ·
                  rfl

theorem cell19_515359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 3].length) (baseStart_515359 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515359 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515359 prefixEnd_515359 := by exact prefixLift 515359
  have htrace : WordTrace (prefixWord ++ tailWord_515359) baseStart_515359 baseEnd_515359 := by
    simpa [prefixWord, tailWord_515359, baseEnd_515359] using wordTrace_append hprefix tailTrace_515359
  have hstable : (prefixWord ++ tailWord_515359).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515359).length < 2 ^ (prefixWord ++ tailWord_515359).sum := by decide
  have hdescent : baseEnd_515359 < baseStart_515359 := by decide
  rcases family_descends (prefixWord ++ tailWord_515359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515363 : List Nat := [1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_515363 : Nat := 118140960795 + 515363 * 2 ^ 59
def prefixEnd_515363 : Nat := 4983230072969 + 3 ^ 40 * 515363 * 2
def baseEnd_515363 : Nat := 156817144025583628795493

theorem tailTrace_515363 : CollatzResearch.WordTrace tailWord_515363 prefixEnd_515363 156817144025583628795493 := by
  unfold tailWord_515363
  simp only [CollatzResearch.WordTrace]
  refine ⟨18796832831935342838118743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12531221887956895225412495 18796832831935342838118743)
  ·
    refine ⟨28195249247903014257178115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18796832831935342838118743 28195249247903014257178115)
    ·
      refine ⟨42292873871854521385767173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28195249247903014257178115 42292873871854521385767173)
      ·
        refine ⟨7929913850972722759831345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42292873871854521385767173 7929913850972722759831345)
        ·
          refine ⟨5947435388229542069873509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7929913850972722759831345 5947435388229542069873509)
          ·
            refine ⟨1115144135293039138101283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5947435388229542069873509 1115144135293039138101283)
            ·
              refine ⟨1672716202939558707151925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115144135293039138101283 1672716202939558707151925)
              ·
                refine ⟨156817144025583628795493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1672716202939558707151925 156817144025583628795493)
                ·
                  rfl

theorem cell19_515363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_515363 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515363 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515363 prefixEnd_515363 := by exact prefixLift 515363
  have htrace : WordTrace (prefixWord ++ tailWord_515363) baseStart_515363 baseEnd_515363 := by
    simpa [prefixWord, tailWord_515363, baseEnd_515363] using wordTrace_append hprefix tailTrace_515363
  have hstable : (prefixWord ++ tailWord_515363).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515363).length < 2 ^ (prefixWord ++ tailWord_515363).sum := by decide
  have hdescent : baseEnd_515363 < baseStart_515363 := by decide
  rcases family_descends (prefixWord ++ tailWord_515363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515522 : List Nat := [3, 5, 2, 1, 2, 1, 2, 3]
def baseStart_515522 : Nat := 118140960795 + 515522 * 2 ^ 59
def prefixEnd_515522 : Nat := 4983230072969 + 3 ^ 40 * 515522 * 2
def baseEnd_515522 : Nat := 156865525313918371261727

theorem tailTrace_515522 : CollatzResearch.WordTrace tailWord_515522 prefixEnd_515522 156865525313918371261727 := by
  unfold tailWord_515522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4700658009589828248289205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12535088025572875328771213 4700658009589828248289205)
  ·
    refine ⟨440686688399046398277113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4700658009589828248289205 440686688399046398277113)
    ·
      refine ⟨330515016299284798707835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440686688399046398277113 330515016299284798707835)
      ·
        refine ⟨495772524448927198061753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330515016299284798707835 495772524448927198061753)
        ·
          refine ⟨371829393336695398546315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495772524448927198061753 371829393336695398546315)
          ·
            refine ⟨557744090005043097819473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371829393336695398546315 557744090005043097819473)
            ·
              refine ⟨418308067503782323364605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557744090005043097819473 418308067503782323364605)
              ·
                refine ⟨156865525313918371261727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418308067503782323364605 156865525313918371261727)
                ·
                  rfl

theorem cell19_515522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_515522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515522 prefixEnd_515522 := by exact prefixLift 515522
  have htrace : WordTrace (prefixWord ++ tailWord_515522) baseStart_515522 baseEnd_515522 := by
    simpa [prefixWord, tailWord_515522, baseEnd_515522] using wordTrace_append hprefix tailTrace_515522
  have hstable : (prefixWord ++ tailWord_515522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515522).length < 2 ^ (prefixWord ++ tailWord_515522).sum := by decide
  have hdescent : baseEnd_515522 < baseStart_515522 := by decide
  rcases family_descends (prefixWord ++ tailWord_515522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515532 : List Nat := [2, 2, 1, 4, 2, 1, 4, 3]
def baseStart_515532 : Nat := 118140960795 + 515532 * 2 ^ 59
def prefixEnd_515532 : Nat := 4983230072969 + 3 ^ 40 * 515532 * 2
def baseEnd_515532 : Nat := 156868568162241311039477

theorem tailTrace_515532 : CollatzResearch.WordTrace tailWord_515532 prefixEnd_515532 156868568162241311039477 := by
  unfold tailWord_515532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401498384161542350510425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12535331178882056467347233 9401498384161542350510425)
  ·
    refine ⟨7051123788121156762882819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9401498384161542350510425 7051123788121156762882819)
    ·
      refine ⟨10576685682181735144324229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7051123788121156762882819 10576685682181735144324229)
      ·
        refine ⟨1983128565409075339560793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10576685682181735144324229 1983128565409075339560793)
        ·
          refine ⟨1487346424056806504670595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1983128565409075339560793 1487346424056806504670595)
          ·
            refine ⟨2231019636085209757005893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487346424056806504670595 2231019636085209757005893)
            ·
              refine ⟨418316181765976829438605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2231019636085209757005893 418316181765976829438605)
              ·
                refine ⟨156868568162241311039477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418316181765976829438605 156868568162241311039477)
                ·
                  rfl

theorem cell19_515532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_515532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515532 prefixEnd_515532 := by exact prefixLift 515532
  have htrace : WordTrace (prefixWord ++ tailWord_515532) baseStart_515532 baseEnd_515532 := by
    simpa [prefixWord, tailWord_515532, baseEnd_515532] using wordTrace_append hprefix tailTrace_515532
  have hstable : (prefixWord ++ tailWord_515532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515532).length < 2 ^ (prefixWord ++ tailWord_515532).sum := by decide
  have hdescent : baseEnd_515532 < baseStart_515532 := by decide
  rcases family_descends (prefixWord ++ tailWord_515532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515536 : List Nat := [2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_515536 : Nat := 118140960795 + 515536 * 2 ^ 59
def prefixEnd_515536 : Nat := 4983230072969 + 3 ^ 40 * 515536 * 2
def baseEnd_515536 : Nat := 156869785301570486950577

theorem tailTrace_515536 : CollatzResearch.WordTrace tailWord_515536 prefixEnd_515536 156869785301570486950577 := by
  unfold tailWord_515536
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401571330154296692083231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12535428440205728922777641 9401571330154296692083231)
  ·
    refine ⟨14102356995231445038124847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9401571330154296692083231 14102356995231445038124847)
    ·
      refine ⟨21153535492847167557187271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14102356995231445038124847 21153535492847167557187271)
      ·
        refine ⟨31730303239270751335780907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21153535492847167557187271 31730303239270751335780907)
        ·
          refine ⟨47595454858906127003671361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31730303239270751335780907 47595454858906127003671361)
          ·
            refine ⟨35696591144179595252753521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47595454858906127003671361 35696591144179595252753521)
            ·
              refine ⟨26772443358134696439565141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35696591144179595252753521 26772443358134696439565141)
              ·
                refine ⟨156869785301570486950577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26772443358134696439565141 156869785301570486950577)
                ·
                  rfl

theorem cell19_515536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_515536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515536 prefixEnd_515536 := by exact prefixLift 515536
  have htrace : WordTrace (prefixWord ++ tailWord_515536) baseStart_515536 baseEnd_515536 := by
    simpa [prefixWord, tailWord_515536, baseEnd_515536] using wordTrace_append hprefix tailTrace_515536
  have hstable : (prefixWord ++ tailWord_515536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515536).length < 2 ^ (prefixWord ++ tailWord_515536).sum := by decide
  have hdescent : baseEnd_515536 < baseStart_515536 := by decide
  rcases family_descends (prefixWord ++ tailWord_515536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515553 : List Nat := [1, 2, 3, 1, 2, 5, 5]
def baseStart_515553 : Nat := 118140960795 + 515553 * 2 ^ 59
def prefixEnd_515553 : Nat := 4983230072969 + 3 ^ 40 * 515553 * 2
def baseEnd_515553 : Nat := 52291652714573161524251

theorem tailTrace_515553 : CollatzResearch.WordTrace tailWord_515553 prefixEnd_515553 52291652714573161524251 := by
  unfold tailWord_515553
  simp only [CollatzResearch.WordTrace]
  refine ⟨18803762701247005287535313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12535841800831336858356875 18803762701247005287535313)
  ·
    refine ⟨14102822025935253965651485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18803762701247005287535313 14102822025935253965651485)
    ·
      refine ⟨5288558259725720237119307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14102822025935253965651485 5288558259725720237119307)
      ·
        refine ⟨7932837389588580355678961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5288558259725720237119307 7932837389588580355678961)
        ·
          refine ⟨5949628042191435266759221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7932837389588580355678961 5949628042191435266759221)
          ·
            refine ⟨557777628955447056258677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5949628042191435266759221 557777628955447056258677)
            ·
              refine ⟨52291652714573161524251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 557777628955447056258677 52291652714573161524251)
              ·
                rfl

theorem cell19_515553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_515553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515553 prefixEnd_515553 := by exact prefixLift 515553
  have htrace : WordTrace (prefixWord ++ tailWord_515553) baseStart_515553 baseEnd_515553 := by
    simpa [prefixWord, tailWord_515553, baseEnd_515553] using wordTrace_append hprefix tailTrace_515553
  have hstable : (prefixWord ++ tailWord_515553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515553).length < 2 ^ (prefixWord ++ tailWord_515553).sum := by decide
  have hdescent : baseEnd_515553 < baseStart_515553 := by decide
  rcases family_descends (prefixWord ++ tailWord_515553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515570 : List Nat := [3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_515570 : Nat := 118140960795 + 515570 * 2 ^ 59
def prefixEnd_515570 : Nat := 4983230072969 + 3 ^ 40 * 515570 * 2
def baseEnd_515570 : Nat := 156880130985868482194929

theorem tailTrace_515570 : CollatzResearch.WordTrace tailWord_515570 prefixEnd_515570 156880130985868482194929 := by
  unfold tailWord_515570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4701095685546354297726041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12536255161456944793936109 4701095685546354297726041)
  ·
    refine ⟨3525821764159765723294531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4701095685546354297726041 3525821764159765723294531)
    ·
      refine ⟨5288732646239648584941797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3525821764159765723294531 5288732646239648584941797)
      ·
        refine ⟨991637371169934109676587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5288732646239648584941797 991637371169934109676587)
        ·
          refine ⟨1487456056754901164514881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991637371169934109676587 1487456056754901164514881)
          ·
            refine ⟨1115592042566175873386161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1487456056754901164514881 1115592042566175873386161)
            ·
              refine ⟨836694031924631905039621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115592042566175873386161 836694031924631905039621)
              ·
                refine ⟨156880130985868482194929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836694031924631905039621 156880130985868482194929)
                ·
                  rfl

theorem cell19_515570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_515570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515570 prefixEnd_515570 := by exact prefixLift 515570
  have htrace : WordTrace (prefixWord ++ tailWord_515570) baseStart_515570 baseEnd_515570 := by
    simpa [prefixWord, tailWord_515570, baseEnd_515570] using wordTrace_append hprefix tailTrace_515570
  have hstable : (prefixWord ++ tailWord_515570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515570).length < 2 ^ (prefixWord ++ tailWord_515570).sum := by decide
  have hdescent : baseEnd_515570 < baseStart_515570 := by decide
  rcases family_descends (prefixWord ++ tailWord_515570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515591 : List Nat := [1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_515591 : Nat := 118140960795 + 515591 * 2 ^ 59
def prefixEnd_515591 : Nat := 4983230072969 + 3 ^ 40 * 515591 * 2
def baseEnd_515591 : Nat := 156886520967346655728205

theorem tailTrace_515591 : CollatzResearch.WordTrace tailWord_515591 prefixEnd_515591 156886520967346655728205 := by
  unfold tailWord_515591
  simp only [CollatzResearch.WordTrace]
  refine ⟨18805148675109337777418627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12536765783406225184945751 18805148675109337777418627)
  ·
    refine ⟨28207723012664006666127941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18805148675109337777418627 28207723012664006666127941)
    ·
      refine ⟨5288948064874501249898989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28207723012664006666127941 5288948064874501249898989)
      ·
        refine ⟨1983355524327937968712121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5288948064874501249898989 1983355524327937968712121)
        ·
          refine ⟨1487516643245953476534091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1983355524327937968712121 1487516643245953476534091)
          ·
            refine ⟨2231274964868930214801137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487516643245953476534091 2231274964868930214801137)
            ·
              refine ⟨1673456223651697661100853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2231274964868930214801137 1673456223651697661100853)
              ·
                refine ⟨156886520967346655728205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1673456223651697661100853 156886520967346655728205)
                ·
                  rfl

theorem cell19_515591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_515591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515591 prefixEnd_515591 := by exact prefixLift 515591
  have htrace : WordTrace (prefixWord ++ tailWord_515591) baseStart_515591 baseEnd_515591 := by
    simpa [prefixWord, tailWord_515591, baseEnd_515591] using wordTrace_append hprefix tailTrace_515591
  have hstable : (prefixWord ++ tailWord_515591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515591).length < 2 ^ (prefixWord ++ tailWord_515591).sum := by decide
  have hdescent : baseEnd_515591 < baseStart_515591 := by decide
  rcases family_descends (prefixWord ++ tailWord_515591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515593 : List Nat := [1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_515593 : Nat := 118140960795 + 515593 * 2 ^ 59
def prefixEnd_515593 : Nat := 4983230072969 + 3 ^ 40 * 515593 * 2
def baseEnd_515593 : Nat := 156887129537011243683755

theorem tailTrace_515593 : CollatzResearch.WordTrace tailWord_515593 prefixEnd_515593 156887129537011243683755 := by
  unfold tailWord_515593
  simp only [CollatzResearch.WordTrace]
  refine ⟨18805221621102092118991433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12536814414068061412660955 18805221621102092118991433)
  ·
    refine ⟨14103916215826569089243575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18805221621102092118991433 14103916215826569089243575)
    ·
      refine ⟨21155874323739853633865363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14103916215826569089243575 21155874323739853633865363)
      ·
        refine ⟨31733811485609780450798045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21155874323739853633865363 31733811485609780450798045)
        ·
          refine ⟨11900179307103667669049267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31733811485609780450798045 11900179307103667669049267)
          ·
            refine ⟨17850268960655501503573901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11900179307103667669049267 17850268960655501503573901)
            ·
              refine ⟨6693850860245813063840213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17850268960655501503573901 6693850860245813063840213)
              ·
                refine ⟨156887129537011243683755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6693850860245813063840213 156887129537011243683755)
                ·
                  rfl

theorem cell19_515593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_515593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515593 prefixEnd_515593 := by exact prefixLift 515593
  have htrace : WordTrace (prefixWord ++ tailWord_515593) baseStart_515593 baseEnd_515593 := by
    simpa [prefixWord, tailWord_515593, baseEnd_515593] using wordTrace_append hprefix tailTrace_515593
  have hstable : (prefixWord ++ tailWord_515593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515593).length < 2 ^ (prefixWord ++ tailWord_515593).sum := by decide
  have hdescent : baseEnd_515593 < baseStart_515593 := by decide
  rcases family_descends (prefixWord ++ tailWord_515593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515701 : List Nat := [1, 3, 4, 2, 1, 3, 2, 3]
def baseStart_515701 : Nat := 118140960795 + 515701 * 2 ^ 59
def prefixEnd_515701 : Nat := 4983230072969 + 3 ^ 40 * 515701 * 2
def baseEnd_515701 : Nat := 156919992298898993283461

theorem tailTrace_515701 : CollatzResearch.WordTrace tailWord_515701 prefixEnd_515701 156919992298898993283461 := by
  unfold tailWord_515701
  simp only [CollatzResearch.WordTrace]
  refine ⟨18809160704710826563922957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12539440469807217709281971 18809160704710826563922957)
  ·
    refine ⟨7053435264266559961471109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18809160704710826563922957 7053435264266559961471109)
    ·
      refine ⟨1322519112049979992775833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7053435264266559961471109 1322519112049979992775833)
      ·
        refine ⟨991889334037484994581875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1322519112049979992775833 991889334037484994581875)
        ·
          refine ⟨1487834001056227491872813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991889334037484994581875 1487834001056227491872813)
          ·
            refine ⟨557937750396085309452305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1487834001056227491872813 557937750396085309452305)
            ·
              refine ⟨418453312797063982089229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557937750396085309452305 418453312797063982089229)
              ·
                refine ⟨156919992298898993283461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418453312797063982089229 156919992298898993283461)
                ·
                  rfl

theorem cell19_515701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 3].length) (baseStart_515701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515701 prefixEnd_515701 := by exact prefixLift 515701
  have htrace : WordTrace (prefixWord ++ tailWord_515701) baseStart_515701 baseEnd_515701 := by
    simpa [prefixWord, tailWord_515701, baseEnd_515701] using wordTrace_append hprefix tailTrace_515701
  have hstable : (prefixWord ++ tailWord_515701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515701).length < 2 ^ (prefixWord ++ tailWord_515701).sum := by decide
  have hdescent : baseEnd_515701 < baseStart_515701 := by decide
  rcases family_descends (prefixWord ++ tailWord_515701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515707 : List Nat := [1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_515707 : Nat := 118140960795 + 515707 * 2 ^ 59
def prefixEnd_515707 : Nat := 4983230072969 + 3 ^ 40 * 515707 * 2
def baseEnd_515707 : Nat := 156921818007892757150111

theorem tailTrace_515707 : CollatzResearch.WordTrace tailWord_515707 prefixEnd_515707 156921818007892757150111 := by
  unfold tailWord_515707
  simp only [CollatzResearch.WordTrace]
  refine ⟨18809379542689089588641375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12539586361792726392427583 18809379542689089588641375)
  ·
    refine ⟨28214069314033634382962063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18809379542689089588641375 28214069314033634382962063)
    ·
      refine ⟨42321103971050451574443095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28214069314033634382962063 42321103971050451574443095)
      ·
        refine ⟨63481655956575677361664643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42321103971050451574443095 63481655956575677361664643)
        ·
          refine ⟨95222483934863516042496965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63481655956575677361664643 95222483934863516042496965)
          ·
            refine ⟨17854215737786909257968181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95222483934863516042496965 17854215737786909257968181)
            ·
              refine ⟨1673832725417522742934517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17854215737786909257968181 1673832725417522742934517)
              ·
                refine ⟨156921818007892757150111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1673832725417522742934517 156921818007892757150111)
                ·
                  rfl

theorem cell19_515707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_515707 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515707 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515707 prefixEnd_515707 := by exact prefixLift 515707
  have htrace : WordTrace (prefixWord ++ tailWord_515707) baseStart_515707 baseEnd_515707 := by
    simpa [prefixWord, tailWord_515707, baseEnd_515707] using wordTrace_append hprefix tailTrace_515707
  have hstable : (prefixWord ++ tailWord_515707).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515707).length < 2 ^ (prefixWord ++ tailWord_515707).sum := by decide
  have hdescent : baseEnd_515707 < baseStart_515707 := by decide
  rcases family_descends (prefixWord ++ tailWord_515707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515720 : List Nat := [2, 1, 3, 5, 2, 1, 5]
def baseStart_515720 : Nat := 118140960795 + 515720 * 2 ^ 59
def prefixEnd_515720 : Nat := 4983230072969 + 3 ^ 40 * 515720 * 2
def baseEnd_515720 : Nat := 52308591236904192953729

theorem tailTrace_515720 : CollatzResearch.WordTrace tailWord_515720 prefixEnd_515720 52308591236904192953729 := by
  unfold tailWord_515720
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404926845820996404432307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12539902461094661872576409 9404926845820996404432307)
  ·
    refine ⟨14107390268731494606648461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9404926845820996404432307 14107390268731494606648461)
    ·
      refine ⟨5290271350774310477493173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14107390268731494606648461 5290271350774310477493173)
      ·
        refine ⟨495962939135091607264985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5290271350774310477493173 495962939135091607264985)
        ·
          refine ⟨371972204351318705448739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495962939135091607264985 371972204351318705448739)
          ·
            refine ⟨557958306526978058173109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371972204351318705448739 557958306526978058173109)
            ·
              refine ⟨52308591236904192953729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 557958306526978058173109 52308591236904192953729)
              ·
                rfl

theorem cell19_515720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 5].length) (baseStart_515720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515720 prefixEnd_515720 := by exact prefixLift 515720
  have htrace : WordTrace (prefixWord ++ tailWord_515720) baseStart_515720 baseEnd_515720 := by
    simpa [prefixWord, tailWord_515720, baseEnd_515720] using wordTrace_append hprefix tailTrace_515720
  have hstable : (prefixWord ++ tailWord_515720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515720).length < 2 ^ (prefixWord ++ tailWord_515720).sum := by decide
  have hdescent : baseEnd_515720 < baseStart_515720 := by decide
  rcases family_descends (prefixWord ++ tailWord_515720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515815 : List Nat := [1, 1, 5, 4, 1, 1, 3, 3]
def baseStart_515815 : Nat := 118140960795 + 515815 * 2 ^ 59
def prefixEnd_515815 : Nat := 4983230072969 + 3 ^ 40 * 515815 * 2
def baseEnd_515815 : Nat := 156954680769780506749817

theorem tailTrace_515815 : CollatzResearch.WordTrace tailWord_515815 prefixEnd_515815 156954680769780506749817 := by
  unfold tailWord_515815
  simp only [CollatzResearch.WordTrace]
  refine ⟨18813318626297824033572899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12542212417531882689048599 18813318626297824033572899)
  ·
    refine ⟨28219977939446736050359349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18813318626297824033572899 28219977939446736050359349)
    ·
      refine ⟨2645622931823131504721189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28219977939446736050359349 2645622931823131504721189)
      ·
        refine ⟨496054299716837157135223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2645622931823131504721189 496054299716837157135223)
        ·
          refine ⟨744081449575255735702835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496054299716837157135223 744081449575255735702835)
          ·
            refine ⟨1116122174362883603554253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744081449575255735702835 1116122174362883603554253)
            ·
              refine ⟨418545815386081351332845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1116122174362883603554253 418545815386081351332845)
              ·
                refine ⟨156954680769780506749817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418545815386081351332845 156954680769780506749817)
                ·
                  rfl

theorem cell19_515815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 3].length) (baseStart_515815 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515815 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515815 prefixEnd_515815 := by exact prefixLift 515815
  have htrace : WordTrace (prefixWord ++ tailWord_515815) baseStart_515815 baseEnd_515815 := by
    simpa [prefixWord, tailWord_515815, baseEnd_515815] using wordTrace_append hprefix tailTrace_515815
  have hstable : (prefixWord ++ tailWord_515815).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515815).length < 2 ^ (prefixWord ++ tailWord_515815).sum := by decide
  have hdescent : baseEnd_515815 < baseStart_515815 := by decide
  rcases family_descends (prefixWord ++ tailWord_515815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515876 : List Nat := [2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_515876 : Nat := 118140960795 + 515876 * 2 ^ 59
def prefixEnd_515876 : Nat := 4983230072969 + 3 ^ 40 * 515876 * 2
def baseEnd_515876 : Nat := 156973242144550439394095

theorem tailTrace_515876 : CollatzResearch.WordTrace tailWord_515876 prefixEnd_515876 156973242144550439394095 := by
  unfold tailWord_515876
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407771739538415725771741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12543695652717887634362321 9407771739538415725771741)
  ·
    refine ⟨3527914402326905897164403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9407771739538415725771741 3527914402326905897164403)
    ·
      refine ⟨5291871603490358845746605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527914402326905897164403 5291871603490358845746605)
      ·
        refine ⟨1984451851308884567154977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5291871603490358845746605 1984451851308884567154977)
        ·
          refine ⟨1488338888481663425366233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1984451851308884567154977 1488338888481663425366233)
          ·
            refine ⟨1116254166361247569024675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1488338888481663425366233 1116254166361247569024675)
            ·
              refine ⟨1674381249541871353537013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116254166361247569024675 1674381249541871353537013)
              ·
                refine ⟨156973242144550439394095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1674381249541871353537013 156973242144550439394095)
                ·
                  rfl

theorem cell19_515876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_515876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515876 prefixEnd_515876 := by exact prefixLift 515876
  have htrace : WordTrace (prefixWord ++ tailWord_515876) baseStart_515876 baseEnd_515876 := by
    simpa [prefixWord, tailWord_515876, baseEnd_515876] using wordTrace_append hprefix tailTrace_515876
  have hstable : (prefixWord ++ tailWord_515876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515876).length < 2 ^ (prefixWord ++ tailWord_515876).sum := by decide
  have hdescent : baseEnd_515876 < baseStart_515876 := by decide
  rcases family_descends (prefixWord ++ tailWord_515876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515893 : List Nat := [1, 3, 3, 1, 5, 1, 5]
def baseStart_515893 : Nat := 118140960795 + 515893 * 2 ^ 59
def prefixEnd_515893 : Nat := 4983230072969 + 3 ^ 40 * 515893 * 2
def baseEnd_515893 : Nat := 52326138328899812338757

theorem tailTrace_515893 : CollatzResearch.WordTrace tailWord_515893 prefixEnd_515893 52326138328899812338757 := by
  unfold tailWord_515893
  simp only [CollatzResearch.WordTrace]
  refine ⟨18816163520015243354912333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12544109013343495569941555 18816163520015243354912333)
  ·
    refine ⟨7056061320005716258092125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18816163520015243354912333 7056061320005716258092125)
    ·
      refine ⟨2646022995002143596784547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7056061320005716258092125 2646022995002143596784547)
      ·
        refine ⟨3969034492503215395176821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2646022995002143596784547 3969034492503215395176821)
        ·
          refine ⟨372096983672176443297827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3969034492503215395176821 372096983672176443297827)
          ·
            refine ⟨558145475508264664946741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372096983672176443297827 558145475508264664946741)
            ·
              refine ⟨52326138328899812338757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 558145475508264664946741 52326138328899812338757)
              ·
                rfl

theorem cell19_515893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 5].length) (baseStart_515893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515893 prefixEnd_515893 := by exact prefixLift 515893
  have htrace : WordTrace (prefixWord ++ tailWord_515893) baseStart_515893 baseEnd_515893 := by
    simpa [prefixWord, tailWord_515893, baseEnd_515893] using wordTrace_append hprefix tailTrace_515893
  have hstable : (prefixWord ++ tailWord_515893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515893).length < 2 ^ (prefixWord ++ tailWord_515893).sum := by decide
  have hdescent : baseEnd_515893 < baseStart_515893 := by decide
  rcases family_descends (prefixWord ++ tailWord_515893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515910 : List Nat := [6, 1, 1, 2, 1, 2, 2, 4]
def baseStart_515910 : Nat := 118140960795 + 515910 * 2 ^ 59
def prefixEnd_515910 : Nat := 4983230072969 + 3 ^ 40 * 515910 * 2
def baseEnd_515910 : Nat := 156983587828848434638447

theorem tailTrace_515910 : CollatzResearch.WordTrace tailWord_515910 prefixEnd_515910 156983587828848434638447 := by
  unfold tailWord_515910
  simp only [CollatzResearch.WordTrace]
  refine ⟨588024486279801726821287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12544522373969103505520789 588024486279801726821287)
  ·
    refine ⟨882036729419702590231931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 588024486279801726821287 882036729419702590231931)
    ·
      refine ⟨1323055094129553885347897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 882036729419702590231931 1323055094129553885347897)
      ·
        refine ⟨992291320597165414010923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1323055094129553885347897 992291320597165414010923)
        ·
          refine ⟨1488436980895748121016385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992291320597165414010923 1488436980895748121016385)
          ·
            refine ⟨1116327735671811090762289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1488436980895748121016385 1116327735671811090762289)
            ·
              refine ⟨837245801753858318071717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1116327735671811090762289 837245801753858318071717)
              ·
                refine ⟨156983587828848434638447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837245801753858318071717 156983587828848434638447)
                ·
                  rfl

theorem cell19_515910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_515910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515910 prefixEnd_515910 := by exact prefixLift 515910
  have htrace : WordTrace (prefixWord ++ tailWord_515910) baseStart_515910 baseEnd_515910 := by
    simpa [prefixWord, tailWord_515910, baseEnd_515910] using wordTrace_append hprefix tailTrace_515910
  have hstable : (prefixWord ++ tailWord_515910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515910).length < 2 ^ (prefixWord ++ tailWord_515910).sum := by decide
  have hdescent : baseEnd_515910 < baseStart_515910 := by decide
  rcases family_descends (prefixWord ++ tailWord_515910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515935 : List Nat := [1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_515935 : Nat := 118140960795 + 515935 * 2 ^ 59
def prefixEnd_515935 : Nat := 4983230072969 + 3 ^ 40 * 515935 * 2
def baseEnd_515935 : Nat := 156991194949655784082823

theorem tailTrace_515935 : CollatzResearch.WordTrace tailWord_515935 prefixEnd_515935 156991194949655784082823 := by
  unfold tailWord_515935
  simp only [CollatzResearch.WordTrace]
  refine ⟨18817695385863084527941259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12545130257242056351960839 18817695385863084527941259)
  ·
    refine ⟨28226543078794626791911889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18817695385863084527941259 28226543078794626791911889)
    ·
      refine ⟨21169907309095970093933917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28226543078794626791911889 21169907309095970093933917)
      ·
        refine ⟨7938715240910988785225219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21169907309095970093933917 7938715240910988785225219)
        ·
          refine ⟨11908072861366483177837829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7938715240910988785225219 11908072861366483177837829)
          ·
            refine ⟨2232763661506215595844593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11908072861366483177837829 2232763661506215595844593)
            ·
              refine ⟨1674572746129661696883445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232763661506215595844593 1674572746129661696883445)
              ·
                refine ⟨156991194949655784082823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1674572746129661696883445 156991194949655784082823)
                ·
                  rfl

theorem cell19_515935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_515935 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515935 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515935 prefixEnd_515935 := by exact prefixLift 515935
  have htrace : WordTrace (prefixWord ++ tailWord_515935) baseStart_515935 baseEnd_515935 := by
    simpa [prefixWord, tailWord_515935, baseEnd_515935] using wordTrace_append hprefix tailTrace_515935
  have hstable : (prefixWord ++ tailWord_515935).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515935).length < 2 ^ (prefixWord ++ tailWord_515935).sum := by decide
  have hdescent : baseEnd_515935 < baseStart_515935 := by decide
  rcases family_descends (prefixWord ++ tailWord_515935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515971 : List Nat := [1, 1, 1, 3, 4, 4, 1, 4]
def baseStart_515971 : Nat := 118140960795 + 515971 * 2 ^ 59
def prefixEnd_515971 : Nat := 4983230072969 + 3 ^ 40 * 515971 * 2
def baseEnd_515971 : Nat := 157002149203618367282725

theorem tailTrace_515971 : CollatzResearch.WordTrace tailWord_515971 prefixEnd_515971 157002149203618367282725 := by
  unfold tailWord_515971
  simp only [CollatzResearch.WordTrace]
  refine ⟨18819008413732662676251767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12546005609155108450834511 18819008413732662676251767)
  ·
    refine ⟨28228512620598994014377651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18819008413732662676251767 28228512620598994014377651)
    ·
      refine ⟨42342768930898491021566477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28228512620598994014377651 42342768930898491021566477)
      ·
        refine ⟨15878538349086934133087429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42342768930898491021566477 15878538349086934133087429)
        ·
          refine ⟨2977225940453800149953893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15878538349086934133087429 2977225940453800149953893)
          ·
            refine ⟨558229863835087528116355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2977225940453800149953893 558229863835087528116355)
            ·
              refine ⟨837344795752631292174533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558229863835087528116355 837344795752631292174533)
              ·
                refine ⟨157002149203618367282725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837344795752631292174533 157002149203618367282725)
                ·
                  rfl

theorem cell19_515971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_515971 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515971 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515971 prefixEnd_515971 := by exact prefixLift 515971
  have htrace : WordTrace (prefixWord ++ tailWord_515971) baseStart_515971 baseEnd_515971 := by
    simpa [prefixWord, tailWord_515971, baseEnd_515971] using wordTrace_append hprefix tailTrace_515971
  have hstable : (prefixWord ++ tailWord_515971).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515971).length < 2 ^ (prefixWord ++ tailWord_515971).sum := by decide
  have hdescent : baseEnd_515971 < baseStart_515971 := by decide
  rcases family_descends (prefixWord ++ tailWord_515971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_515988 : List Nat := [2, 4, 2, 1, 1, 3, 3, 3]
def baseStart_515988 : Nat := 118140960795 + 515988 * 2 ^ 59
def prefixEnd_515988 : Nat := 4983230072969 + 3 ^ 40 * 515988 * 2
def baseEnd_515988 : Nat := 157007322045767364904901

theorem tailTrace_515988 : CollatzResearch.WordTrace tailWord_515988 prefixEnd_515988 157007322045767364904901 := by
  unfold tailWord_515988
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409814227335537289810309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12546418969780716386413745 9409814227335537289810309)
  ·
    refine ⟨1764340167625413241839433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9409814227335537289810309 1764340167625413241839433)
    ·
      refine ⟨1323255125719059931379575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1764340167625413241839433 1323255125719059931379575)
      ·
        refine ⟨1984882688578589897069363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323255125719059931379575 1984882688578589897069363)
        ·
          refine ⟨2977324032867884845604045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984882688578589897069363 2977324032867884845604045)
          ·
            refine ⟨1116496512325456817101517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2977324032867884845604045 1116496512325456817101517)
            ·
              refine ⟨418686192122046306413069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1116496512325456817101517 418686192122046306413069)
              ·
                refine ⟨157007322045767364904901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418686192122046306413069 157007322045767364904901)
                ·
                  rfl

theorem cell19_515988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_515988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_515988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_515988 prefixEnd_515988 := by exact prefixLift 515988
  have htrace : WordTrace (prefixWord ++ tailWord_515988) baseStart_515988 baseEnd_515988 := by
    simpa [prefixWord, tailWord_515988, baseEnd_515988] using wordTrace_append hprefix tailTrace_515988
  have hstable : (prefixWord ++ tailWord_515988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_515988).length < 2 ^ (prefixWord ++ tailWord_515988).sum := by decide
  have hdescent : baseEnd_515988 < baseStart_515988 := by decide
  rcases family_descends (prefixWord ++ tailWord_515988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516060 : List Nat := [2, 2, 6, 1, 2, 1, 5]
def baseStart_516060 : Nat := 118140960795 + 516060 * 2 ^ 59
def prefixEnd_516060 : Nat := 4983230072969 + 3 ^ 40 * 516060 * 2
def baseEnd_516060 : Nat := 52343076851230843768235

theorem tailTrace_516060 : CollatzResearch.WordTrace tailWord_516060 prefixEnd_516060 52343076851230843768235 := by
  unfold tailWord_516060
  simp only [CollatzResearch.WordTrace]
  refine ⟨9411127255205115438120817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12548169673606820584161089 9411127255205115438120817)
  ·
    refine ⟨7058345441403836578590613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9411127255205115438120817 7058345441403836578590613)
    ·
      refine ⟨330859942565804839621435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7058345441403836578590613 330859942565804839621435)
      ·
        refine ⟨496289913848707259432153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330859942565804839621435 496289913848707259432153)
        ·
          refine ⟨372217435386530444574115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496289913848707259432153 372217435386530444574115)
          ·
            refine ⟨558326153079795666861173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372217435386530444574115 558326153079795666861173)
            ·
              refine ⟨52343076851230843768235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 558326153079795666861173 52343076851230843768235)
              ·
                rfl

theorem cell19_516060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 5].length) (baseStart_516060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516060 prefixEnd_516060 := by exact prefixLift 516060
  have htrace : WordTrace (prefixWord ++ tailWord_516060) baseStart_516060 baseEnd_516060 := by
    simpa [prefixWord, tailWord_516060, baseEnd_516060] using wordTrace_append hprefix tailTrace_516060
  have hstable : (prefixWord ++ tailWord_516060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516060).length < 2 ^ (prefixWord ++ tailWord_516060).sum := by decide
  have hdescent : baseEnd_516060 < baseStart_516060 := by decide
  rcases family_descends (prefixWord ++ tailWord_516060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516125 : List Nat := [1, 4, 2, 2, 2, 8]
def baseStart_516125 : Nat := 118140960795 + 516125 * 2 ^ 59
def prefixEnd_516125 : Nat := 4983230072969 + 3 ^ 40 * 516125 * 2
def baseEnd_516125 : Nat := 17449889896421293317787

theorem tailTrace_516125 : CollatzResearch.WordTrace tailWord_516125 prefixEnd_516125 17449889896421293317787 := by
  unfold tailWord_516125
  simp only [CollatzResearch.WordTrace]
  refine ⟨18824625255174746977357829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12549750170116497984905219 18824625255174746977357829)
  ·
    refine ⟨3529617235345265058254593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18824625255174746977357829 3529617235345265058254593)
    ·
      refine ⟨2647212926508948793690945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3529617235345265058254593 2647212926508948793690945)
      ·
        refine ⟨1985409694881711595268209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2647212926508948793690945 1985409694881711595268209)
        ·
          refine ⟨1489057271161283696451157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1985409694881711595268209 1489057271161283696451157)
          ·
            refine ⟨17449889896421293317787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1489057271161283696451157 17449889896421293317787)
            ·
              rfl

theorem cell19_516125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 8].length) (baseStart_516125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516125 prefixEnd_516125 := by exact prefixLift 516125
  have htrace : WordTrace (prefixWord ++ tailWord_516125) baseStart_516125 baseEnd_516125 := by
    simpa [prefixWord, tailWord_516125, baseEnd_516125] using wordTrace_append hprefix tailTrace_516125
  have hstable : (prefixWord ++ tailWord_516125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516125).length < 2 ^ (prefixWord ++ tailWord_516125).sum := by decide
  have hdescent : baseEnd_516125 < baseStart_516125 := by decide
  rcases family_descends (prefixWord ++ tailWord_516125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516142 : List Nat := [4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_516142 : Nat := 118140960795 + 516142 * 2 ^ 59
def prefixEnd_516142 : Nat := 4983230072969 + 3 ^ 40 * 516142 * 2
def baseEnd_516142 : Nat := 157054181909940637482259

theorem tailTrace_516142 : CollatzResearch.WordTrace tailWord_516142 prefixEnd_516142 157054181909940637482259 := by
  unfold tailWord_516142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353155662014144860090835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12550163530742105920484453 2353155662014144860090835)
  ·
    refine ⟨3529733493021217290136253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2353155662014144860090835 3529733493021217290136253)
    ·
      refine ⟨1323650059882956483801095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3529733493021217290136253 1323650059882956483801095)
      ·
        refine ⟨1985475089824434725701643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323650059882956483801095 1985475089824434725701643)
        ·
          refine ⟨2978212634736652088552465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985475089824434725701643 2978212634736652088552465)
          ·
            refine ⟨2233659476052489066414349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2978212634736652088552465 2233659476052489066414349)
            ·
              refine ⟨837622303519683399905381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2233659476052489066414349 837622303519683399905381)
              ·
                refine ⟨157054181909940637482259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837622303519683399905381 157054181909940637482259)
                ·
                  rfl

theorem cell19_516142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_516142 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516142 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516142 prefixEnd_516142 := by exact prefixLift 516142
  have htrace : WordTrace (prefixWord ++ tailWord_516142) baseStart_516142 baseEnd_516142 := by
    simpa [prefixWord, tailWord_516142, baseEnd_516142] using wordTrace_append hprefix tailTrace_516142
  have hstable : (prefixWord ++ tailWord_516142).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516142).length < 2 ^ (prefixWord ++ tailWord_516142).sum := by decide
  have hdescent : baseEnd_516142 < baseStart_516142 := by decide
  rcases family_descends (prefixWord ++ tailWord_516142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516144 : List Nat := [2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_516144 : Nat := 118140960795 + 516144 * 2 ^ 59
def prefixEnd_516144 : Nat := 4983230072969 + 3 ^ 40 * 516144 * 2
def baseEnd_516144 : Nat := 157054790479605225437809

theorem tailTrace_516144 : CollatzResearch.WordTrace tailWord_516144 prefixEnd_516144 157054790479605225437809 := by
  unfold tailWord_516144
  simp only [CollatzResearch.WordTrace]
  refine ⟨9412659121052956611149743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12550212161403942148199657 9412659121052956611149743)
  ·
    refine ⟨14118988681579434916724615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9412659121052956611149743 14118988681579434916724615)
    ·
      refine ⟨21178483022369152375086923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14118988681579434916724615 21178483022369152375086923)
      ·
        refine ⟨31767724533553728562630385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21178483022369152375086923 31767724533553728562630385)
        ·
          refine ⟨23825793400165296421972789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31767724533553728562630385 23825793400165296421972789)
          ·
            refine ⟨2233668131265496539559949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23825793400165296421972789 2233668131265496539559949)
            ·
              refine ⟨837625549224561202334981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2233668131265496539559949 837625549224561202334981)
              ·
                refine ⟨157054790479605225437809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837625549224561202334981 157054790479605225437809)
                ·
                  rfl

theorem cell19_516144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_516144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516144 prefixEnd_516144 := by exact prefixLift 516144
  have htrace : WordTrace (prefixWord ++ tailWord_516144) baseStart_516144 baseEnd_516144 := by
    simpa [prefixWord, tailWord_516144, baseEnd_516144] using wordTrace_append hprefix tailTrace_516144
  have hstable : (prefixWord ++ tailWord_516144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516144).length < 2 ^ (prefixWord ++ tailWord_516144).sum := by decide
  have hdescent : baseEnd_516144 < baseStart_516144 := by decide
  rcases family_descends (prefixWord ++ tailWord_516144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516220 : List Nat := [2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_516220 : Nat := 118140960795 + 516220 * 2 ^ 59
def prefixEnd_516220 : Nat := 4983230072969 + 3 ^ 40 * 516220 * 2
def baseEnd_516220 : Nat := 157077916126859567748713

theorem tailTrace_516220 : CollatzResearch.WordTrace tailWord_516220 prefixEnd_516220 157077916126859567748713 := by
  unfold tailWord_516220
  simp only [CollatzResearch.WordTrace]
  refine ⟨9414045094915289101033057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12552060126553718801377409 9414045094915289101033057)
  ·
    refine ⟨7060533821186466825774793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9414045094915289101033057 7060533821186466825774793)
    ·
      refine ⟨5295400365889850119331095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7060533821186466825774793 5295400365889850119331095)
      ·
        refine ⟨7943100548834775178996643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295400365889850119331095 7943100548834775178996643)
        ·
          refine ⟨11914650823252162768494965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7943100548834775178996643 11914650823252162768494965)
          ·
            refine ⟨1116998514679890259546403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11914650823252162768494965 1116998514679890259546403)
            ·
              refine ⟨1675497772019835389319605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116998514679890259546403 1675497772019835389319605)
              ·
                refine ⟨157077916126859567748713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1675497772019835389319605 157077916126859567748713)
                ·
                  rfl

theorem cell19_516220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_516220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516220 prefixEnd_516220 := by exact prefixLift 516220
  have htrace : WordTrace (prefixWord ++ tailWord_516220) baseStart_516220 baseEnd_516220 := by
    simpa [prefixWord, tailWord_516220, baseEnd_516220] using wordTrace_append hprefix tailTrace_516220
  have hstable : (prefixWord ++ tailWord_516220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516220).length < 2 ^ (prefixWord ++ tailWord_516220).sum := by decide
  have hdescent : baseEnd_516220 < baseStart_516220 := by decide
  rcases family_descends (prefixWord ++ tailWord_516220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516254 : List Nat := [4, 3, 1, 1, 3, 1, 2, 4]
def baseStart_516254 : Nat := 118140960795 + 516254 * 2 ^ 59
def prefixEnd_516254 : Nat := 4983230072969 + 3 ^ 40 * 516254 * 2
def baseEnd_516254 : Nat := 157088261811157562993065

theorem tailTrace_516254 : CollatzResearch.WordTrace tailWord_516254 prefixEnd_516254 157088261811157562993065 := by
  unfold tailWord_516254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353666283963425251100477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12552886847804934672535877 2353666283963425251100477)
  ·
    refine ⟨882624856486284469162679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2353666283963425251100477 882624856486284469162679)
    ·
      refine ⟨1323937284729426703744019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 882624856486284469162679 1323937284729426703744019)
      ·
        refine ⟨1985905927094140055616029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323937284729426703744019 1985905927094140055616029)
        ·
          refine ⟨744714722660302520856011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1985905927094140055616029 744714722660302520856011)
          ·
            refine ⟨1117072083990453781284017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744714722660302520856011 1117072083990453781284017)
            ·
              refine ⟨837804062992840335963013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117072083990453781284017 837804062992840335963013)
              ·
                refine ⟨157088261811157562993065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837804062992840335963013 157088261811157562993065)
                ·
                  rfl

theorem cell19_516254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_516254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516254 prefixEnd_516254 := by exact prefixLift 516254
  have htrace : WordTrace (prefixWord ++ tailWord_516254) baseStart_516254 baseEnd_516254 := by
    simpa [prefixWord, tailWord_516254, baseEnd_516254] using wordTrace_append hprefix tailTrace_516254
  have hstable : (prefixWord ++ tailWord_516254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516254).length < 2 ^ (prefixWord ++ tailWord_516254).sum := by decide
  have hdescent : baseEnd_516254 < baseStart_516254 := by decide
  rcases family_descends (prefixWord ++ tailWord_516254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516294 : List Nat := [6, 1, 2, 10]
def baseStart_516294 : Nat := 118140960795 + 516294 * 2 ^ 59
def prefixEnd_516294 : Nat := 4983230072969 + 3 ^ 40 * 516294 * 2
def baseEnd_516294 : Nat := 1939511521042584223507

theorem tailTrace_516294 : CollatzResearch.WordTrace tailWord_516294 prefixEnd_516294 1939511521042584223507 := by
  unfold tailWord_516294
  simp only [CollatzResearch.WordTrace]
  refine ⟨588462162236327776258123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12553859461041659226839957 588462162236327776258123)
  ·
    refine ⟨882693243354491664387185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 588462162236327776258123 882693243354491664387185)
    ·
      refine ⟨662019932515868748290389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 882693243354491664387185 662019932515868748290389)
      ·
        refine ⟨1939511521042584223507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 662019932515868748290389 1939511521042584223507)
        ·
          rfl

theorem cell19_516294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 10].length) (baseStart_516294 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516294 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516294 prefixEnd_516294 := by exact prefixLift 516294
  have htrace : WordTrace (prefixWord ++ tailWord_516294) baseStart_516294 baseEnd_516294 := by
    simpa [prefixWord, tailWord_516294, baseEnd_516294] using wordTrace_append hprefix tailTrace_516294
  have hstable : (prefixWord ++ tailWord_516294).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516294).length < 2 ^ (prefixWord ++ tailWord_516294).sum := by decide
  have hdescent : baseEnd_516294 < baseStart_516294 := by decide
  rcases family_descends (prefixWord ++ tailWord_516294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516336 : List Nat := [2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_516336 : Nat := 118140960795 + 516336 * 2 ^ 59
def prefixEnd_516336 : Nat := 4983230072969 + 3 ^ 40 * 516336 * 2
def baseEnd_516336 : Nat := 157113213167405669170619

theorem tailTrace_516336 : CollatzResearch.WordTrace tailWord_516336 prefixEnd_516336 157113213167405669170619 := by
  unfold tailWord_516336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9416160528705165006644431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12554880704940220008859241 9416160528705165006644431)
  ·
    refine ⟨14124240793057747509966647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9416160528705165006644431 14124240793057747509966647)
    ·
      refine ⟨21186361189586621264949971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14124240793057747509966647 21186361189586621264949971)
      ·
        refine ⟨31779541784379931897424957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21186361189586621264949971 31779541784379931897424957)
        ·
          refine ⟨11917328169142474461534359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31779541784379931897424957 11917328169142474461534359)
          ·
            refine ⟨17875992253713711692301539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11917328169142474461534359 17875992253713711692301539)
            ·
              refine ⟨26813988380570567538452309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17875992253713711692301539 26813988380570567538452309)
              ·
                refine ⟨157113213167405669170619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26813988380570567538452309 157113213167405669170619)
                ·
                  rfl

theorem cell19_516336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_516336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516336 prefixEnd_516336 := by exact prefixLift 516336
  have htrace : WordTrace (prefixWord ++ tailWord_516336) baseStart_516336 baseEnd_516336 := by
    simpa [prefixWord, tailWord_516336, baseEnd_516336] using wordTrace_append hprefix tailTrace_516336
  have hstable : (prefixWord ++ tailWord_516336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516336).length < 2 ^ (prefixWord ++ tailWord_516336).sum := by decide
  have hdescent : baseEnd_516336 < baseStart_516336 := by decide
  rcases family_descends (prefixWord ++ tailWord_516336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516355 : List Nat := [1, 1, 1, 3, 2, 3, 8]
def baseStart_516355 : Nat := 118140960795 + 516355 * 2 ^ 59
def prefixEnd_516355 : Nat := 4983230072969 + 3 ^ 40 * 516355 * 2
def baseEnd_516355 : Nat := 52372998193073084916115

theorem tailTrace_516355 : CollatzResearch.WordTrace tailWord_516355 prefixEnd_516355 52372998193073084916115 := by
  unfold tailWord_516355
  simp only [CollatzResearch.WordTrace]
  refine ⟨18833014044341496258230519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12555342696227664172153679 18833014044341496258230519)
  ·
    refine ⟨28249521066512244387345779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18833014044341496258230519 28249521066512244387345779)
    ·
      refine ⟨42374281599768366581018669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28249521066512244387345779 42374281599768366581018669)
      ·
        refine ⟨15890355599913137467882001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42374281599768366581018669 15890355599913137467882001)
        ·
          refine ⟨11917766699934853100911501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15890355599913137467882001 11917766699934853100911501)
          ·
            refine ⟨4469162512475569912841813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11917766699934853100911501 4469162512475569912841813)
            ·
              refine ⟨52372998193073084916115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4469162512475569912841813 52372998193073084916115)
              ·
                rfl

theorem cell19_516355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_516355 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516355 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516355 prefixEnd_516355 := by exact prefixLift 516355
  have htrace : WordTrace (prefixWord ++ tailWord_516355) baseStart_516355 baseEnd_516355 := by
    simpa [prefixWord, tailWord_516355, baseEnd_516355] using wordTrace_append hprefix tailTrace_516355
  have hstable : (prefixWord ++ tailWord_516355).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516355).length < 2 ^ (prefixWord ++ tailWord_516355).sum := by decide
  have hdescent : baseEnd_516355 < baseStart_516355 := by decide
  rcases family_descends (prefixWord ++ tailWord_516355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516410 : List Nat := [3, 1, 1, 1, 4, 4, 5]
def baseStart_516410 : Nat := 118140960795 + 516410 * 2 ^ 59
def prefixEnd_516410 : Nat := 4983230072969 + 3 ^ 40 * 516410 * 2
def baseEnd_516410 : Nat := 52378576748331807841991

theorem tailTrace_516410 : CollatzResearch.WordTrace tailWord_516410 prefixEnd_516410 52378576748331807841991 := by
  unfold tailWord_516410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4708755014785560162870671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12556680039428160434321789 4708755014785560162870671)
  ·
    refine ⟨7063132522178340244306007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4708755014785560162870671 7063132522178340244306007)
    ·
      refine ⟨10594698783267510366459011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7063132522178340244306007 10594698783267510366459011)
      ·
        refine ⟨15892048174901265549688517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10594698783267510366459011 15892048174901265549688517)
        ·
          refine ⟨2979759032793987290566597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15892048174901265549688517 2979759032793987290566597)
          ·
            refine ⟨558704818648872616981237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2979759032793987290566597 558704818648872616981237)
            ·
              refine ⟨52378576748331807841991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 558704818648872616981237 52378576748331807841991)
              ·
                rfl

theorem cell19_516410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_516410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516410 prefixEnd_516410 := by exact prefixLift 516410
  have htrace : WordTrace (prefixWord ++ tailWord_516410) baseStart_516410 baseEnd_516410 := by
    simpa [prefixWord, tailWord_516410, baseEnd_516410] using wordTrace_append hprefix tailTrace_516410
  have hstable : (prefixWord ++ tailWord_516410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516410).length < 2 ^ (prefixWord ++ tailWord_516410).sum := by decide
  have hdescent : baseEnd_516410 < baseStart_516410 := by decide
  rcases family_descends (prefixWord ++ tailWord_516410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516505 : List Nat := [1, 2, 1, 2, 1, 4, 5, 3]
def baseStart_516505 : Nat := 118140960795 + 516505 * 2 ^ 59
def prefixEnd_516505 : Nat := 4983230072969 + 3 ^ 40 * 516505 * 2
def baseEnd_516505 : Nat := 157164637304063351414603

theorem tailTrace_516505 : CollatzResearch.WordTrace tailWord_516505 prefixEnd_516505 157164637304063351414603 := by
  unfold tailWord_516505
  simp only [CollatzResearch.WordTrace]
  refine ⟨18838484993798071876190969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12558989995865381250793979 18838484993798071876190969)
  ·
    refine ⟨14128863745348553907143227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18838484993798071876190969 14128863745348553907143227)
    ·
      refine ⟨21193295618022830860714841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14128863745348553907143227 21193295618022830860714841)
      ·
        refine ⟨15894971713517123145536131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21193295618022830860714841 15894971713517123145536131)
        ·
          refine ⟨23842457570275684718304197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15894971713517123145536131 23842457570275684718304197)
          ·
            refine ⟨4470460794426690884682037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23842457570275684718304197 4470460794426690884682037)
            ·
              refine ⟨419105699477502270438941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4470460794426690884682037 419105699477502270438941)
              ·
                refine ⟨157164637304063351414603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419105699477502270438941 157164637304063351414603)
                ·
                  rfl

theorem cell19_516505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 3].length) (baseStart_516505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516505 prefixEnd_516505 := by exact prefixLift 516505
  have htrace : WordTrace (prefixWord ++ tailWord_516505) baseStart_516505 baseEnd_516505 := by
    simpa [prefixWord, tailWord_516505, baseEnd_516505] using wordTrace_append hprefix tailTrace_516505
  have hstable : (prefixWord ++ tailWord_516505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516505).length < 2 ^ (prefixWord ++ tailWord_516505).sum := by decide
  have hdescent : baseEnd_516505 < baseStart_516505 := by decide
  rcases family_descends (prefixWord ++ tailWord_516505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516579 : List Nat := [1, 1, 1, 6, 4, 1, 5]
def baseStart_516579 : Nat := 118140960795 + 516579 * 2 ^ 59
def prefixEnd_516579 : Nat := 4983230072969 + 3 ^ 40 * 516579 * 2
def baseEnd_516579 : Nat := 52395718127217701923319

theorem tailTrace_516579 : CollatzResearch.WordTrace tailWord_516579 prefixEnd_516579 52395718127217701923319 := by
  unfold tailWord_516579
  simp only [CollatzResearch.WordTrace]
  refine ⟨18841183995529982514384791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12560789330353321676256527 18841183995529982514384791)
  ·
    refine ⟨28261775993294973771577187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18841183995529982514384791 28261775993294973771577187)
    ·
      refine ⟨42392663989942460657365781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28261775993294973771577187 42392663989942460657365781)
      ·
        refine ⟨1987156124528552843314021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42392663989942460657365781 1987156124528552843314021)
        ·
          refine ⟨372591773349103658121379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1987156124528552843314021 372591773349103658121379)
          ·
            refine ⟨558887660023655487182069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372591773349103658121379 558887660023655487182069)
            ·
              refine ⟨52395718127217701923319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 558887660023655487182069 52395718127217701923319)
              ·
                rfl

theorem cell19_516579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 5].length) (baseStart_516579 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516579 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516579 prefixEnd_516579 := by exact prefixLift 516579
  have htrace : WordTrace (prefixWord ++ tailWord_516579) baseStart_516579 baseEnd_516579 := by
    simpa [prefixWord, tailWord_516579, baseEnd_516579] using wordTrace_append hprefix tailTrace_516579
  have hstable : (prefixWord ++ tailWord_516579).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516579).length < 2 ^ (prefixWord ++ tailWord_516579).sum := by decide
  have hdescent : baseEnd_516579 < baseStart_516579 := by decide
  rcases family_descends (prefixWord ++ tailWord_516579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516640 : List Nat := [2, 1, 1, 6, 9]
def baseStart_516640 : Nat := 118140960795 + 516640 * 2 ^ 59
def prefixEnd_516640 : Nat := 4983230072969 + 3 ^ 40 * 516640 * 2
def baseEnd_516640 : Nat := 5822433916904556978305

theorem tailTrace_516640 : CollatzResearch.WordTrace tailWord_516640 prefixEnd_516640 5822433916904556978305 := by
  unfold tailWord_516640
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421704424154494966177687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12562272565539326621570249 9421704424154494966177687)
  ·
    refine ⟨14132556636231742449266531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9421704424154494966177687 14132556636231742449266531)
    ·
      refine ⟨21198834954347613673899797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14132556636231742449266531 21198834954347613673899797)
      ·
        refine ⟨993695388485044390964053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21198834954347613673899797 993695388485044390964053)
        ·
          refine ⟨5822433916904556978305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 993695388485044390964053 5822433916904556978305)
          ·
            rfl

theorem cell19_516640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 9].length) (baseStart_516640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516640 prefixEnd_516640 := by exact prefixLift 516640
  have htrace : WordTrace (prefixWord ++ tailWord_516640) baseStart_516640 baseEnd_516640 := by
    simpa [prefixWord, tailWord_516640, baseEnd_516640] using wordTrace_append hprefix tailTrace_516640
  have hstable : (prefixWord ++ tailWord_516640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516640).length < 2 ^ (prefixWord ++ tailWord_516640).sum := by decide
  have hdescent : baseEnd_516640 < baseStart_516640 := by decide
  rcases family_descends (prefixWord ++ tailWord_516640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516733 : List Nat := [1, 4, 1, 1, 5, 1, 1, 5]
def baseStart_516733 : Nat := 118140960795 + 516733 * 2 ^ 59
def prefixEnd_516733 : Nat := 4983230072969 + 3 ^ 40 * 516733 * 2
def baseEnd_516733 : Nat := 157234014245826378347315

theorem tailTrace_516733 : CollatzResearch.WordTrace tailWord_516733 prefixEnd_516733 157234014245826378347315 := by
  unfold tailWord_516733
  simp only [CollatzResearch.WordTrace]
  refine ⟨18846800836972066815490853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12564533891314711210327235 18846800836972066815490853)
  ·
    refine ⟨3533775156932262527904535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18846800836972066815490853 3533775156932262527904535)
    ·
      refine ⟨5300662735398393791856803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3533775156932262527904535 5300662735398393791856803)
      ·
        refine ⟨7950994103097590687785205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5300662735398393791856803 7950994103097590687785205)
        ·
          refine ⟨745405697165399126979863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7950994103097590687785205 745405697165399126979863)
          ·
            refine ⟨1118108545748098690469795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745405697165399126979863 1118108545748098690469795)
            ·
              refine ⟨1677162818622148035704693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118108545748098690469795 1677162818622148035704693)
              ·
                refine ⟨157234014245826378347315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1677162818622148035704693 157234014245826378347315)
                ·
                  rfl

theorem cell19_516733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_516733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516733 prefixEnd_516733 := by exact prefixLift 516733
  have htrace : WordTrace (prefixWord ++ tailWord_516733) baseStart_516733 baseEnd_516733 := by
    simpa [prefixWord, tailWord_516733, baseEnd_516733] using wordTrace_append hprefix tailTrace_516733
  have hstable : (prefixWord ++ tailWord_516733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516733).length < 2 ^ (prefixWord ++ tailWord_516733).sum := by decide
  have hdescent : baseEnd_516733 < baseStart_516733 := by decide
  rcases family_descends (prefixWord ++ tailWord_516733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516847 : List Nat := [1, 1, 2, 1, 5, 3, 3, 3]
def baseStart_516847 : Nat := 118140960795 + 516847 * 2 ^ 59
def prefixEnd_516847 : Nat := 4983230072969 + 3 ^ 40 * 516847 * 2
def baseEnd_516847 : Nat := 157268702716707891813671

theorem tailTrace_516847 : CollatzResearch.WordTrace tailWord_516847 prefixEnd_516847 157268702716707891813671 := by
  unfold tailWord_516847
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850958758559064285140795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12567305839039376190093863 18850958758559064285140795)
  ·
    refine ⟨28276438137838596427711193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18850958758559064285140795 28276438137838596427711193)
    ·
      refine ⟨21207328603378947320783395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28276438137838596427711193 21207328603378947320783395)
      ·
        refine ⟨31810992905068420981175093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21207328603378947320783395 31810992905068420981175093)
        ·
          refine ⟨2982280584850164466985165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31810992905068420981175093 2982280584850164466985165)
          ·
            refine ⟨1118355219318811675119437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2982280584850164466985165 1118355219318811675119437)
            ·
              refine ⟨419383207244554378169789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1118355219318811675119437 419383207244554378169789)
              ·
                refine ⟨157268702716707891813671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419383207244554378169789 157268702716707891813671)
                ·
                  rfl

theorem cell19_516847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 3].length) (baseStart_516847 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516847 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516847 prefixEnd_516847 := by exact prefixLift 516847
  have htrace : WordTrace (prefixWord ++ tailWord_516847) baseStart_516847 baseEnd_516847 := by
    simpa [prefixWord, tailWord_516847, baseEnd_516847] using wordTrace_append hprefix tailTrace_516847
  have hstable : (prefixWord ++ tailWord_516847).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516847).length < 2 ^ (prefixWord ++ tailWord_516847).sum := by decide
  have hdescent : baseEnd_516847 < baseStart_516847 := by decide
  rcases family_descends (prefixWord ++ tailWord_516847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516866 : List Nat := [3, 4, 1, 1, 1, 3, 6]
def baseStart_516866 : Nat := 118140960795 + 516866 * 2 ^ 59
def prefixEnd_516866 : Nat := 4983230072969 + 3 ^ 40 * 516866 * 2
def baseEnd_516866 : Nat := 52424828042840492463799

theorem tailTrace_516866 : CollatzResearch.WordTrace tailWord_516866 prefixEnd_516866 52424828042840492463799 := by
  unfold tailWord_516866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712912936372557632520613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12567767830326820353388301 4712912936372557632520613)
  ·
    refine ⟨883671175569854556097615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4712912936372557632520613 883671175569854556097615)
    ·
      refine ⟨1325506763354781834146423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 883671175569854556097615 1325506763354781834146423)
      ·
        refine ⟨1988260145032172751219635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1325506763354781834146423 1988260145032172751219635)
        ·
          refine ⟨2982390217548259126829453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988260145032172751219635 2982390217548259126829453)
          ·
            refine ⟨1118396331580597172561045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2982390217548259126829453 1118396331580597172561045)
            ·
              refine ⟨52424828042840492463799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1118396331580597172561045 52424828042840492463799)
              ·
                rfl

theorem cell19_516866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_516866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516866 prefixEnd_516866 := by exact prefixLift 516866
  have htrace : WordTrace (prefixWord ++ tailWord_516866) baseStart_516866 baseEnd_516866 := by
    simpa [prefixWord, tailWord_516866, baseEnd_516866] using wordTrace_append hprefix tailTrace_516866
  have hstable : (prefixWord ++ tailWord_516866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516866).length < 2 ^ (prefixWord ++ tailWord_516866).sum := by decide
  have hdescent : baseEnd_516866 < baseStart_516866 := by decide
  rcases family_descends (prefixWord ++ tailWord_516866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516868 : List Nat := [2, 3, 2, 2, 1, 1, 8]
def baseStart_516868 : Nat := 118140960795 + 516868 * 2 ^ 59
def prefixEnd_516868 : Nat := 4983230072969 + 3 ^ 40 * 516868 * 2
def baseEnd_516868 : Nat := 52425030899395355115649

theorem tailTrace_516868 : CollatzResearch.WordTrace tailWord_516868 prefixEnd_516868 52425030899395355115649 := by
  unfold tailWord_516868
  simp only [CollatzResearch.WordTrace]
  refine ⟨9425862345741492435827629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12567816460988656581103505 9425862345741492435827629)
  ·
    refine ⟨3534698379653059663435361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9425862345741492435827629 3534698379653059663435361)
    ·
      refine ⟨2651023784739794747576521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3534698379653059663435361 2651023784739794747576521)
      ·
        refine ⟨1988267838554846060682391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2651023784739794747576521 1988267838554846060682391)
        ·
          refine ⟨2982401757832269091023587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988267838554846060682391 2982401757832269091023587)
          ·
            refine ⟨4473602636748403636535381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982401757832269091023587 4473602636748403636535381)
            ·
              refine ⟨52425030899395355115649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4473602636748403636535381 52425030899395355115649)
              ·
                rfl

theorem cell19_516868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_516868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516868 prefixEnd_516868 := by exact prefixLift 516868
  have htrace : WordTrace (prefixWord ++ tailWord_516868) baseStart_516868 baseEnd_516868 := by
    simpa [prefixWord, tailWord_516868, baseEnd_516868] using wordTrace_append hprefix tailTrace_516868
  have hstable : (prefixWord ++ tailWord_516868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516868).length < 2 ^ (prefixWord ++ tailWord_516868).sum := by decide
  have hdescent : baseEnd_516868 < baseStart_516868 := by decide
  rcases family_descends (prefixWord ++ tailWord_516868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516900 : List Nat := [2, 3, 1, 3, 4, 1, 2, 3]
def baseStart_516900 : Nat := 118140960795 + 516900 * 2 ^ 59
def prefixEnd_516900 : Nat := 4983230072969 + 3 ^ 40 * 516900 * 2
def baseEnd_516900 : Nat := 157284829812819472635749

theorem tailTrace_516900 : CollatzResearch.WordTrace tailWord_516900 prefixEnd_516900 157284829812819472635749 := by
  unfold tailWord_516900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9426445913683527168410077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12568594551578036224546769 9426445913683527168410077)
  ·
    refine ⟨3534917217631322688153779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9426445913683527168410077 3534917217631322688153779)
    ·
      refine ⟨5302375826446984032230669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3534917217631322688153779 5302375826446984032230669)
      ·
        refine ⟨1988390934917619012086501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5302375826446984032230669 1988390934917619012086501)
        ·
          refine ⟨372823300297053564766219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1988390934917619012086501 372823300297053564766219)
          ·
            refine ⟨559234950445580347149329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372823300297053564766219 559234950445580347149329)
            ·
              refine ⟨419426212834185260361997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559234950445580347149329 419426212834185260361997)
              ·
                refine ⟨157284829812819472635749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419426212834185260361997 157284829812819472635749)
                ·
                  rfl

theorem cell19_516900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_516900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516900 prefixEnd_516900 := by exact prefixLift 516900
  have htrace : WordTrace (prefixWord ++ tailWord_516900) baseStart_516900 baseEnd_516900 := by
    simpa [prefixWord, tailWord_516900, baseEnd_516900] using wordTrace_append hprefix tailTrace_516900
  have hstable : (prefixWord ++ tailWord_516900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516900).length < 2 ^ (prefixWord ++ tailWord_516900).sum := by decide
  have hdescent : baseEnd_516900 < baseStart_516900 := by decide
  rcases family_descends (prefixWord ++ tailWord_516900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516963 : List Nat := [1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_516963 : Nat := 118140960795 + 516963 * 2 ^ 59
def prefixEnd_516963 : Nat := 4983230072969 + 3 ^ 40 * 516963 * 2
def baseEnd_516963 : Nat := 157303999757253993235577

theorem tailTrace_516963 : CollatzResearch.WordTrace tailWord_516963 prefixEnd_516963 157303999757253993235577 := by
  unfold tailWord_516963
  simp only [CollatzResearch.WordTrace]
  refine ⟨18855189626138816096363543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12570126417425877397575695 18855189626138816096363543)
  ·
    refine ⟨28282784439208224144545315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18855189626138816096363543 28282784439208224144545315)
    ·
      refine ⟨42424176658812336216817973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28282784439208224144545315 42424176658812336216817973)
      ·
        refine ⟨3977266561763656520326685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42424176658812336216817973 3977266561763656520326685)
        ·
          refine ⟨1491474960661371195122507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3977266561763656520326685 1491474960661371195122507)
          ·
            refine ⟨2237212440992056792683761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491474960661371195122507 2237212440992056792683761)
            ·
              refine ⟨1677909330744042594512821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237212440992056792683761 1677909330744042594512821)
              ·
                refine ⟨157303999757253993235577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1677909330744042594512821 157303999757253993235577)
                ·
                  rfl

theorem cell19_516963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_516963 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516963 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516963 prefixEnd_516963 := by exact prefixLift 516963
  have htrace : WordTrace (prefixWord ++ tailWord_516963) baseStart_516963 baseEnd_516963 := by
    simpa [prefixWord, tailWord_516963, baseEnd_516963] using wordTrace_append hprefix tailTrace_516963
  have hstable : (prefixWord ++ tailWord_516963).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516963).length < 2 ^ (prefixWord ++ tailWord_516963).sum := by decide
  have hdescent : baseEnd_516963 < baseStart_516963 := by decide
  rcases family_descends (prefixWord ++ tailWord_516963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_516999 : List Nat := [1, 1, 4, 2, 3, 3, 1, 4]
def baseStart_516999 : Nat := 118140960795 + 516999 * 2 ^ 59
def prefixEnd_516999 : Nat := 4983230072969 + 3 ^ 40 * 516999 * 2
def baseEnd_516999 : Nat := 157314954011216576435479

theorem tailTrace_516999 : CollatzResearch.WordTrace tailWord_516999 prefixEnd_516999 157314954011216576435479 := by
  unfold tailWord_516999
  simp only [CollatzResearch.WordTrace]
  refine ⟨18856502654008394244674051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12571001769338929496449367 18856502654008394244674051)
  ·
    refine ⟨28284753981012591367011077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18856502654008394244674051 28284753981012591367011077)
    ·
      refine ⟨5303391371439860881314577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28284753981012591367011077 5303391371439860881314577)
      ·
        refine ⟨3977543528579895660985933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5303391371439860881314577 3977543528579895660985933)
        ·
          refine ⟨1491578823217460872869725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3977543528579895660985933 1491578823217460872869725)
          ·
            refine ⟨559342058706547827326147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1491578823217460872869725 559342058706547827326147)
            ·
              refine ⟨839013088059821740989221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559342058706547827326147 839013088059821740989221)
              ·
                refine ⟨157314954011216576435479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 839013088059821740989221 157314954011216576435479)
                ·
                  rfl

theorem cell19_516999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_516999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_516999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_516999 prefixEnd_516999 := by exact prefixLift 516999
  have htrace : WordTrace (prefixWord ++ tailWord_516999) baseStart_516999 baseEnd_516999 := by
    simpa [prefixWord, tailWord_516999, baseEnd_516999] using wordTrace_append hprefix tailTrace_516999
  have hstable : (prefixWord ++ tailWord_516999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_516999).length < 2 ^ (prefixWord ++ tailWord_516999).sum := by decide
  have hdescent : baseEnd_516999 < baseStart_516999 := by decide
  rcases family_descends (prefixWord ++ tailWord_516999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517001 : List Nat := [1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_517001 : Nat := 118140960795 + 517001 * 2 ^ 59
def prefixEnd_517001 : Nat := 4983230072969 + 3 ^ 40 * 517001 * 2
def baseEnd_517001 : Nat := 157315562580881164391029

theorem tailTrace_517001 : CollatzResearch.WordTrace tailWord_517001 prefixEnd_517001 157315562580881164391029 := by
  unfold tailWord_517001
  simp only [CollatzResearch.WordTrace]
  refine ⟨18856575600001148586246857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12571050400000765724164571 18856575600001148586246857)
  ·
    refine ⟨14142431700000861439685143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18856575600001148586246857 14142431700000861439685143)
    ·
      refine ⟨21213647550001292159527715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14142431700000861439685143 21213647550001292159527715)
      ·
        refine ⟨31820471325001938239291573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21213647550001292159527715 31820471325001938239291573)
        ·
          refine ⟨2983169186718931709933585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31820471325001938239291573 2983169186718931709933585)
          ·
            refine ⟨2237376890039198782450189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2983169186718931709933585 2237376890039198782450189)
            ·
              refine ⟨839016333764699543418821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2237376890039198782450189 839016333764699543418821)
              ·
                refine ⟨157315562580881164391029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 839016333764699543418821 157315562580881164391029)
                ·
                  rfl

theorem cell19_517001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_517001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517001 prefixEnd_517001 := by exact prefixLift 517001
  have htrace : WordTrace (prefixWord ++ tailWord_517001) baseStart_517001 baseEnd_517001 := by
    simpa [prefixWord, tailWord_517001, baseEnd_517001] using wordTrace_append hprefix tailTrace_517001
  have hstable : (prefixWord ++ tailWord_517001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517001).length < 2 ^ (prefixWord ++ tailWord_517001).sum := by decide
  have hdescent : baseEnd_517001 < baseStart_517001 := by decide
  rcases family_descends (prefixWord ++ tailWord_517001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517134 : List Nat := [4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_517134 : Nat := 118140960795 + 517134 * 2 ^ 59
def prefixEnd_517134 : Nat := 4983230072969 + 3 ^ 40 * 517134 * 2
def baseEnd_517134 : Nat := 157356032463576263435111

theorem tailTrace_517134 : CollatzResearch.WordTrace tailWord_517134 prefixEnd_517134 157356032463576263435111 := by
  unfold tailWord_517134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2357678313564914037604807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12574284339012874867225637 2357678313564914037604807)
  ·
    refine ⟨3536517470347371056407211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2357678313564914037604807 3536517470347371056407211)
    ·
      refine ⟨5304776205521056584610817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3536517470347371056407211 5304776205521056584610817)
      ·
        refine ⟨3978582154140792438458113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5304776205521056584610817 3978582154140792438458113)
        ·
          refine ⟨2983936615605594328843585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3978582154140792438458113 2983936615605594328843585)
          ·
            refine ⟨2237952461704195746632689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2983936615605594328843585 2237952461704195746632689)
            ·
              refine ⟨1678464346278146809974517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237952461704195746632689 1678464346278146809974517)
              ·
                refine ⟨157356032463576263435111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1678464346278146809974517 157356032463576263435111)
                ·
                  rfl

theorem cell19_517134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_517134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517134 prefixEnd_517134 := by exact prefixLift 517134
  have htrace : WordTrace (prefixWord ++ tailWord_517134) baseStart_517134 baseEnd_517134 := by
    simpa [prefixWord, tailWord_517134, baseEnd_517134] using wordTrace_append hprefix tailTrace_517134
  have hstable : (prefixWord ++ tailWord_517134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517134).length < 2 ^ (prefixWord ++ tailWord_517134).sum := by decide
  have hdescent : baseEnd_517134 < baseStart_517134 := by decide
  rcases family_descends (prefixWord ++ tailWord_517134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517155 : List Nat := [1, 1, 1, 4, 3, 9]
def baseStart_517155 : Nat := 118140960795 + 517155 * 2 ^ 59
def prefixEnd_517155 : Nat := 4983230072969 + 3 ^ 40 * 517155 * 2
def baseEnd_517155 : Nat := 17484713605006048552043

theorem tailTrace_517155 : CollatzResearch.WordTrace tailWord_517155 prefixEnd_517155 17484713605006048552043 := by
  unfold tailWord_517155
  simp only [CollatzResearch.WordTrace]
  refine ⟨18862192441443232887352919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12574794960962155258235279 18862192441443232887352919)
  ·
    refine ⟨28293288662164849331029379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18862192441443232887352919 28293288662164849331029379)
    ·
      refine ⟨42439932993247273996544069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28293288662164849331029379 42439932993247273996544069)
      ·
        refine ⟨7957487436233863874352013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42439932993247273996544069 7957487436233863874352013)
        ·
          refine ⟨2984057788587698952882005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7957487436233863874352013 2984057788587698952882005)
          ·
            refine ⟨17484713605006048552043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2984057788587698952882005 17484713605006048552043)
            ·
              rfl

theorem cell19_517155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 9].length) (baseStart_517155 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517155 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517155 prefixEnd_517155 := by exact prefixLift 517155
  have htrace : WordTrace (prefixWord ++ tailWord_517155) baseStart_517155 baseEnd_517155 := by
    simpa [prefixWord, tailWord_517155, baseEnd_517155] using wordTrace_append hprefix tailTrace_517155
  have hstable : (prefixWord ++ tailWord_517155).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517155).length < 2 ^ (prefixWord ++ tailWord_517155).sum := by decide
  have hdescent : baseEnd_517155 < baseStart_517155 := by decide
  rcases family_descends (prefixWord ++ tailWord_517155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517206 : List Nat := [5, 2, 2, 1, 2, 1, 6]
def baseStart_517206 : Nat := 118140960795 + 517206 * 2 ^ 59
def prefixEnd_517206 : Nat := 4983230072969 + 3 ^ 40 * 517206 * 2
def baseEnd_517206 : Nat := 52459313657167143278305

theorem tailTrace_517206 : CollatzResearch.WordTrace tailWord_517206 prefixEnd_517206 52459313657167143278305 := by
  unfold tailWord_517206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179003285266154287341217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12576035042838979064972981 1179003285266154287341217)
  ·
    refine ⟨884252463949615715505913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1179003285266154287341217 884252463949615715505913)
    ·
      refine ⟨663189347962211786629435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 884252463949615715505913 663189347962211786629435)
      ·
        refine ⟨994784021943317679944153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663189347962211786629435 994784021943317679944153)
        ·
          refine ⟨746088016457488259958115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994784021943317679944153 746088016457488259958115)
          ·
            refine ⟨1119132024686232389937173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746088016457488259958115 1119132024686232389937173)
            ·
              refine ⟨52459313657167143278305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1119132024686232389937173 52459313657167143278305)
              ·
                rfl

theorem cell19_517206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_517206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517206 prefixEnd_517206 := by exact prefixLift 517206
  have htrace : WordTrace (prefixWord ++ tailWord_517206) baseStart_517206 baseEnd_517206 := by
    simpa [prefixWord, tailWord_517206, baseEnd_517206] using wordTrace_append hprefix tailTrace_517206
  have hstable : (prefixWord ++ tailWord_517206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517206).length < 2 ^ (prefixWord ++ tailWord_517206).sum := by decide
  have hdescent : baseEnd_517206 < baseStart_517206 := by decide
  rcases family_descends (prefixWord ++ tailWord_517206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517231 : List Nat := [1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_517231 : Nat := 118140960795 + 517231 * 2 ^ 59
def prefixEnd_517231 : Nat := 4983230072969 + 3 ^ 40 * 517231 * 2
def baseEnd_517231 : Nat := 157385548092308779279291

theorem tailTrace_517231 : CollatzResearch.WordTrace tailWord_517231 prefixEnd_517231 157385548092308779279291 := by
  unfold tailWord_517231
  simp only [CollatzResearch.WordTrace]
  refine ⟨18864964389167897867119547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12576642926111931911413031 18864964389167897867119547)
  ·
    refine ⟨28297446583751846800679321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18864964389167897867119547 28297446583751846800679321)
    ·
      refine ⟨21223084937813885100509491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28297446583751846800679321 21223084937813885100509491)
      ·
        refine ⟨31834627406720827650764237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21223084937813885100509491 31834627406720827650764237)
        ·
          refine ⟨11937985277520310369036589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31834627406720827650764237 11937985277520310369036589)
          ·
            refine ⟨4476744479070116388388721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11937985277520310369036589 4476744479070116388388721)
            ·
              refine ⟨3357558359302587291291541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4476744479070116388388721 3357558359302587291291541)
              ·
                refine ⟨157385548092308779279291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3357558359302587291291541 157385548092308779279291)
                ·
                  rfl

theorem cell19_517231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_517231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517231 prefixEnd_517231 := by exact prefixLift 517231
  have htrace : WordTrace (prefixWord ++ tailWord_517231) baseStart_517231 baseEnd_517231 := by
    simpa [prefixWord, tailWord_517231, baseEnd_517231] using wordTrace_append hprefix tailTrace_517231
  have hstable : (prefixWord ++ tailWord_517231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517231).length < 2 ^ (prefixWord ++ tailWord_517231).sum := by decide
  have hdescent : baseEnd_517231 < baseStart_517231 := by decide
  rcases family_descends (prefixWord ++ tailWord_517231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517248 : List Nat := [2, 1, 1, 2, 1, 3, 6, 3]
def baseStart_517248 : Nat := 118140960795 + 517248 * 2 ^ 59
def prefixEnd_517248 : Nat := 4983230072969 + 3 ^ 40 * 517248 * 2
def baseEnd_517248 : Nat := 157390720934457776901467

theorem tailTrace_517248 : CollatzResearch.WordTrace tailWord_517248 prefixEnd_517248 157390720934457776901467 := by
  unfold tailWord_517248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9432792215053154885244199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12577056286737539846992265 9432792215053154885244199)
  ·
    refine ⟨14149188322579732327866299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9432792215053154885244199 14149188322579732327866299)
    ·
      refine ⟨21223782483869598491799449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14149188322579732327866299 21223782483869598491799449)
      ·
        refine ⟨15917836862902198868849587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21223782483869598491799449 15917836862902198868849587)
        ·
          refine ⟨23876755294353298303274381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15917836862902198868849587 23876755294353298303274381)
          ·
            refine ⟨8953783235382486863727893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23876755294353298303274381 8953783235382486863727893)
            ·
              refine ⟨419708589158554071737245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8953783235382486863727893 419708589158554071737245)
              ·
                refine ⟨157390720934457776901467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419708589158554071737245 157390720934457776901467)
                ·
                  rfl

theorem cell19_517248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_517248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517248 prefixEnd_517248 := by exact prefixLift 517248
  have htrace : WordTrace (prefixWord ++ tailWord_517248) baseStart_517248 baseEnd_517248 := by
    simpa [prefixWord, tailWord_517248, baseEnd_517248] using wordTrace_append hprefix tailTrace_517248
  have hstable : (prefixWord ++ tailWord_517248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517248).length < 2 ^ (prefixWord ++ tailWord_517248).sum := by decide
  have hdescent : baseEnd_517248 < baseStart_517248 := by decide
  rcases family_descends (prefixWord ++ tailWord_517248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517318 : List Nat := [6, 1, 2, 2, 2, 6]
def baseStart_517318 : Nat := 118140960795 + 517318 * 2 ^ 59
def prefixEnd_517318 : Nat := 4983230072969 + 3 ^ 40 * 517318 * 2
def baseEnd_517318 : Nat := 17490224541413150593969

theorem tailTrace_517318 : CollatzResearch.WordTrace tailWord_517318 prefixEnd_517318 17490224541413150593969 := by
  unfold tailWord_517318
  simp only [CollatzResearch.WordTrace]
  refine ⟨589629298120397241423019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12578758359901807817024405 589629298120397241423019)
  ·
    refine ⟨884443947180595862134529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 589629298120397241423019 884443947180595862134529)
    ·
      refine ⟨663332960385446896600897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 884443947180595862134529 663332960385446896600897)
      ·
        refine ⟨497499720289085172450673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663332960385446896600897 497499720289085172450673)
        ·
          refine ⟨373124790216813879338005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497499720289085172450673 373124790216813879338005)
          ·
            refine ⟨17490224541413150593969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 373124790216813879338005 17490224541413150593969)
            ·
              rfl

theorem cell19_517318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 6].length) (baseStart_517318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517318 prefixEnd_517318 := by exact prefixLift 517318
  have htrace : WordTrace (prefixWord ++ tailWord_517318) baseStart_517318 baseEnd_517318 := by
    simpa [prefixWord, tailWord_517318, baseEnd_517318] using wordTrace_append hprefix tailTrace_517318
  have hstable : (prefixWord ++ tailWord_517318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517318).length < 2 ^ (prefixWord ++ tailWord_517318).sum := by decide
  have hdescent : baseEnd_517318 < baseStart_517318 := by decide
  rcases family_descends (prefixWord ++ tailWord_517318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517326 : List Nat := [4, 1, 1, 1, 12]
def baseStart_517326 : Nat := 118140960795 + 517326 * 2 ^ 59
def prefixEnd_517326 : Nat := 4983230072969 + 3 ^ 40 * 517326 * 2
def baseEnd_517326 : Nat := 5830165005606544709923

theorem tailTrace_517326 : CollatzResearch.WordTrace tailWord_517326 prefixEnd_517326 5830165005606544709923 := by
  unfold tailWord_517326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2358553665477966136478479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12578952882549152727885221 2358553665477966136478479)
  ·
    refine ⟨3537830498216949204717719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2358553665477966136478479 3537830498216949204717719)
    ·
      refine ⟨5306745747325423807076579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3537830498216949204717719 5306745747325423807076579)
      ·
        refine ⟨7960118620988135710614869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5306745747325423807076579 7960118620988135710614869)
        ·
          refine ⟨5830165005606544709923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7960118620988135710614869 5830165005606544709923)
          ·
            rfl

theorem cell19_517326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 12].length) (baseStart_517326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517326 prefixEnd_517326 := by exact prefixLift 517326
  have htrace : WordTrace (prefixWord ++ tailWord_517326) baseStart_517326 baseEnd_517326 := by
    simpa [prefixWord, tailWord_517326, baseEnd_517326] using wordTrace_append hprefix tailTrace_517326
  have hstable : (prefixWord ++ tailWord_517326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517326).length < 2 ^ (prefixWord ++ tailWord_517326).sum := by decide
  have hdescent : baseEnd_517326 < baseStart_517326 := by decide
  rcases family_descends (prefixWord ++ tailWord_517326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517453 : List Nat := [1, 6, 1, 3, 1, 1, 2, 4]
def baseStart_517453 : Nat := 118140960795 + 517453 * 2 ^ 59
def prefixEnd_517453 : Nat := 4983230072969 + 3 ^ 40 * 517453 * 2
def baseEnd_517453 : Nat := 157453099325078042345353

theorem tailTrace_517453 : CollatzResearch.WordTrace tailWord_517453 prefixEnd_517453 157453099325078042345353 := by
  unfold tailWord_517453
  simp only [CollatzResearch.WordTrace]
  refine ⟨18873061394363629781701013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12582040929575753187800675 18873061394363629781701013)
  ·
    refine ⟨884674752860795146017235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18873061394363629781701013 884674752860795146017235)
    ·
      refine ⟨1327012129291192719025853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 884674752860795146017235 1327012129291192719025853)
      ·
        refine ⟨497629548484197269634695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1327012129291192719025853 497629548484197269634695)
        ·
          refine ⟨746444322726295904452043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497629548484197269634695 746444322726295904452043)
          ·
            refine ⟨1119666484089443856678065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746444322726295904452043 1119666484089443856678065)
            ·
              refine ⟨839749863067082892508549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119666484089443856678065 839749863067082892508549)
              ·
                refine ⟨157453099325078042345353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 839749863067082892508549 157453099325078042345353)
                ·
                  rfl

theorem cell19_517453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 4].length) (baseStart_517453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517453 prefixEnd_517453 := by exact prefixLift 517453
  have htrace : WordTrace (prefixWord ++ tailWord_517453) baseStart_517453 baseEnd_517453 := by
    simpa [prefixWord, tailWord_517453, baseEnd_517453] using wordTrace_append hprefix tailTrace_517453
  have hstable : (prefixWord ++ tailWord_517453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517453).length < 2 ^ (prefixWord ++ tailWord_517453).sum := by decide
  have hdescent : baseEnd_517453 < baseStart_517453 := by decide
  rcases family_descends (prefixWord ++ tailWord_517453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517459 : List Nat := [1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_517459 : Nat := 118140960795 + 517459 * 2 ^ 59
def prefixEnd_517459 : Nat := 4983230072969 + 3 ^ 40 * 517459 * 2
def baseEnd_517459 : Nat := 157454925034071806212003

theorem tailTrace_517459 : CollatzResearch.WordTrace tailWord_517459 prefixEnd_517459 157454925034071806212003 := by
  unfold tailWord_517459
  simp only [CollatzResearch.WordTrace]
  refine ⟨18873280232341892806419431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12582186821561261870946287 18873280232341892806419431)
  ·
    refine ⟨28309920348512839209629147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18873280232341892806419431 28309920348512839209629147)
    ·
      refine ⟨42464880522769258814443721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28309920348512839209629147 42464880522769258814443721)
      ·
        refine ⟨31848660392076944110832791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42464880522769258814443721 31848660392076944110832791)
        ·
          refine ⟨47772990588115416166249187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31848660392076944110832791 47772990588115416166249187)
          ·
            refine ⟨71659485882173124249373781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47772990588115416166249187 71659485882173124249373781)
            ·
              refine ⟨839759600181716299797349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 71659485882173124249373781 839759600181716299797349)
              ·
                refine ⟨157454925034071806212003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 839759600181716299797349 157454925034071806212003)
                ·
                  rfl

theorem cell19_517459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_517459 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517459 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517459 prefixEnd_517459 := by exact prefixLift 517459
  have htrace : WordTrace (prefixWord ++ tailWord_517459) baseStart_517459 baseEnd_517459 := by
    simpa [prefixWord, tailWord_517459, baseEnd_517459] using wordTrace_append hprefix tailTrace_517459
  have hstable : (prefixWord ++ tailWord_517459).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517459).length < 2 ^ (prefixWord ++ tailWord_517459).sum := by decide
  have hdescent : baseEnd_517459 < baseStart_517459 := by decide
  rcases family_descends (prefixWord ++ tailWord_517459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517662 : List Nat := [4, 3, 3, 1, 1, 7]
def baseStart_517662 : Nat := 118140960795 + 517662 * 2 ^ 59
def prefixEnd_517662 : Nat := 4983230072969 + 3 ^ 40 * 517662 * 2
def baseEnd_517662 : Nat := 17501854983891942633371

theorem tailTrace_517662 : CollatzResearch.WordTrace tailWord_517662 prefixEnd_517662 17501854983891942633371 := by
  unfold tailWord_517662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360085531325807309507405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12587122833737638984039493 2360085531325807309507405)
  ·
    refine ⟨885032074247177741065277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2360085531325807309507405 885032074247177741065277)
    ·
      refine ⟨331887027842691652899479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 885032074247177741065277 331887027842691652899479)
      ·
        refine ⟨497830541764037479349219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331887027842691652899479 497830541764037479349219)
        ·
          refine ⟨746745812646056219023829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497830541764037479349219 746745812646056219023829)
          ·
            refine ⟨17501854983891942633371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 746745812646056219023829 17501854983891942633371)
            ·
              rfl

theorem cell19_517662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 7].length) (baseStart_517662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517662 prefixEnd_517662 := by exact prefixLift 517662
  have htrace : WordTrace (prefixWord ++ tailWord_517662) baseStart_517662 baseEnd_517662 := by
    simpa [prefixWord, tailWord_517662, baseEnd_517662] using wordTrace_append hprefix tailTrace_517662
  have hstable : (prefixWord ++ tailWord_517662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517662).length < 2 ^ (prefixWord ++ tailWord_517662).sum := by decide
  have hdescent : baseEnd_517662 < baseStart_517662 := by decide
  rcases family_descends (prefixWord ++ tailWord_517662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517685 : List Nat := [1, 3, 3, 1, 1, 5, 1, 4]
def baseStart_517685 : Nat := 118140960795 + 517685 * 2 ^ 59
def prefixEnd_517685 : Nat := 4983230072969 + 3 ^ 40 * 517685 * 2
def baseEnd_517685 : Nat := 157523693406170245189165

theorem tailTrace_517685 : CollatzResearch.WordTrace tailWord_517685 prefixEnd_517685 157523693406170245189165 := by
  unfold tailWord_517685
  simp only [CollatzResearch.WordTrace]
  refine ⟨18881523129523133404146509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12587682086348755602764339 18881523129523133404146509)
  ·
    refine ⟨7080571173571175026554941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18881523129523133404146509 7080571173571175026554941)
    ·
      refine ⟨2655214190089190634958103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7080571173571175026554941 2655214190089190634958103)
      ·
        refine ⟨3982821285133785952437155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2655214190089190634958103 3982821285133785952437155)
        ·
          refine ⟨5974231927700678928655733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3982821285133785952437155 5974231927700678928655733)
          ·
            refine ⟨560084243221938649561475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5974231927700678928655733 560084243221938649561475)
            ·
              refine ⟨840126364832907974342213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560084243221938649561475 840126364832907974342213)
              ·
                refine ⟨157523693406170245189165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 840126364832907974342213 157523693406170245189165)
                ·
                  rfl

theorem cell19_517685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_517685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517685 prefixEnd_517685 := by exact prefixLift 517685
  have htrace : WordTrace (prefixWord ++ tailWord_517685) baseStart_517685 baseEnd_517685 := by
    simpa [prefixWord, tailWord_517685, baseEnd_517685] using wordTrace_append hprefix tailTrace_517685
  have hstable : (prefixWord ++ tailWord_517685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517685).length < 2 ^ (prefixWord ++ tailWord_517685).sum := by decide
  have hdescent : baseEnd_517685 < baseStart_517685 := by decide
  rcases family_descends (prefixWord ++ tailWord_517685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517687 : List Nat := [1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_517687 : Nat := 118140960795 + 517687 * 2 ^ 59
def prefixEnd_517687 : Nat := 4983230072969 + 3 ^ 40 * 517687 * 2
def baseEnd_517687 : Nat := 157524301975834833144715

theorem tailTrace_517687 : CollatzResearch.WordTrace tailWord_517687 prefixEnd_517687 157524301975834833144715 := by
  unfold tailWord_517687
  simp only [CollatzResearch.WordTrace]
  refine ⟨18881596075515887745719315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12587730717010591830479543 18881596075515887745719315)
  ·
    refine ⟨28322394113273831618578973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18881596075515887745719315 28322394113273831618578973)
    ·
      refine ⟨10620897792477686856967115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28322394113273831618578973 10620897792477686856967115)
      ·
        refine ⟨15931346688716530285450673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10620897792477686856967115 15931346688716530285450673)
        ·
          refine ⟨11948510016537397714088005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15931346688716530285450673 11948510016537397714088005)
          ·
            refine ⟨2240345628100762071391501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11948510016537397714088005 2240345628100762071391501)
            ·
              refine ⟨840129610537785776771813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2240345628100762071391501 840129610537785776771813)
              ·
                refine ⟨157524301975834833144715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 840129610537785776771813 157524301975834833144715)
                ·
                  rfl

theorem cell19_517687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_517687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517687 prefixEnd_517687 := by exact prefixLift 517687
  have htrace : WordTrace (prefixWord ++ tailWord_517687) baseStart_517687 baseEnd_517687 := by
    simpa [prefixWord, tailWord_517687, baseEnd_517687] using wordTrace_append hprefix tailTrace_517687
  have hstable : (prefixWord ++ tailWord_517687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517687).length < 2 ^ (prefixWord ++ tailWord_517687).sum := by decide
  have hdescent : baseEnd_517687 < baseStart_517687 := by decide
  rcases family_descends (prefixWord ++ tailWord_517687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517761 : List Nat := [1, 2, 4, 2, 1, 2, 4, 3]
def baseStart_517761 : Nat := 118140960795 + 517761 * 2 ^ 59
def prefixEnd_517761 : Nat := 4983230072969 + 3 ^ 40 * 517761 * 2
def baseEnd_517761 : Nat := 157546819053424587500069

theorem tailTrace_517761 : CollatzResearch.WordTrace tailWord_517761 prefixEnd_517761 157546819053424587500069 := by
  unfold tailWord_517761
  simp only [CollatzResearch.WordTrace]
  refine ⟨18884295077247798383913137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12589530051498532255942091 18884295077247798383913137)
  ·
    refine ⟨14163221307935848787934853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18884295077247798383913137 14163221307935848787934853)
    ·
      refine ⟨2655603995237971647737785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14163221307935848787934853 2655603995237971647737785)
      ·
        refine ⟨1991702996428478735803339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2655603995237971647737785 1991702996428478735803339)
        ·
          refine ⟨2987554494642718103705009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991702996428478735803339 2987554494642718103705009)
          ·
            refine ⟨2240665870982038577778757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2987554494642718103705009 2240665870982038577778757)
            ·
              refine ⟨420124850809132233333517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2240665870982038577778757 420124850809132233333517)
              ·
                refine ⟨157546819053424587500069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420124850809132233333517 157546819053424587500069)
                ·
                  rfl

theorem cell19_517761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 3].length) (baseStart_517761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517761 prefixEnd_517761 := by exact prefixLift 517761
  have htrace : WordTrace (prefixWord ++ tailWord_517761) baseStart_517761 baseEnd_517761 := by
    simpa [prefixWord, tailWord_517761, baseEnd_517761] using wordTrace_append hprefix tailTrace_517761
  have hstable : (prefixWord ++ tailWord_517761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517761).length < 2 ^ (prefixWord ++ tailWord_517761).sum := by decide
  have hdescent : baseEnd_517761 < baseStart_517761 := by decide
  rcases family_descends (prefixWord ++ tailWord_517761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517778 : List Nat := [3, 2, 3, 1, 4, 1, 5]
def baseStart_517778 : Nat := 118140960795 + 517778 * 2 ^ 59
def prefixEnd_517778 : Nat := 4983230072969 + 3 ^ 40 * 517778 * 2
def baseEnd_517778 : Nat := 52517330631857861707415

theorem tailTrace_517778 : CollatzResearch.WordTrace tailWord_517778 prefixEnd_517778 52517330631857861707415 := by
  unfold tailWord_517778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4721228779546552571820497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12589943412124140191521325 4721228779546552571820497)
  ·
    refine ⟨3540921584659914428865373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4721228779546552571820497 3540921584659914428865373)
    ·
      refine ⟨1327845594247467910824515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3540921584659914428865373 1327845594247467910824515)
      ·
        refine ⟨1991768391371201866236773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327845594247467910824515 1991768391371201866236773)
        ·
          refine ⟨373456573382100349919395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1991768391371201866236773 373456573382100349919395)
          ·
            refine ⟨560184860073150524879093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373456573382100349919395 560184860073150524879093)
            ·
              refine ⟨52517330631857861707415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 560184860073150524879093 52517330631857861707415)
              ·
                rfl

theorem cell19_517778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 5].length) (baseStart_517778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517778 prefixEnd_517778 := by exact prefixLift 517778
  have htrace : WordTrace (prefixWord ++ tailWord_517778) baseStart_517778 baseEnd_517778 := by
    simpa [prefixWord, tailWord_517778, baseEnd_517778] using wordTrace_append hprefix tailTrace_517778
  have hstable : (prefixWord ++ tailWord_517778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517778).length < 2 ^ (prefixWord ++ tailWord_517778).sum := by decide
  have hdescent : baseEnd_517778 < baseStart_517778 := by decide
  rcases family_descends (prefixWord ++ tailWord_517778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517820 : List Nat := [2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_517820 : Nat := 118140960795 + 517820 * 2 ^ 59
def prefixEnd_517820 : Nat := 4983230072969 + 3 ^ 40 * 517820 * 2
def baseEnd_517820 : Nat := 157564771858529932188797

theorem tailTrace_517820 : CollatzResearch.WordTrace tailWord_517820 prefixEnd_517820 157564771858529932188797 := by
  unfold tailWord_517820
  simp only [CollatzResearch.WordTrace]
  refine ⟨9443223492017025730155457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12590964656022700973540609 9443223492017025730155457)
  ·
    refine ⟨7082417619012769297616593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9443223492017025730155457 7082417619012769297616593)
    ·
      refine ⟨5311813214259576973212445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7082417619012769297616593 5311813214259576973212445)
      ·
        refine ⟨1991929955347341364954667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5311813214259576973212445 1991929955347341364954667)
        ·
          refine ⟨2987894933021012047432001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991929955347341364954667 2987894933021012047432001)
          ·
            refine ⟨2240921199765759035574001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2987894933021012047432001 2240921199765759035574001)
            ·
              refine ⟨1680690899824319276680501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2240921199765759035574001 1680690899824319276680501)
              ·
                refine ⟨157564771858529932188797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1680690899824319276680501 157564771858529932188797)
                ·
                  rfl

theorem cell19_517820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_517820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517820 prefixEnd_517820 := by exact prefixLift 517820
  have htrace : WordTrace (prefixWord ++ tailWord_517820) baseStart_517820 baseEnd_517820 := by
    simpa [prefixWord, tailWord_517820, baseEnd_517820] using wordTrace_append hprefix tailTrace_517820
  have hstable : (prefixWord ++ tailWord_517820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517820).length < 2 ^ (prefixWord ++ tailWord_517820).sum := by decide
  have hdescent : baseEnd_517820 < baseStart_517820 := by decide
  rcases family_descends (prefixWord ++ tailWord_517820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517837 : List Nat := [1, 6, 2, 1, 1, 8]
def baseStart_517837 : Nat := 118140960795 + 517837 * 2 ^ 59
def prefixEnd_517837 : Nat := 4983230072969 + 3 ^ 40 * 517837 * 2
def baseEnd_517837 : Nat := 17507771633408769978997

theorem tailTrace_517837 : CollatzResearch.WordTrace tailWord_517837 prefixEnd_517837 17507771633408769978997 := by
  unfold tailWord_517837
  simp only [CollatzResearch.WordTrace]
  refine ⟨18887067024972463363679765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12591378016648308909119843 18887067024972463363679765)
  ·
    refine ⟨885331266795584220172489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18887067024972463363679765 885331266795584220172489)
    ·
      refine ⟨663998450096688165129367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 885331266795584220172489 663998450096688165129367)
      ·
        refine ⟨995997675145032247694051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663998450096688165129367 995997675145032247694051)
        ·
          refine ⟨1493996512717548371541077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995997675145032247694051 1493996512717548371541077)
          ·
            refine ⟨17507771633408769978997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1493996512717548371541077 17507771633408769978997)
            ·
              rfl

theorem cell19_517837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 8].length) (baseStart_517837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517837 prefixEnd_517837 := by exact prefixLift 517837
  have htrace : WordTrace (prefixWord ++ tailWord_517837) baseStart_517837 baseEnd_517837 := by
    simpa [prefixWord, tailWord_517837, baseEnd_517837] using wordTrace_append hprefix tailTrace_517837
  have hstable : (prefixWord ++ tailWord_517837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517837).length < 2 ^ (prefixWord ++ tailWord_517837).sum := by decide
  have hdescent : baseEnd_517837 < baseStart_517837 := by decide
  rcases family_descends (prefixWord ++ tailWord_517837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517841 : List Nat := [1, 2, 2, 1, 2, 11]
def baseStart_517841 : Nat := 118140960795 + 517841 * 2 ^ 59
def prefixEnd_517841 : Nat := 4983230072969 + 3 ^ 40 * 517841 * 2
def baseEnd_517841 : Nat := 17507906871112011746897

theorem tailTrace_517841 : CollatzResearch.WordTrace tailWord_517841 prefixEnd_517841 17507906871112011746897 := by
  unfold tailWord_517841
  simp only [CollatzResearch.WordTrace]
  refine ⟨18887212916957972046825377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12591475277971981364550251 18887212916957972046825377)
  ·
    refine ⟨14165409687718479035119033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18887212916957972046825377 14165409687718479035119033)
    ·
      refine ⟨10624057265788859276339275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14165409687718479035119033 10624057265788859276339275)
      ·
        refine ⟨15936085898683288914508913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10624057265788859276339275 15936085898683288914508913)
        ·
          refine ⟨11952064424012466685881685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15936085898683288914508913 11952064424012466685881685)
          ·
            refine ⟨17507906871112011746897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11952064424012466685881685 17507906871112011746897)
            ·
              rfl

theorem cell19_517841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 11].length) (baseStart_517841 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517841 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517841 prefixEnd_517841 := by exact prefixLift 517841
  have htrace : WordTrace (prefixWord ++ tailWord_517841) baseStart_517841 baseEnd_517841 := by
    simpa [prefixWord, tailWord_517841, baseEnd_517841] using wordTrace_append hprefix tailTrace_517841
  have hstable : (prefixWord ++ tailWord_517841).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517841).length < 2 ^ (prefixWord ++ tailWord_517841).sum := by decide
  have hdescent : baseEnd_517841 < baseStart_517841 := by decide
  rcases family_descends (prefixWord ++ tailWord_517841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517852 : List Nat := [2, 2, 5, 1, 3, 1, 1, 4]
def baseStart_517852 : Nat := 118140960795 + 517852 * 2 ^ 59
def prefixEnd_517852 : Nat := 4983230072969 + 3 ^ 40 * 517852 * 2
def baseEnd_517852 : Nat := 157574508973163339477599

theorem tailTrace_517852 : CollatzResearch.WordTrace tailWord_517852 prefixEnd_517852 157574508973163339477599 := by
  unfold tailWord_517852
  simp only [CollatzResearch.WordTrace]
  refine ⟨9443807059959060462737905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12591742746612080616983873 9443807059959060462737905)
  ·
    refine ⟨7082855294969295347053429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9443807059959060462737905 7082855294969295347053429)
    ·
      refine ⟨664017683903371438786259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7082855294969295347053429 664017683903371438786259)
      ·
        refine ⟨996026525855057158179389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664017683903371438786259 996026525855057158179389)
        ·
          refine ⟨373509947195646434317271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 996026525855057158179389 373509947195646434317271)
          ·
            refine ⟨560264920793469651475907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373509947195646434317271 560264920793469651475907)
            ·
              refine ⟨840397381190204477213861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560264920793469651475907 840397381190204477213861)
              ·
                refine ⟨157574508973163339477599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 840397381190204477213861 157574508973163339477599)
                ·
                  rfl

theorem cell19_517852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_517852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517852 prefixEnd_517852 := by exact prefixLift 517852
  have htrace : WordTrace (prefixWord ++ tailWord_517852) baseStart_517852 baseEnd_517852 := by
    simpa [prefixWord, tailWord_517852, baseEnd_517852] using wordTrace_append hprefix tailTrace_517852
  have hstable : (prefixWord ++ tailWord_517852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517852).length < 2 ^ (prefixWord ++ tailWord_517852).sum := by decide
  have hdescent : baseEnd_517852 < baseStart_517852 := by decide
  rcases family_descends (prefixWord ++ tailWord_517852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517879 : List Nat := [1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_517879 : Nat := 118140960795 + 517879 * 2 ^ 59
def prefixEnd_517879 : Nat := 4983230072969 + 3 ^ 40 * 517879 * 2
def baseEnd_517879 : Nat := 157582724663635276877525

theorem tailTrace_517879 : CollatzResearch.WordTrace tailWord_517879 prefixEnd_517879 157582724663635276877525 := by
  unfold tailWord_517879
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888598890820304536708691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12592399260546869691139127 18888598890820304536708691)
  ·
    refine ⟨28332898336230456805063037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18888598890820304536708691 28332898336230456805063037)
    ·
      refine ⟨10624836876086421301898639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28332898336230456805063037 10624836876086421301898639)
      ·
        refine ⟨15937255314129631952847959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10624836876086421301898639 15937255314129631952847959)
        ·
          refine ⟨23905882971194447929271939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15937255314129631952847959 23905882971194447929271939)
          ·
            refine ⟨35858824456791671893907909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23905882971194447929271939 35858824456791671893907909)
            ·
              refine ⟨6723529585648438480107733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35858824456791671893907909 6723529585648438480107733)
              ·
                refine ⟨157582724663635276877525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6723529585648438480107733 157582724663635276877525)
                ·
                  rfl

theorem cell19_517879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_517879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517879 prefixEnd_517879 := by exact prefixLift 517879
  have htrace : WordTrace (prefixWord ++ tailWord_517879) baseStart_517879 baseEnd_517879 := by
    simpa [prefixWord, tailWord_517879, baseEnd_517879] using wordTrace_append hprefix tailTrace_517879
  have hstable : (prefixWord ++ tailWord_517879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517879).length < 2 ^ (prefixWord ++ tailWord_517879).sum := by decide
  have hdescent : baseEnd_517879 < baseStart_517879 := by decide
  rcases family_descends (prefixWord ++ tailWord_517879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517932 : List Nat := [2, 2, 1, 1, 1, 7, 2, 3]
def baseStart_517932 : Nat := 118140960795 + 517932 * 2 ^ 59
def prefixEnd_517932 : Nat := 4983230072969 + 3 ^ 40 * 517932 * 2
def baseEnd_517932 : Nat := 157598851759746857699603

theorem tailTrace_517932 : CollatzResearch.WordTrace tailWord_517932 prefixEnd_517932 157598851759746857699603 := by
  unfold tailWord_517932
  simp only [CollatzResearch.WordTrace]
  refine ⟨9445265979814147294194025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12593687973085529725592033 9445265979814147294194025)
  ·
    refine ⟨7083949484860610470645519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9445265979814147294194025 7083949484860610470645519)
    ·
      refine ⟨10625924227290915705968279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7083949484860610470645519 10625924227290915705968279)
      ·
        refine ⟨15938886340936373558952419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10625924227290915705968279 15938886340936373558952419)
        ·
          refine ⟨23908329511404560338428629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15938886340936373558952419 23908329511404560338428629)
          ·
            refine ⟨560351472923544382931921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 23908329511404560338428629 560351472923544382931921)
            ·
              refine ⟨420263604692658287198941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560351472923544382931921 420263604692658287198941)
              ·
                refine ⟨157598851759746857699603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420263604692658287198941 157598851759746857699603)
                ·
                  rfl

theorem cell19_517932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_517932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517932 prefixEnd_517932 := by exact prefixLift 517932
  have htrace : WordTrace (prefixWord ++ tailWord_517932) baseStart_517932 baseEnd_517932 := by
    simpa [prefixWord, tailWord_517932, baseEnd_517932] using wordTrace_append hprefix tailTrace_517932
  have hstable : (prefixWord ++ tailWord_517932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517932).length < 2 ^ (prefixWord ++ tailWord_517932).sum := by decide
  have hdescent : baseEnd_517932 < baseStart_517932 := by decide
  rcases family_descends (prefixWord ++ tailWord_517932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517951 : List Nat := [1, 1, 2, 2, 7, 1, 5]
def baseStart_517951 : Nat := 118140960795 + 517951 * 2 ^ 59
def prefixEnd_517951 : Nat := 4983230072969 + 3 ^ 40 * 517951 * 2
def baseEnd_517951 : Nat := 52534877723853481092443

theorem tailTrace_517951 : CollatzResearch.WordTrace tailWord_517951 prefixEnd_517951 52534877723853481092443 := by
  unfold tailWord_517951
  simp only [CollatzResearch.WordTrace]
  refine ⟨18891224946559460833329707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12594149964372973888886471 18891224946559460833329707)
  ·
    refine ⟨28336837419839191249994561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18891224946559460833329707 28336837419839191249994561)
    ·
      refine ⟨21252628064879393437495921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28336837419839191249994561 21252628064879393437495921)
      ·
        refine ⟨15939471048659545078121941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21252628064879393437495921 15939471048659545078121941)
        ·
          refine ⟨373581352702958087768483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15939471048659545078121941 373581352702958087768483)
          ·
            refine ⟨560372029054437131652725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373581352702958087768483 560372029054437131652725)
            ·
              refine ⟨52534877723853481092443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 560372029054437131652725 52534877723853481092443)
              ·
                rfl

theorem cell19_517951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 5].length) (baseStart_517951 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517951 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517951 prefixEnd_517951 := by exact prefixLift 517951
  have htrace : WordTrace (prefixWord ++ tailWord_517951) baseStart_517951 baseEnd_517951 := by
    simpa [prefixWord, tailWord_517951, baseEnd_517951] using wordTrace_append hprefix tailTrace_517951
  have hstable : (prefixWord ++ tailWord_517951).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517951).length < 2 ^ (prefixWord ++ tailWord_517951).sum := by decide
  have hdescent : baseEnd_517951 < baseStart_517951 := by decide
  rcases family_descends (prefixWord ++ tailWord_517951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517955 : List Nat := [1, 1, 1, 3, 1, 5, 7]
def baseStart_517955 : Nat := 118140960795 + 517955 * 2 ^ 59
def prefixEnd_517955 : Nat := 4983230072969 + 3 ^ 40 * 517955 * 2
def baseEnd_517955 : Nat := 52535283436963206396143

theorem tailTrace_517955 : CollatzResearch.WordTrace tailWord_517955 prefixEnd_517955 52535283436963206396143 := by
  unfold tailWord_517955
  simp only [CollatzResearch.WordTrace]
  refine ⟨18891370838544969516475319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12594247225696646344316879 18891370838544969516475319)
  ·
    refine ⟨28337056257817454274712979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18891370838544969516475319 28337056257817454274712979)
    ·
      refine ⟨42505584386726181412069469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28337056257817454274712979 42505584386726181412069469)
      ·
        refine ⟨15939594145022318029526051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42505584386726181412069469 15939594145022318029526051)
        ·
          refine ⟨23909391217533477044289077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15939594145022318029526051 23909391217533477044289077)
          ·
            refine ⟨2241505426643763472902101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23909391217533477044289077 2241505426643763472902101)
            ·
              refine ⟨52535283436963206396143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2241505426643763472902101 52535283436963206396143)
              ·
                rfl

theorem cell19_517955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_517955 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517955 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517955 prefixEnd_517955 := by exact prefixLift 517955
  have htrace : WordTrace (prefixWord ++ tailWord_517955) baseStart_517955 baseEnd_517955 := by
    simpa [prefixWord, tailWord_517955, baseEnd_517955] using wordTrace_append hprefix tailTrace_517955
  have hstable : (prefixWord ++ tailWord_517955).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517955).length < 2 ^ (prefixWord ++ tailWord_517955).sum := by decide
  have hdescent : baseEnd_517955 < baseStart_517955 := by decide
  rcases family_descends (prefixWord ++ tailWord_517955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517972 : List Nat := [2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_517972 : Nat := 118140960795 + 517972 * 2 ^ 59
def prefixEnd_517972 : Nat := 4983230072969 + 3 ^ 40 * 517972 * 2
def baseEnd_517972 : Nat := 157611023153038616810605

theorem tailTrace_517972 : CollatzResearch.WordTrace tailWord_517972 prefixEnd_517972 157611023153038616810605 := by
  unfold tailWord_517972
  simp only [CollatzResearch.WordTrace]
  refine ⟨9445995439741690709922085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12594660586322254279896113 9445995439741690709922085)
  ·
    refine ⟨1771124144951567008110391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9445995439741690709922085 1771124144951567008110391)
    ·
      refine ⟨2656686217427350512165587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1771124144951567008110391 2656686217427350512165587)
      ·
        refine ⟨3985029326141025768248381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2656686217427350512165587 3985029326141025768248381)
        ·
          refine ⟨1494385997302884663093143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3985029326141025768248381 1494385997302884663093143)
          ·
            refine ⟨2241578995954326994639715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494385997302884663093143 2241578995954326994639715)
            ·
              refine ⟨3362368493931490491959573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241578995954326994639715 3362368493931490491959573)
              ·
                refine ⟨157611023153038616810605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3362368493931490491959573 157611023153038616810605)
                ·
                  rfl

theorem cell19_517972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_517972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_517972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_517972 prefixEnd_517972 := by exact prefixLift 517972
  have htrace : WordTrace (prefixWord ++ tailWord_517972) baseStart_517972 baseEnd_517972 := by
    simpa [prefixWord, tailWord_517972, baseEnd_517972] using wordTrace_append hprefix tailTrace_517972
  have hstable : (prefixWord ++ tailWord_517972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517972).length < 2 ^ (prefixWord ++ tailWord_517972).sum := by decide
  have hdescent : baseEnd_517972 < baseStart_517972 := by decide
  rcases family_descends (prefixWord ++ tailWord_517972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518105 : List Nat := [1, 2, 1, 2, 6, 1, 1, 5]
def baseStart_518105 : Nat := 118140960795 + 518105 * 2 ^ 59
def prefixEnd_518105 : Nat := 4983230072969 + 3 ^ 40 * 518105 * 2
def baseEnd_518105 : Nat := 157651493035733715854687

theorem tailTrace_518105 : CollatzResearch.WordTrace tailWord_518105 prefixEnd_518105 157651493035733715854687 := by
  unfold tailWord_518105
  simp only [CollatzResearch.WordTrace]
  refine ⟨18896841788001545134435769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12597894525334363422957179 18896841788001545134435769)
  ·
    refine ⟨14172631341001158850826827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18896841788001545134435769 14172631341001158850826827)
    ·
      refine ⟨21258947011501738276240241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14172631341001158850826827 21258947011501738276240241)
      ·
        refine ⟨15944210258626303707180181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21258947011501738276240241 15944210258626303707180181)
        ·
          refine ⟨747384855873107986274071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15944210258626303707180181 747384855873107986274071)
          ·
            refine ⟨1121077283809661979411107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747384855873107986274071 1121077283809661979411107)
            ·
              refine ⟨1681615925714492969116661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121077283809661979411107 1681615925714492969116661)
              ·
                refine ⟨157651493035733715854687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1681615925714492969116661 157651493035733715854687)
                ·
                  rfl

theorem cell19_518105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_518105 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518105 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518105 prefixEnd_518105 := by exact prefixLift 518105
  have htrace : WordTrace (prefixWord ++ tailWord_518105) baseStart_518105 baseEnd_518105 := by
    simpa [prefixWord, tailWord_518105, baseEnd_518105] using wordTrace_append hprefix tailTrace_518105
  have hstable : (prefixWord ++ tailWord_518105).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518105).length < 2 ^ (prefixWord ++ tailWord_518105).sum := by decide
  have hdescent : baseEnd_518105 < baseStart_518105 := by decide
  rcases family_descends (prefixWord ++ tailWord_518105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518196 : List Nat := [2, 5, 1, 2, 2, 2, 1, 4]
def baseStart_518196 : Nat := 118140960795 + 518196 * 2 ^ 59
def prefixEnd_518196 : Nat := 4983230072969 + 3 ^ 40 * 518196 * 2
def baseEnd_518196 : Nat := 157679182955472467832217

theorem tailTrace_518196 : CollatzResearch.WordTrace tailWord_518196 prefixEnd_518196 157679182955472467832217 := by
  unfold tailWord_518196
  simp only [CollatzResearch.WordTrace]
  refine ⟨9450080415335933837999221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12600107220447911783998961 9450080415335933837999221)
  ·
    refine ⟨885945038937743797312427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9450080415335933837999221 885945038937743797312427)
    ·
      refine ⟨1328917558406615695968641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 885945038937743797312427 1328917558406615695968641)
      ·
        refine ⟨996688168804961771976481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1328917558406615695968641 996688168804961771976481)
        ·
          refine ⟨747516126603721328982361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996688168804961771976481 747516126603721328982361)
          ·
            refine ⟨560637094952790996736771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747516126603721328982361 560637094952790996736771)
            ·
              refine ⟨840955642429186495105157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560637094952790996736771 840955642429186495105157)
              ·
                refine ⟨157679182955472467832217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 840955642429186495105157 157679182955472467832217)
                ·
                  rfl

theorem cell19_518196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_518196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518196 prefixEnd_518196 := by exact prefixLift 518196
  have htrace : WordTrace (prefixWord ++ tailWord_518196) baseStart_518196 baseEnd_518196 := by
    simpa [prefixWord, tailWord_518196, baseEnd_518196] using wordTrace_append hprefix tailTrace_518196
  have hstable : (prefixWord ++ tailWord_518196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518196).length < 2 ^ (prefixWord ++ tailWord_518196).sum := by decide
  have hdescent : baseEnd_518196 < baseStart_518196 := by decide
  rcases family_descends (prefixWord ++ tailWord_518196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518240 : List Nat := [2, 1, 1, 3, 2, 4, 6]
def baseStart_518240 : Nat := 118140960795 + 518240 * 2 ^ 59
def prefixEnd_518240 : Nat := 4983230072969 + 3 ^ 40 * 518240 * 2
def baseEnd_518240 : Nat := 52564190496031134284773

theorem tailTrace_518240 : CollatzResearch.WordTrace tailWord_518240 prefixEnd_518240 52564190496031134284773 := by
  unfold tailWord_518240
  simp only [CollatzResearch.WordTrace]
  refine ⟨9450882821256231595300087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12601177095008308793733449 9450882821256231595300087)
  ·
    refine ⟨14176324231884347392950131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9450882821256231595300087 14176324231884347392950131)
    ·
      refine ⟨21264486347826521089425197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14176324231884347392950131 21264486347826521089425197)
      ·
        refine ⟨7974182380434945408534449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21264486347826521089425197 7974182380434945408534449)
        ·
          refine ⟨5980636785326209056400837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7974182380434945408534449 5980636785326209056400837)
          ·
            refine ⟨1121369397248664198075157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5980636785326209056400837 1121369397248664198075157)
            ·
              refine ⟨52564190496031134284773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1121369397248664198075157 52564190496031134284773)
              ·
                rfl

theorem cell19_518240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_518240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518240 prefixEnd_518240 := by exact prefixLift 518240
  have htrace : WordTrace (prefixWord ++ tailWord_518240) baseStart_518240 baseEnd_518240 := by
    simpa [prefixWord, tailWord_518240, baseEnd_518240] using wordTrace_append hprefix tailTrace_518240
  have hstable : (prefixWord ++ tailWord_518240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518240).length < 2 ^ (prefixWord ++ tailWord_518240).sum := by decide
  have hdescent : baseEnd_518240 < baseStart_518240 := by decide
  rcases family_descends (prefixWord ++ tailWord_518240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518295 : List Nat := [1, 1, 3, 3, 4, 2, 5]
def baseStart_518295 : Nat := 118140960795 + 518295 * 2 ^ 59
def prefixEnd_518295 : Nat := 4983230072969 + 3 ^ 40 * 518295 * 2
def baseEnd_518295 : Nat := 52569769051289857210649

theorem tailTrace_518295 : CollatzResearch.WordTrace tailWord_518295 prefixEnd_518295 52569769051289857210649 := by
  unfold tailWord_518295
  simp only [CollatzResearch.WordTrace]
  refine ⟨18903771657313207583852339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12602514438208805055901559 18903771657313207583852339)
  ·
    refine ⟨28355657485969811375778509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18903771657313207583852339 28355657485969811375778509)
    ·
      refine ⟨10633371557238679265916941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28355657485969811375778509 10633371557238679265916941)
      ·
        refine ⟨3987514333964504724718853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10633371557238679265916941 3987514333964504724718853)
        ·
          refine ⟨747658937618344635884785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3987514333964504724718853 747658937618344635884785)
          ·
            refine ⟨560744203213758476913589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747658937618344635884785 560744203213758476913589)
            ·
              refine ⟨52569769051289857210649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 560744203213758476913589 52569769051289857210649)
              ·
                rfl

theorem cell19_518295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_518295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518295 prefixEnd_518295 := by exact prefixLift 518295
  have htrace : WordTrace (prefixWord ++ tailWord_518295) baseStart_518295 baseEnd_518295 := by
    simpa [prefixWord, tailWord_518295, baseEnd_518295] using wordTrace_append hprefix tailTrace_518295
  have hstable : (prefixWord ++ tailWord_518295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518295).length < 2 ^ (prefixWord ++ tailWord_518295).sum := by decide
  have hdescent : baseEnd_518295 < baseStart_518295 := by decide
  rcases family_descends (prefixWord ++ tailWord_518295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518354 : List Nat := [3, 2, 2, 2, 1, 9]
def baseStart_518354 : Nat := 118140960795 + 518354 * 2 ^ 59
def prefixEnd_518354 : Nat := 4983230072969 + 3 ^ 40 * 518354 * 2
def baseEnd_518354 : Nat := 17525251106552768480075

theorem tailTrace_518354 : CollatzResearch.WordTrace tailWord_518354 prefixEnd_518354 17525251106552768480075 := by
  unfold tailWord_518354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726480891024865165062529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12603949042732973773500077 4726480891024865165062529)
  ·
    refine ⟨3544860668268648873796897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4726480891024865165062529 3544860668268648873796897)
    ·
      refine ⟨2658645501201486655347673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3544860668268648873796897 2658645501201486655347673)
      ·
        refine ⟨1993984125901114991510755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2658645501201486655347673 1993984125901114991510755)
        ·
          refine ⟨2990976188851672487266133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993984125901114991510755 2990976188851672487266133)
          ·
            refine ⟨17525251106552768480075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2990976188851672487266133 17525251106552768480075)
            ·
              rfl

theorem cell19_518354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 9].length) (baseStart_518354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518354 prefixEnd_518354 := by exact prefixLift 518354
  have htrace : WordTrace (prefixWord ++ tailWord_518354) baseStart_518354 baseEnd_518354 := by
    simpa [prefixWord, tailWord_518354, baseEnd_518354] using wordTrace_append hprefix tailTrace_518354
  have hstable : (prefixWord ++ tailWord_518354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518354).length < 2 ^ (prefixWord ++ tailWord_518354).sum := by decide
  have hdescent : baseEnd_518354 < baseStart_518354 := by decide
  rcases family_descends (prefixWord ++ tailWord_518354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518439 : List Nat := [1, 1, 8, 1, 2, 1, 2, 3]
def baseStart_518439 : Nat := 118140960795 + 518439 * 2 ^ 59
def prefixEnd_518439 : Nat := 4983230072969 + 3 ^ 40 * 518439 * 2
def baseEnd_518439 : Nat := 157753124169719904431555

theorem tailTrace_518439 : CollatzResearch.WordTrace tailWord_518439 prefixEnd_518439 157753124169719904431555 := by
  unfold tailWord_518439
  simp only [CollatzResearch.WordTrace]
  refine ⟨18909023768791520177094371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12606015845861013451396247 18909023768791520177094371)
  ·
    refine ⟨28363535653187280265641557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18909023768791520177094371 28363535653187280265641557)
    ·
      refine ⟨332385183435788440612987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 28363535653187280265641557 332385183435788440612987)
      ·
        refine ⟨498577775153682660919481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332385183435788440612987 498577775153682660919481)
        ·
          refine ⟨373933331365261995689611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498577775153682660919481 373933331365261995689611)
          ·
            refine ⟨560899997047892993534417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373933331365261995689611 560899997047892993534417)
            ·
              refine ⟨420674997785919745150813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560899997047892993534417 420674997785919745150813)
              ·
                refine ⟨157753124169719904431555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420674997785919745150813 157753124169719904431555)
                ·
                  rfl

theorem cell19_518439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 3].length) (baseStart_518439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518439 prefixEnd_518439 := by exact prefixLift 518439
  have htrace : WordTrace (prefixWord ++ tailWord_518439) baseStart_518439 baseEnd_518439 := by
    simpa [prefixWord, tailWord_518439, baseEnd_518439] using wordTrace_append hprefix tailTrace_518439
  have hstable : (prefixWord ++ tailWord_518439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518439).length < 2 ^ (prefixWord ++ tailWord_518439).sum := by decide
  have hdescent : baseEnd_518439 < baseStart_518439 := by decide
  rcases family_descends (prefixWord ++ tailWord_518439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518445 : List Nat := [1, 5, 3, 1, 2, 1, 1, 5]
def baseStart_518445 : Nat := 118140960795 + 518445 * 2 ^ 59
def prefixEnd_518445 : Nat := 4983230072969 + 3 ^ 40 * 518445 * 2
def baseEnd_518445 : Nat := 157754949878713668298205

theorem tailTrace_518445 : CollatzResearch.WordTrace tailWord_518445 prefixEnd_518445 157754949878713668298205 := by
  unfold tailWord_518445
  simp only [CollatzResearch.WordTrace]
  refine ⟨18909242606769783201812789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12606161737846522134541859 18909242606769783201812789)
  ·
    refine ⟨1772741494384667175169949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18909242606769783201812789 1772741494384667175169949)
    ·
      refine ⟨664778060394250190688731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1772741494384667175169949 664778060394250190688731)
      ·
        refine ⟨997167090591375286033097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664778060394250190688731 997167090591375286033097)
        ·
          refine ⟨747875317943531464524823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 997167090591375286033097 747875317943531464524823)
          ·
            refine ⟨1121812976915297196787235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747875317943531464524823 1121812976915297196787235)
            ·
              refine ⟨1682719465372945795180853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121812976915297196787235 1682719465372945795180853)
              ·
                refine ⟨157754949878713668298205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1682719465372945795180853 157754949878713668298205)
                ·
                  rfl

theorem cell19_518445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_518445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518445 prefixEnd_518445 := by exact prefixLift 518445
  have htrace : WordTrace (prefixWord ++ tailWord_518445) baseStart_518445 baseEnd_518445 := by
    simpa [prefixWord, tailWord_518445, baseEnd_518445] using wordTrace_append hprefix tailTrace_518445
  have hstable : (prefixWord ++ tailWord_518445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518445).length < 2 ^ (prefixWord ++ tailWord_518445).sum := by decide
  have hdescent : baseEnd_518445 < baseStart_518445 := by decide
  rcases family_descends (prefixWord ++ tailWord_518445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518485 : List Nat := [1, 3, 2, 2, 4, 1, 2, 4]
def baseStart_518485 : Nat := 118140960795 + 518485 * 2 ^ 59
def prefixEnd_518485 : Nat := 4983230072969 + 3 ^ 40 * 518485 * 2
def baseEnd_518485 : Nat := 157767121272005427409207

theorem tailTrace_518485 : CollatzResearch.WordTrace tailWord_518485 prefixEnd_518485 157767121272005427409207 := by
  unfold tailWord_518485
  simp only [CollatzResearch.WordTrace]
  refine ⟨18910701526624870033268909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12607134351083246688845939 18910701526624870033268909)
  ·
    refine ⟨7091513072484326262475841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18910701526624870033268909 7091513072484326262475841)
    ·
      refine ⟨5318634804363244696856881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7091513072484326262475841 5318634804363244696856881)
      ·
        refine ⟨3988976103272433522642661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5318634804363244696856881 3988976103272433522642661)
        ·
          refine ⟨747933019363581285495499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3988976103272433522642661 747933019363581285495499)
          ·
            refine ⟨1121899529045371928243249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747933019363581285495499 1121899529045371928243249)
            ·
              refine ⟨841424646784028946182437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121899529045371928243249 841424646784028946182437)
              ·
                refine ⟨157767121272005427409207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841424646784028946182437 157767121272005427409207)
                ·
                  rfl

theorem cell19_518485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_518485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518485 prefixEnd_518485 := by exact prefixLift 518485
  have htrace : WordTrace (prefixWord ++ tailWord_518485) baseStart_518485 baseEnd_518485 := by
    simpa [prefixWord, tailWord_518485, baseEnd_518485] using wordTrace_append hprefix tailTrace_518485
  have hstable : (prefixWord ++ tailWord_518485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518485).length < 2 ^ (prefixWord ++ tailWord_518485).sum := by decide
  have hdescent : baseEnd_518485 < baseStart_518485 := by decide
  rcases family_descends (prefixWord ++ tailWord_518485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518487 : List Nat := [1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_518487 : Nat := 118140960795 + 518487 * 2 ^ 59
def prefixEnd_518487 : Nat := 4983230072969 + 3 ^ 40 * 518487 * 2
def baseEnd_518487 : Nat := 157767729841670015364757

theorem tailTrace_518487 : CollatzResearch.WordTrace tailWord_518487 prefixEnd_518487 157767729841670015364757 := by
  unfold tailWord_518487
  simp only [CollatzResearch.WordTrace]
  refine ⟨18910774472617624374841715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12607182981745082916561143 18910774472617624374841715)
  ·
    refine ⟨28366161708926436562262573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18910774472617624374841715 28366161708926436562262573)
    ·
      refine ⟨10637310640847413710848465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28366161708926436562262573 10637310640847413710848465)
      ·
        refine ⟨7977982980635560283136349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10637310640847413710848465 7977982980635560283136349)
        ·
          refine ⟨2991743617738335106176131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7977982980635560283136349 2991743617738335106176131)
          ·
            refine ⟨4487615426607502659264197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991743617738335106176131 4487615426607502659264197)
            ·
              refine ⟨841427892488906748612037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4487615426607502659264197 841427892488906748612037)
              ·
                refine ⟨157767729841670015364757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841427892488906748612037 157767729841670015364757)
                ·
                  rfl

theorem cell19_518487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_518487 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518487 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518487 prefixEnd_518487 := by exact prefixLift 518487
  have htrace : WordTrace (prefixWord ++ tailWord_518487) baseStart_518487 baseEnd_518487 := by
    simpa [prefixWord, tailWord_518487, baseEnd_518487] using wordTrace_append hprefix tailTrace_518487
  have hstable : (prefixWord ++ tailWord_518487).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518487).length < 2 ^ (prefixWord ++ tailWord_518487).sum := by decide
  have hdescent : baseEnd_518487 < baseStart_518487 := by decide
  rcases family_descends (prefixWord ++ tailWord_518487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518538 : List Nat := [3, 1, 2, 5, 2, 1, 1, 4]
def baseStart_518538 : Nat := 118140960795 + 518538 * 2 ^ 59
def prefixEnd_518538 : Nat := 4983230072969 + 3 ^ 40 * 518538 * 2
def baseEnd_518538 : Nat := 157783248368117008231285

theorem tailTrace_518538 : CollatzResearch.WordTrace tailWord_518538 prefixEnd_518538 157783248368117008231285 := by
  unfold tailWord_518538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4728158648858215021237067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12608423063621906723298845 4728158648858215021237067)
  ·
    refine ⟨7092237973287322531855601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4728158648858215021237067 7092237973287322531855601)
    ·
      refine ⟨5319178479965491898891701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7092237973287322531855601 5319178479965491898891701)
      ·
        refine ⟨498672982496764865521097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5319178479965491898891701 498672982496764865521097)
        ·
          refine ⟨374004736872573649140823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498672982496764865521097 374004736872573649140823)
          ·
            refine ⟨561007105308860473711235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374004736872573649140823 561007105308860473711235)
            ·
              refine ⟨841510657963290710566853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561007105308860473711235 841510657963290710566853)
              ·
                refine ⟨157783248368117008231285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841510657963290710566853 157783248368117008231285)
                ·
                  rfl

theorem cell19_518538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_518538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518538 prefixEnd_518538 := by exact prefixLift 518538
  have htrace : WordTrace (prefixWord ++ tailWord_518538) baseStart_518538 baseEnd_518538 := by
    simpa [prefixWord, tailWord_518538, baseEnd_518538] using wordTrace_append hprefix tailTrace_518538
  have hstable : (prefixWord ++ tailWord_518538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518538).length < 2 ^ (prefixWord ++ tailWord_518538).sum := by decide
  have hdescent : baseEnd_518538 < baseStart_518538 := by decide
  rcases family_descends (prefixWord ++ tailWord_518538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518542 : List Nat := [4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_518542 : Nat := 118140960795 + 518542 * 2 ^ 59
def prefixEnd_518542 : Nat := 4983230072969 + 3 ^ 40 * 518542 * 2
def baseEnd_518542 : Nat := 157784465507446184142385

theorem tailTrace_518542 : CollatzResearch.WordTrace tailWord_518542 prefixEnd_518542 157784465507446184142385 := by
  unfold tailWord_518542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364097560927296096011735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12608520324945579178729253 2364097560927296096011735)
  ·
    refine ⟨3546146341390944144017603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2364097560927296096011735 3546146341390944144017603)
    ·
      refine ⟨5319219512086416216026405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546146341390944144017603 5319219512086416216026405)
      ·
        refine ⟨997353658516203040504951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5319219512086416216026405 997353658516203040504951)
        ·
          refine ⟨1496030487774304560757427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997353658516203040504951 1496030487774304560757427)
          ·
            refine ⟨2244045731661456841136141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496030487774304560757427 2244045731661456841136141)
            ·
              refine ⟨841517149373046315426053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2244045731661456841136141 841517149373046315426053)
              ·
                refine ⟨157784465507446184142385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841517149373046315426053 157784465507446184142385)
                ·
                  rfl

theorem cell19_518542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_518542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518542 prefixEnd_518542 := by exact prefixLift 518542
  have htrace : WordTrace (prefixWord ++ tailWord_518542) baseStart_518542 baseEnd_518542 := by
    simpa [prefixWord, tailWord_518542, baseEnd_518542] using wordTrace_append hprefix tailTrace_518542
  have hstable : (prefixWord ++ tailWord_518542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518542).length < 2 ^ (prefixWord ++ tailWord_518542).sum := by decide
  have hdescent : baseEnd_518542 < baseStart_518542 := by decide
  rcases family_descends (prefixWord ++ tailWord_518542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518603 : List Nat := [1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_518603 : Nat := 118140960795 + 518603 * 2 ^ 59
def prefixEnd_518603 : Nat := 4983230072969 + 3 ^ 40 * 518603 * 2
def baseEnd_518603 : Nat := 157803026882216116786663

theorem tailTrace_518603 : CollatzResearch.WordTrace tailWord_518603 prefixEnd_518603 157803026882216116786663 := by
  unfold tailWord_518603
  simp only [CollatzResearch.WordTrace]
  refine ⟨18915005340197376186064463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12610003560131584124042975 18915005340197376186064463)
  ·
    refine ⟨28372508010296064279096695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18915005340197376186064463 28372508010296064279096695)
    ·
      refine ⟨42558762015444096418645043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28372508010296064279096695 42558762015444096418645043)
      ·
        refine ⟨63838143023166144627967565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42558762015444096418645043 63838143023166144627967565)
        ·
          refine ⟨23939303633687304235487837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63838143023166144627967565 23939303633687304235487837)
          ·
            refine ⟨8977238862632739088307939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23939303633687304235487837 8977238862632739088307939)
            ·
              refine ⟨13465858293949108632461909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8977238862632739088307939 13465858293949108632461909)
              ·
                refine ⟨157803026882216116786663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13465858293949108632461909 157803026882216116786663)
                ·
                  rfl

theorem cell19_518603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_518603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518603 prefixEnd_518603 := by exact prefixLift 518603
  have htrace : WordTrace (prefixWord ++ tailWord_518603) baseStart_518603 baseEnd_518603 := by
    simpa [prefixWord, tailWord_518603, baseEnd_518603] using wordTrace_append hprefix tailTrace_518603
  have hstable : (prefixWord ++ tailWord_518603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518603).length < 2 ^ (prefixWord ++ tailWord_518603).sum := by decide
  have hdescent : baseEnd_518603 < baseStart_518603 := by decide
  rcases family_descends (prefixWord ++ tailWord_518603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518637 : List Nat := [1, 5, 1, 3, 1, 3, 5]
def baseStart_518637 : Nat := 118140960795 + 518637 * 2 ^ 59
def prefixEnd_518637 : Nat := 4983230072969 + 3 ^ 40 * 518637 * 2
def baseEnd_518637 : Nat := 52604457522171370677005

theorem tailTrace_518637 : CollatzResearch.WordTrace tailWord_518637 prefixEnd_518637 52604457522171370677005 := by
  unfold tailWord_518637
  simp only [CollatzResearch.WordTrace]
  refine ⟨18916245422074199992802165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12610830281382799995201443 18916245422074199992802165)
  ·
    refine ⟨1773398008319456249325203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18916245422074199992802165 1773398008319456249325203)
    ·
      refine ⟨2660097012479184373987805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773398008319456249325203 2660097012479184373987805)
      ·
        refine ⟨997536379679694140245427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2660097012479184373987805 997536379679694140245427)
        ·
          refine ⟨1496304569519541210368141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997536379679694140245427 1496304569519541210368141)
          ·
            refine ⟨561114213569827953888053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1496304569519541210368141 561114213569827953888053)
            ·
              refine ⟨52604457522171370677005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 561114213569827953888053 52604457522171370677005)
              ·
                rfl

theorem cell19_518637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_518637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518637 prefixEnd_518637 := by exact prefixLift 518637
  have htrace : WordTrace (prefixWord ++ tailWord_518637) baseStart_518637 baseEnd_518637 := by
    simpa [prefixWord, tailWord_518637, baseEnd_518637] using wordTrace_append hprefix tailTrace_518637
  have hstable : (prefixWord ++ tailWord_518637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518637).length < 2 ^ (prefixWord ++ tailWord_518637).sum := by decide
  have hdescent : baseEnd_518637 < baseStart_518637 := by decide
  rcases family_descends (prefixWord ++ tailWord_518637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518696 : List Nat := [2, 1, 5, 2, 1, 8]
def baseStart_518696 : Nat := 118140960795 + 518696 * 2 ^ 59
def prefixEnd_518696 : Nat := 4983230072969 + 3 ^ 40 * 518696 * 2
def baseEnd_518696 : Nat := 17536813930179939635527

theorem tailTrace_518696 : CollatzResearch.WordTrace tailWord_518696 prefixEnd_518696 17536813930179939635527 := by
  unfold tailWord_518696
  simp only [CollatzResearch.WordTrace]
  refine ⟨9459198664430226534599971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12612264885906968712799961 9459198664430226534599971)
  ·
    refine ⟨14188797996645339801899957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9459198664430226534599971 14188797996645339801899957)
    ·
      refine ⟨1330199812185500606428121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14188797996645339801899957 1330199812185500606428121)
      ·
        refine ⟨997649859139125454821091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1330199812185500606428121 997649859139125454821091)
        ·
          refine ⟨1496474788708688182231637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997649859139125454821091 1496474788708688182231637)
          ·
            refine ⟨17536813930179939635527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1496474788708688182231637 17536813930179939635527)
            ·
              rfl

theorem cell19_518696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 8].length) (baseStart_518696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518696 prefixEnd_518696 := by exact prefixLift 518696
  have htrace : WordTrace (prefixWord ++ tailWord_518696) baseStart_518696 baseEnd_518696 := by
    simpa [prefixWord, tailWord_518696, baseEnd_518696] using wordTrace_append hprefix tailTrace_518696
  have hstable : (prefixWord ++ tailWord_518696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518696).length < 2 ^ (prefixWord ++ tailWord_518696).sum := by decide
  have hdescent : baseEnd_518696 < baseStart_518696 := by decide
  rcases family_descends (prefixWord ++ tailWord_518696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518755 : List Nat := [1, 1, 1, 5, 1, 2, 8]
def baseStart_518755 : Nat := 118140960795 + 518755 * 2 ^ 59
def prefixEnd_518755 : Nat := 4983230072969 + 3 ^ 40 * 518755 * 2
def baseEnd_518755 : Nat := 52616426058908267136157

theorem tailTrace_518755 : CollatzResearch.WordTrace tailWord_518755 prefixEnd_518755 52616426058908267136157 := by
  unfold tailWord_518755
  simp only [CollatzResearch.WordTrace]
  refine ⟨18920549235646706145597719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12613699490431137430398479 18920549235646706145597719)
  ·
    refine ⟨28380823853470059218396579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18920549235646706145597719 28380823853470059218396579)
    ·
      refine ⟨42571235780205088827594869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28380823853470059218396579 42571235780205088827594869)
      ·
        refine ⟨3991053354394227077587019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42571235780205088827594869 3991053354394227077587019)
        ·
          refine ⟨5986580031591340616380529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991053354394227077587019 5986580031591340616380529)
          ·
            refine ⟨4489935023693505462285397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5986580031591340616380529 4489935023693505462285397)
            ·
              refine ⟨52616426058908267136157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4489935023693505462285397 52616426058908267136157)
              ·
                rfl

theorem cell19_518755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_518755 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518755 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518755 prefixEnd_518755 := by exact prefixLift 518755
  have htrace : WordTrace (prefixWord ++ tailWord_518755) baseStart_518755 baseEnd_518755 := by
    simpa [prefixWord, tailWord_518755, baseEnd_518755] using wordTrace_append hprefix tailTrace_518755
  have hstable : (prefixWord ++ tailWord_518755).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518755).length < 2 ^ (prefixWord ++ tailWord_518755).sum := by decide
  have hdescent : baseEnd_518755 < baseStart_518755 := by decide
  rcases family_descends (prefixWord ++ tailWord_518755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518789 : List Nat := [1, 3, 1, 1, 4, 4, 2, 3]
def baseStart_518789 : Nat := 118140960795 + 518789 * 2 ^ 59
def prefixEnd_518789 : Nat := 4983230072969 + 3 ^ 40 * 518789 * 2
def baseEnd_518789 : Nat := 157859623861022796652823

theorem tailTrace_518789 : CollatzResearch.WordTrace tailWord_518789 prefixEnd_518789 157859623861022796652823 := by
  unfold tailWord_518789
  simp only [CollatzResearch.WordTrace]
  refine ⟨18921789317523529952335421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12614526211682353301556947 18921789317523529952335421)
  ·
    refine ⟨7095670994071323732125783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18921789317523529952335421 7095670994071323732125783)
    ·
      refine ⟨10643506491106985598188675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7095670994071323732125783 10643506491106985598188675)
      ·
        refine ⟨15965259736660478397283013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10643506491106985598188675 15965259736660478397283013)
        ·
          refine ⟨2993486200623839699490565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15965259736660478397283013 2993486200623839699490565)
          ·
            refine ⟨561278662616969943654481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2993486200623839699490565 561278662616969943654481)
            ·
              refine ⟨420958996962727457740861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561278662616969943654481 420958996962727457740861)
              ·
                refine ⟨157859623861022796652823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420958996962727457740861 157859623861022796652823)
                ·
                  rfl

theorem cell19_518789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 3].length) (baseStart_518789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518789 prefixEnd_518789 := by exact prefixLift 518789
  have htrace : WordTrace (prefixWord ++ tailWord_518789) baseStart_518789 baseEnd_518789 := by
    simpa [prefixWord, tailWord_518789, baseEnd_518789] using wordTrace_append hprefix tailTrace_518789
  have hstable : (prefixWord ++ tailWord_518789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518789).length < 2 ^ (prefixWord ++ tailWord_518789).sum := by decide
  have hdescent : baseEnd_518789 < baseStart_518789 := by decide
  rcases family_descends (prefixWord ++ tailWord_518789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518829 : List Nat := [1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_518829 : Nat := 118140960795 + 518829 * 2 ^ 59
def prefixEnd_518829 : Nat := 4983230072969 + 3 ^ 40 * 518829 * 2
def baseEnd_518829 : Nat := 157871795254314555763825

theorem tailTrace_518829 : CollatzResearch.WordTrace tailWord_518829 prefixEnd_518829 157871795254314555763825 := by
  unfold tailWord_518829
  simp only [CollatzResearch.WordTrace]
  refine ⟨18923248237378616783791541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12615498824919077855861027 18923248237378616783791541)
  ·
    refine ⟨1774054522254245323480457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18923248237378616783791541 1774054522254245323480457)
    ·
      refine ⟨1330540891690683992610343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1774054522254245323480457 1330540891690683992610343)
      ·
        refine ⟨1995811337536025988915515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330540891690683992610343 1995811337536025988915515)
        ·
          refine ⟨2993717006304038983373273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995811337536025988915515 2993717006304038983373273)
          ·
            refine ⟨2245287754728029237529955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2993717006304038983373273 2245287754728029237529955)
            ·
              refine ⟨3367931632092043856294933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245287754728029237529955 3367931632092043856294933)
              ·
                refine ⟨157871795254314555763825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3367931632092043856294933 157871795254314555763825)
                ·
                  rfl

theorem cell19_518829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_518829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518829 prefixEnd_518829 := by exact prefixLift 518829
  have htrace : WordTrace (prefixWord ++ tailWord_518829) baseStart_518829 baseEnd_518829 := by
    simpa [prefixWord, tailWord_518829, baseEnd_518829] using wordTrace_append hprefix tailTrace_518829
  have hstable : (prefixWord ++ tailWord_518829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518829).length < 2 ^ (prefixWord ++ tailWord_518829).sum := by decide
  have hdescent : baseEnd_518829 < baseStart_518829 := by decide
  rcases family_descends (prefixWord ++ tailWord_518829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518831 : List Nat := [1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_518831 : Nat := 118140960795 + 518831 * 2 ^ 59
def prefixEnd_518831 : Nat := 4983230072969 + 3 ^ 40 * 518831 * 2
def baseEnd_518831 : Nat := 157872403823979143719375

theorem tailTrace_518831 : CollatzResearch.WordTrace tailWord_518831 prefixEnd_518831 157872403823979143719375 := by
  unfold tailWord_518831
  simp only [CollatzResearch.WordTrace]
  refine ⟨18923321183371371125364347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12615547455580914083576231 18923321183371371125364347)
  ·
    refine ⟨28384981775057056688046521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18923321183371371125364347 28384981775057056688046521)
    ·
      refine ⟨21288736331292792516034891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28384981775057056688046521 21288736331292792516034891)
      ·
        refine ⟨31933104496939188774052337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21288736331292792516034891 31933104496939188774052337)
        ·
          refine ⟨23949828372704391580539253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31933104496939188774052337 23949828372704391580539253)
          ·
            refine ⟨2245296409941036710675555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23949828372704391580539253 2245296409941036710675555)
            ·
              refine ⟨3367944614911555066013333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245296409941036710675555 3367944614911555066013333)
              ·
                refine ⟨157872403823979143719375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3367944614911555066013333 157872403823979143719375)
                ·
                  rfl

theorem cell19_518831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_518831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518831 prefixEnd_518831 := by exact prefixLift 518831
  have htrace : WordTrace (prefixWord ++ tailWord_518831) baseStart_518831 baseEnd_518831 := by
    simpa [prefixWord, tailWord_518831, baseEnd_518831] using wordTrace_append hprefix tailTrace_518831
  have hstable : (prefixWord ++ tailWord_518831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518831).length < 2 ^ (prefixWord ++ tailWord_518831).sum := by decide
  have hdescent : baseEnd_518831 < baseStart_518831 := by decide
  rcases family_descends (prefixWord ++ tailWord_518831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518945 : List Nat := [1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_518945 : Nat := 118140960795 + 518945 * 2 ^ 59
def prefixEnd_518945 : Nat := 4983230072969 + 3 ^ 40 * 518945 * 2
def baseEnd_518945 : Nat := 157907092294860657185731

theorem tailTrace_518945 : CollatzResearch.WordTrace tailWord_518945 prefixEnd_518945 157907092294860657185731 := by
  unfold tailWord_518945
  simp only [CollatzResearch.WordTrace]
  refine ⟨18927479104958368595014289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12618319403305579063342859 18927479104958368595014289)
  ·
    refine ⟨14195609328718776446260717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18927479104958368595014289 14195609328718776446260717)
    ·
      refine ⟨5323353498269541167347769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14195609328718776446260717 5323353498269541167347769)
      ·
        refine ⟨3992515123702155875510827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5323353498269541167347769 3992515123702155875510827)
        ·
          refine ⟨5988772685553233813266241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992515123702155875510827 5988772685553233813266241)
          ·
            refine ⟨4491579514164925359949681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5988772685553233813266241 4491579514164925359949681)
            ·
              refine ⟨3368684635623694019962261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491579514164925359949681 3368684635623694019962261)
              ·
                refine ⟨157907092294860657185731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3368684635623694019962261 157907092294860657185731)
                ·
                  rfl

theorem cell19_518945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_518945 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518945 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518945 prefixEnd_518945 := by exact prefixLift 518945
  have htrace : WordTrace (prefixWord ++ tailWord_518945) baseStart_518945 baseEnd_518945 := by
    simpa [prefixWord, tailWord_518945, baseEnd_518945] using wordTrace_append hprefix tailTrace_518945
  have hstable : (prefixWord ++ tailWord_518945).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518945).length < 2 ^ (prefixWord ++ tailWord_518945).sum := by decide
  have hdescent : baseEnd_518945 < baseStart_518945 := by decide
  rcases family_descends (prefixWord ++ tailWord_518945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518958 : List Nat := [4, 1, 3, 2, 1, 3, 2, 3]
def baseStart_518958 : Nat := 118140960795 + 518958 * 2 ^ 59
def prefixEnd_518958 : Nat := 4983230072969 + 3 ^ 40 * 518958 * 2
def baseEnd_518958 : Nat := 157911047997680478896807

theorem tailTrace_518958 : CollatzResearch.WordTrace tailWord_518958 prefixEnd_518958 157911047997680478896807 := by
  unfold tailWord_518958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365994156738908976904691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12618635502607514543491685 2365994156738908976904691)
  ·
    refine ⟨3548991235108363465357037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2365994156738908976904691 3548991235108363465357037)
    ·
      refine ⟨1330871713165636299508889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3548991235108363465357037 1330871713165636299508889)
      ·
        refine ⟨998153784874227224631667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1330871713165636299508889 998153784874227224631667)
        ·
          refine ⟨1497230677311340836947501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998153784874227224631667 1497230677311340836947501)
          ·
            refine ⟨561461503991752813855313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1497230677311340836947501 561461503991752813855313)
            ·
              refine ⟨421096127993814610391485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561461503991752813855313 421096127993814610391485)
              ·
                refine ⟨157911047997680478896807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421096127993814610391485 157911047997680478896807)
                ·
                  rfl

theorem cell19_518958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_518958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518958 prefixEnd_518958 := by exact prefixLift 518958
  have htrace : WordTrace (prefixWord ++ tailWord_518958) baseStart_518958 baseEnd_518958 := by
    simpa [prefixWord, tailWord_518958, baseEnd_518958] using wordTrace_append hprefix tailTrace_518958
  have hstable : (prefixWord ++ tailWord_518958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518958).length < 2 ^ (prefixWord ++ tailWord_518958).sum := by decide
  have hdescent : baseEnd_518958 < baseStart_518958 := by decide
  rcases family_descends (prefixWord ++ tailWord_518958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518977 : List Nat := [1, 2, 5, 3, 2, 1, 5]
def baseStart_518977 : Nat := 118140960795 + 518977 * 2 ^ 59
def prefixEnd_518977 : Nat := 4983230072969 + 3 ^ 40 * 518977 * 2
def baseEnd_518977 : Nat := 52638943136498021491511

theorem tailTrace_518977 : CollatzResearch.WordTrace tailWord_518977 prefixEnd_518977 52638943136498021491511 := by
  unfold tailWord_518977
  simp only [CollatzResearch.WordTrace]
  refine ⟨18928646240842438060179185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12619097493894958706786123 18928646240842438060179185)
  ·
    refine ⟨14196484680631828545134389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18928646240842438060179185 14196484680631828545134389)
    ·
      refine ⟨1330920438809233926106349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14196484680631828545134389 1330920438809233926106349)
      ·
        refine ⟨499095164553462722289881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1330920438809233926106349 499095164553462722289881)
        ·
          refine ⟨374321373415097041717411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499095164553462722289881 374321373415097041717411)
          ·
            refine ⟨561482060122645562576117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374321373415097041717411 561482060122645562576117)
            ·
              refine ⟨52638943136498021491511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 561482060122645562576117 52638943136498021491511)
              ·
                rfl

theorem cell19_518977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 5].length) (baseStart_518977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_518977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_518977 prefixEnd_518977 := by exact prefixLift 518977
  have htrace : WordTrace (prefixWord ++ tailWord_518977) baseStart_518977 baseEnd_518977 := by
    simpa [prefixWord, tailWord_518977, baseEnd_518977] using wordTrace_append hprefix tailTrace_518977
  have hstable : (prefixWord ++ tailWord_518977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518977).length < 2 ^ (prefixWord ++ tailWord_518977).sum := by decide
  have hdescent : baseEnd_518977 < baseStart_518977 := by decide
  rcases family_descends (prefixWord ++ tailWord_518977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519002 : List Nat := [3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_519002 : Nat := 118140960795 + 519002 * 2 ^ 59
def prefixEnd_519002 : Nat := 4983230072969 + 3 ^ 40 * 519002 * 2
def baseEnd_519002 : Nat := 157924436530301413918909

theorem tailTrace_519002 : CollatzResearch.WordTrace tailWord_519002 prefixEnd_519002 157924436530301413918909 := by
  unfold tailWord_519002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732389516437966832459815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12619705377167911553226173 4732389516437966832459815)
  ·
    refine ⟨7098584274656950248689723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4732389516437966832459815 7098584274656950248689723)
    ·
      refine ⟨10647876411985425373034585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7098584274656950248689723 10647876411985425373034585)
      ·
        refine ⟨7985907308989069029775939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10647876411985425373034585 7985907308989069029775939)
        ·
          refine ⟨11978860963483603544663909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7985907308989069029775939 11978860963483603544663909)
          ·
            refine ⟨2246036430653175664624483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11978860963483603544663909 2246036430653175664624483)
            ·
              refine ⟨3369054645979763496936725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246036430653175664624483 3369054645979763496936725)
              ·
                refine ⟨157924436530301413918909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3369054645979763496936725 157924436530301413918909)
                ·
                  rfl

theorem cell19_519002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_519002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519002 prefixEnd_519002 := by exact prefixLift 519002
  have htrace : WordTrace (prefixWord ++ tailWord_519002) baseStart_519002 baseEnd_519002 := by
    simpa [prefixWord, tailWord_519002, baseEnd_519002] using wordTrace_append hprefix tailTrace_519002
  have hstable : (prefixWord ++ tailWord_519002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519002).length < 2 ^ (prefixWord ++ tailWord_519002).sum := by decide
  have hdescent : baseEnd_519002 < baseStart_519002 := by decide
  rcases family_descends (prefixWord ++ tailWord_519002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519038 : List Nat := [4, 2, 3, 1, 9]
def baseStart_519038 : Nat := 118140960795 + 519038 * 2 ^ 59
def prefixEnd_519038 : Nat := 4983230072969 + 3 ^ 40 * 519038 * 2
def baseEnd_519038 : Nat := 5849458917935703596993

theorem tailTrace_519038 : CollatzResearch.WordTrace tailWord_519038 prefixEnd_519038 5849458917935703596993 := by
  unfold tailWord_519038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366358886702680684768721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12620580729080963652099845 2366358886702680684768721)
  ·
    refine ⟨1774769165027010513576541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2366358886702680684768721 1774769165027010513576541)
    ·
      refine ⟨665538436885128942591203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1774769165027010513576541 665538436885128942591203)
      ·
        refine ⟨998307655327693413886805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665538436885128942591203 998307655327693413886805)
        ·
          refine ⟨5849458917935703596993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 998307655327693413886805 5849458917935703596993)
          ·
            rfl

theorem cell19_519038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 9].length) (baseStart_519038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519038 prefixEnd_519038 := by exact prefixLift 519038
  have htrace : WordTrace (prefixWord ++ tailWord_519038) baseStart_519038 baseEnd_519038 := by
    simpa [prefixWord, tailWord_519038, baseEnd_519038] using wordTrace_append hprefix tailTrace_519038
  have hstable : (prefixWord ++ tailWord_519038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519038).length < 2 ^ (prefixWord ++ tailWord_519038).sum := by decide
  have hdescent : baseEnd_519038 < baseStart_519038 := by decide
  rcases family_descends (prefixWord ++ tailWord_519038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519074 : List Nat := [3, 3, 1, 2, 2, 2, 3, 3]
def baseStart_519074 : Nat := 118140960795 + 519074 * 2 ^ 59
def prefixEnd_519074 : Nat := 4983230072969 + 3 ^ 40 * 519074 * 2
def baseEnd_519074 : Nat := 157946345038226580318713

theorem tailTrace_519074 : CollatzResearch.WordTrace tailWord_519074 prefixEnd_519074 157946345038226580318713 := by
  unfold tailWord_519074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4733046030372755906615069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12621456080994015750973517 4733046030372755906615069)
  ·
    refine ⟨1774892261389783464980651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4733046030372755906615069 1774892261389783464980651)
    ·
      refine ⟨2662338392084675197470977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774892261389783464980651 2662338392084675197470977)
      ·
        refine ⟨1996753794063506398103233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2662338392084675197470977 1996753794063506398103233)
        ·
          refine ⟨1497565345547629798577425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1996753794063506398103233 1497565345547629798577425)
          ·
            refine ⟨1123174009160722348933069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1497565345547629798577425 1123174009160722348933069)
            ·
              refine ⟨421190253435270880849901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123174009160722348933069 421190253435270880849901)
              ·
                refine ⟨157946345038226580318713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421190253435270880849901 157946345038226580318713)
                ·
                  rfl

theorem cell19_519074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_519074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519074 prefixEnd_519074 := by exact prefixLift 519074
  have htrace : WordTrace (prefixWord ++ tailWord_519074) baseStart_519074 baseEnd_519074 := by
    simpa [prefixWord, tailWord_519074, baseEnd_519074] using wordTrace_append hprefix tailTrace_519074
  have hstable : (prefixWord ++ tailWord_519074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519074).length < 2 ^ (prefixWord ++ tailWord_519074).sum := by decide
  have hdescent : baseEnd_519074 < baseStart_519074 := by decide
  rcases family_descends (prefixWord ++ tailWord_519074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519076 : List Nat := [2, 3, 1, 2, 1, 2, 5, 3]
def baseStart_519076 : Nat := 118140960795 + 519076 * 2 ^ 59
def prefixEnd_519076 : Nat := 4983230072969 + 3 ^ 40 * 519076 * 2
def baseEnd_519076 : Nat := 157946953607891168274263

theorem tailTrace_519076 : CollatzResearch.WordTrace tailWord_519076 prefixEnd_519076 157946953607891168274263 := by
  unfold tailWord_519076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9466128533741888984016541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12621504711655851978688721 9466128533741888984016541)
  ·
    refine ⟨3549798200153208369006203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9466128533741888984016541 3549798200153208369006203)
    ·
      refine ⟨5324697300229812553509305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549798200153208369006203 5324697300229812553509305)
      ·
        refine ⟨3993522975172359415131979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5324697300229812553509305 3993522975172359415131979)
        ·
          refine ⟨5990284462758539122697969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993522975172359415131979 5990284462758539122697969)
          ·
            refine ⟨4492713347068904342023477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5990284462758539122697969 4492713347068904342023477)
            ·
              refine ⟨421191876287709782064701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4492713347068904342023477 421191876287709782064701)
              ·
                refine ⟨157946953607891168274263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421191876287709782064701 157946953607891168274263)
                ·
                  rfl

theorem cell19_519076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_519076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519076 prefixEnd_519076 := by exact prefixLift 519076
  have htrace : WordTrace (prefixWord ++ tailWord_519076) baseStart_519076 baseEnd_519076 := by
    simpa [prefixWord, tailWord_519076, baseEnd_519076] using wordTrace_append hprefix tailTrace_519076
  have hstable : (prefixWord ++ tailWord_519076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519076).length < 2 ^ (prefixWord ++ tailWord_519076).sum := by decide
  have hdescent : baseEnd_519076 < baseStart_519076 := by decide
  rcases family_descends (prefixWord ++ tailWord_519076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519097 : List Nat := [1, 2, 1, 4, 2, 3, 6]
def baseStart_519097 : Nat := 118140960795 + 519097 * 2 ^ 59
def prefixEnd_519097 : Nat := 4983230072969 + 3 ^ 40 * 519097 * 2
def baseEnd_519097 : Nat := 52651114529789780602513

theorem tailTrace_519097 : CollatzResearch.WordTrace tailWord_519097 prefixEnd_519097 52651114529789780602513 := by
  unfold tailWord_519097
  simp only [CollatzResearch.WordTrace]
  refine ⟨18933023000407698554547545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12622015333605132369698363 18933023000407698554547545)
  ·
    refine ⟨14199767250305773915910659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18933023000407698554547545 14199767250305773915910659)
    ·
      refine ⟨21299650875458660873865989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14199767250305773915910659 21299650875458660873865989)
      ·
        refine ⟨3993684539148498913849873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21299650875458660873865989 3993684539148498913849873)
        ·
          refine ⟨2995263404361374185387405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3993684539148498913849873 2995263404361374185387405)
          ·
            refine ⟨1123223776635515319520277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2995263404361374185387405 1123223776635515319520277)
            ·
              refine ⟨52651114529789780602513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1123223776635515319520277 52651114529789780602513)
              ·
                rfl

theorem cell19_519097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_519097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519097 prefixEnd_519097 := by exact prefixLift 519097
  have htrace : WordTrace (prefixWord ++ tailWord_519097) baseStart_519097 baseEnd_519097 := by
    simpa [prefixWord, tailWord_519097, baseEnd_519097] using wordTrace_append hprefix tailTrace_519097
  have hstable : (prefixWord ++ tailWord_519097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519097).length < 2 ^ (prefixWord ++ tailWord_519097).sum := by decide
  have hdescent : baseEnd_519097 < baseStart_519097 := by decide
  rcases family_descends (prefixWord ++ tailWord_519097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519116 : List Nat := [2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_519116 : Nat := 118140960795 + 519116 * 2 ^ 59
def prefixEnd_519116 : Nat := 4983230072969 + 3 ^ 40 * 519116 * 2
def baseEnd_519116 : Nat := 157959125001182927385265

theorem tailTrace_519116 : CollatzResearch.WordTrace tailWord_519116 prefixEnd_519116 157959125001182927385265 := by
  unfold tailWord_519116
  simp only [CollatzResearch.WordTrace]
  refine ⟨9466857993669432399744601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12622477324892576532992801 9466857993669432399744601)
  ·
    refine ⟨7100143495252074299808451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9466857993669432399744601 7100143495252074299808451)
    ·
      refine ⟨10650215242878111449712677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7100143495252074299808451 10650215242878111449712677)
      ·
        refine ⟨1996915358039645896821127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10650215242878111449712677 1996915358039645896821127)
        ·
          refine ⟨2995373037059468845231691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996915358039645896821127 2995373037059468845231691)
          ·
            refine ⟨4493059555589203267847537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995373037059468845231691 4493059555589203267847537)
            ·
              refine ⟨3369794666691902450885653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4493059555589203267847537 3369794666691902450885653)
              ·
                refine ⟨157959125001182927385265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3369794666691902450885653 157959125001182927385265)
                ·
                  rfl

theorem cell19_519116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_519116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519116 prefixEnd_519116 := by exact prefixLift 519116
  have htrace : WordTrace (prefixWord ++ tailWord_519116) baseStart_519116 baseEnd_519116 := by
    simpa [prefixWord, tailWord_519116, baseEnd_519116] using wordTrace_append hprefix tailTrace_519116
  have hstable : (prefixWord ++ tailWord_519116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519116).length < 2 ^ (prefixWord ++ tailWord_519116).sum := by decide
  have hdescent : baseEnd_519116 < baseStart_519116 := by decide
  rcases family_descends (prefixWord ++ tailWord_519116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519133 : List Nat := [1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_519133 : Nat := 118140960795 + 519133 * 2 ^ 59
def prefixEnd_519133 : Nat := 4983230072969 + 3 ^ 40 * 519133 * 2
def baseEnd_519133 : Nat := 157964297843331925007441

theorem tailTrace_519133 : CollatzResearch.WordTrace tailWord_519133 prefixEnd_519133 157964297843331925007441 := by
  unfold tailWord_519133
  simp only [CollatzResearch.WordTrace]
  refine ⟨18934336028277276702858053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12622890685518184468572035 18934336028277276702858053)
  ·
    refine ⟨3550188005301989381785885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18934336028277276702858053 3550188005301989381785885)
    ·
      refine ⟨1331320501988246018169707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3550188005301989381785885 1331320501988246018169707)
      ·
        refine ⟨1996980752982369027254561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331320501988246018169707 1996980752982369027254561)
        ·
          refine ⟨1497735564736776770440921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1996980752982369027254561 1497735564736776770440921)
          ·
            refine ⟨1123301673552582577830691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1497735564736776770440921 1123301673552582577830691)
            ·
              refine ⟨1684952510328873866746037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123301673552582577830691 1684952510328873866746037)
              ·
                refine ⟨157964297843331925007441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1684952510328873866746037 157964297843331925007441)
                ·
                  rfl

theorem cell19_519133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_519133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519133 prefixEnd_519133 := by exact prefixLift 519133
  have htrace : WordTrace (prefixWord ++ tailWord_519133) baseStart_519133 baseEnd_519133 := by
    simpa [prefixWord, tailWord_519133, baseEnd_519133] using wordTrace_append hprefix tailTrace_519133
  have hstable : (prefixWord ++ tailWord_519133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519133).length < 2 ^ (prefixWord ++ tailWord_519133).sum := by decide
  have hdescent : baseEnd_519133 < baseStart_519133 := by decide
  rcases family_descends (prefixWord ++ tailWord_519133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519150 : List Nat := [4, 1, 2, 1, 5, 1, 5]
def baseStart_519150 : Nat := 118140960795 + 519150 * 2 ^ 59
def prefixEnd_519150 : Nat := 4983230072969 + 3 ^ 40 * 519150 * 2
def baseEnd_519150 : Nat := 52656490228493640876539

theorem tailTrace_519150 : CollatzResearch.WordTrace tailWord_519150 prefixEnd_519150 52656490228493640876539 := by
  unfold tailWord_519150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366869508651961075778363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12623304046143792404151269 2366869508651961075778363)
  ·
    refine ⟨3550304262977941613667545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2366869508651961075778363 3550304262977941613667545)
    ·
      refine ⟨2662728197233456210250659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3550304262977941613667545 2662728197233456210250659)
      ·
        refine ⟨3994092295850184315375989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662728197233456210250659 3994092295850184315375989)
        ·
          refine ⟨374446152735954779566499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3994092295850184315375989 374446152735954779566499)
          ·
            refine ⟨561669229103932169349749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374446152735954779566499 561669229103932169349749)
            ·
              refine ⟨52656490228493640876539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 561669229103932169349749 52656490228493640876539)
              ·
                rfl

theorem cell19_519150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 5].length) (baseStart_519150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519150 prefixEnd_519150 := by exact prefixLift 519150
  have htrace : WordTrace (prefixWord ++ tailWord_519150) baseStart_519150 baseEnd_519150 := by
    simpa [prefixWord, tailWord_519150, baseEnd_519150] using wordTrace_append hprefix tailTrace_519150
  have hstable : (prefixWord ++ tailWord_519150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519150).length < 2 ^ (prefixWord ++ tailWord_519150).sum := by decide
  have hdescent : baseEnd_519150 < baseStart_519150 := by decide
  rcases family_descends (prefixWord ++ tailWord_519150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519173 : List Nat := [1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_519173 : Nat := 118140960795 + 519173 * 2 ^ 59
def prefixEnd_519173 : Nat := 4983230072969 + 3 ^ 40 * 519173 * 2
def baseEnd_519173 : Nat := 157976469236623684118443

theorem tailTrace_519173 : CollatzResearch.WordTrace tailWord_519173 prefixEnd_519173 157976469236623684118443 := by
  unfold tailWord_519173
  simp only [CollatzResearch.WordTrace]
  refine ⟨18935794948132363534314173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12623863298754909022876115 18935794948132363534314173)
  ·
    refine ⟨7100923105549636325367815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18935794948132363534314173 7100923105549636325367815)
    ·
      refine ⟨10651384658324454488051723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7100923105549636325367815 10651384658324454488051723)
      ·
        refine ⟨15977076987486681732077585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10651384658324454488051723 15977076987486681732077585)
        ·
          refine ⟨11982807740615011299058189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15977076987486681732077585 11982807740615011299058189)
          ·
            refine ⟨4493552902730629237146821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11982807740615011299058189 4493552902730629237146821)
            ·
              refine ⟨842541169261992981965029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4493552902730629237146821 842541169261992981965029)
              ·
                refine ⟨157976469236623684118443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 842541169261992981965029 157976469236623684118443)
                ·
                  rfl

theorem cell19_519173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_519173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519173 prefixEnd_519173 := by exact prefixLift 519173
  have htrace : WordTrace (prefixWord ++ tailWord_519173) baseStart_519173 baseEnd_519173 := by
    simpa [prefixWord, tailWord_519173, baseEnd_519173] using wordTrace_append hprefix tailTrace_519173
  have hstable : (prefixWord ++ tailWord_519173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519173).length < 2 ^ (prefixWord ++ tailWord_519173).sum := by decide
  have hdescent : baseEnd_519173 < baseStart_519173 := by decide
  rcases family_descends (prefixWord ++ tailWord_519173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519192 : List Nat := [2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_519192 : Nat := 118140960795 + 519192 * 2 ^ 59
def prefixEnd_519192 : Nat := 4983230072969 + 3 ^ 40 * 519192 * 2
def baseEnd_519192 : Nat := 157982250648437269696169

theorem tailTrace_519192 : CollatzResearch.WordTrace tailWord_519192 prefixEnd_519192 157982250648437269696169 := by
  unfold tailWord_519192
  simp only [CollatzResearch.WordTrace]
  refine ⟨9468243967531764889627915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12624325290042353186170553 9468243967531764889627915)
  ·
    refine ⟨14202365951297647334441873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9468243967531764889627915 14202365951297647334441873)
    ·
      refine ⟨10651774463473235500831405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14202365951297647334441873 10651774463473235500831405)
      ·
        refine ⟨3994415423802463312811777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10651774463473235500831405 3994415423802463312811777)
        ·
          refine ⟨2995811567851847484608833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3994415423802463312811777 2995811567851847484608833)
          ·
            refine ⟨2246858675888885613456625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2995811567851847484608833 2246858675888885613456625)
            ·
              refine ⟨1685144006916664210092469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246858675888885613456625 1685144006916664210092469)
              ·
                refine ⟨157982250648437269696169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1685144006916664210092469 157982250648437269696169)
                ·
                  rfl

theorem cell19_519192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_519192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519192 prefixEnd_519192 := by exact prefixLift 519192
  have htrace : WordTrace (prefixWord ++ tailWord_519192) baseStart_519192 baseEnd_519192 := by
    simpa [prefixWord, tailWord_519192, baseEnd_519192] using wordTrace_append hprefix tailTrace_519192
  have hstable : (prefixWord ++ tailWord_519192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519192).length < 2 ^ (prefixWord ++ tailWord_519192).sum := by decide
  have hdescent : baseEnd_519192 < baseStart_519192 := by decide
  rcases family_descends (prefixWord ++ tailWord_519192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519228 : List Nat := [2, 2, 2, 2, 2, 4, 1, 4]
def baseStart_519228 : Nat := 118140960795 + 519228 * 2 ^ 59
def prefixEnd_519228 : Nat := 4983230072969 + 3 ^ 40 * 519228 * 2
def baseEnd_519228 : Nat := 157993204902399852896071

theorem tailTrace_519228 : CollatzResearch.WordTrace tailWord_519228 prefixEnd_519228 157993204902399852896071 := by
  unfold tailWord_519228
  simp only [CollatzResearch.WordTrace]
  refine ⟨9468900481466553963783169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12625200641955405285044225 9468900481466553963783169)
  ·
    refine ⟨7101675361099915472837377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9468900481466553963783169 7101675361099915472837377)
    ·
      refine ⟨5326256520824936604628033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7101675361099915472837377 5326256520824936604628033)
      ·
        refine ⟨3994692390618702453471025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5326256520824936604628033 3994692390618702453471025)
        ·
          refine ⟨2996019292964026840103269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3994692390618702453471025 2996019292964026840103269)
          ·
            refine ⟨561753617430755032519363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2996019292964026840103269 561753617430755032519363)
            ·
              refine ⟨842630426146132548779045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561753617430755032519363 842630426146132548779045)
              ·
                refine ⟨157993204902399852896071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 842630426146132548779045 157993204902399852896071)
                ·
                  rfl

theorem cell19_519228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_519228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519228 prefixEnd_519228 := by exact prefixLift 519228
  have htrace : WordTrace (prefixWord ++ tailWord_519228) baseStart_519228 baseEnd_519228 := by
    simpa [prefixWord, tailWord_519228, baseEnd_519228] using wordTrace_append hprefix tailTrace_519228
  have hstable : (prefixWord ++ tailWord_519228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519228).length < 2 ^ (prefixWord ++ tailWord_519228).sum := by decide
  have hdescent : baseEnd_519228 < baseStart_519228 := by decide
  rcases family_descends (prefixWord ++ tailWord_519228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519245 : List Nat := [1, 6, 1, 1, 1, 3, 3, 3]
def baseStart_519245 : Nat := 118140960795 + 519245 * 2 ^ 59
def prefixEnd_519245 : Nat := 4983230072969 + 3 ^ 40 * 519245 * 2
def baseEnd_519245 : Nat := 157998377744548850518247

theorem tailTrace_519245 : CollatzResearch.WordTrace tailWord_519245 prefixEnd_519245 157998377744548850518247 := by
  unfold tailWord_519245
  simp only [CollatzResearch.WordTrace]
  refine ⟨18938421003871519830935189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12625614002581013220623459 18938421003871519830935189)
  ·
    refine ⟨887738484556477492075087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18938421003871519830935189 887738484556477492075087)
    ·
      refine ⟨1331607726834716238112631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 887738484556477492075087 1331607726834716238112631)
      ·
        refine ⟨1997411590252074357168947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331607726834716238112631 1997411590252074357168947)
        ·
          refine ⟨2996117385378111535753421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997411590252074357168947 2996117385378111535753421)
          ·
            refine ⟨1123544019516791825907533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2996117385378111535753421 1123544019516791825907533)
            ·
              refine ⟨421329007318796934715325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123544019516791825907533 421329007318796934715325)
              ·
                refine ⟨157998377744548850518247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421329007318796934715325 157998377744548850518247)
                ·
                  rfl

theorem cell19_519245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 3].length) (baseStart_519245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519245 prefixEnd_519245 := by exact prefixLift 519245
  have htrace : WordTrace (prefixWord ++ tailWord_519245) baseStart_519245 baseEnd_519245 := by
    simpa [prefixWord, tailWord_519245, baseEnd_519245] using wordTrace_append hprefix tailTrace_519245
  have hstable : (prefixWord ++ tailWord_519245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519245).length < 2 ^ (prefixWord ++ tailWord_519245).sum := by decide
  have hdescent : baseEnd_519245 < baseStart_519245 := by decide
  rcases family_descends (prefixWord ++ tailWord_519245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519266 : List Nat := [3, 3, 2, 2, 1, 2, 6]
def baseStart_519266 : Nat := 118140960795 + 519266 * 2 ^ 59
def prefixEnd_519266 : Nat := 4983230072969 + 3 ^ 40 * 519266 * 2
def baseEnd_519266 : Nat := 52668255908675674683841

theorem tailTrace_519266 : CollatzResearch.WordTrace tailWord_519266 prefixEnd_519266 52668255908675674683841 := by
  unfold tailWord_519266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4734796734198860104362413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12626124624530293611633101 4734796734198860104362413)
  ·
    refine ⟨1775548775324572539135905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4734796734198860104362413 1775548775324572539135905)
    ·
      refine ⟨1331661581493429404351929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1775548775324572539135905 1331661581493429404351929)
      ·
        refine ⟨998746186120072053263947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1331661581493429404351929 998746186120072053263947)
        ·
          refine ⟨1498119279180108079895921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998746186120072053263947 1498119279180108079895921)
          ·
            refine ⟨1123589459385081059921941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498119279180108079895921 1123589459385081059921941)
            ·
              refine ⟨52668255908675674683841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1123589459385081059921941 52668255908675674683841)
              ·
                rfl

theorem cell19_519266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_519266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519266 prefixEnd_519266 := by exact prefixLift 519266
  have htrace : WordTrace (prefixWord ++ tailWord_519266) baseStart_519266 baseEnd_519266 := by
    simpa [prefixWord, tailWord_519266, baseEnd_519266] using wordTrace_append hprefix tailTrace_519266
  have hstable : (prefixWord ++ tailWord_519266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519266).length < 2 ^ (prefixWord ++ tailWord_519266).sum := by decide
  have hdescent : baseEnd_519266 < baseStart_519266 := by decide
  rcases family_descends (prefixWord ++ tailWord_519266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519304 : List Nat := [2, 1, 3, 4, 2, 1, 1, 5]
def baseStart_519304 : Nat := 118140960795 + 519304 * 2 ^ 59
def prefixEnd_519304 : Nat := 4983230072969 + 3 ^ 40 * 519304 * 2
def baseEnd_519304 : Nat := 158016330549654195206975

theorem tailTrace_519304 : CollatzResearch.WordTrace tailWord_519304 prefixEnd_519304 158016330549654195206975 := by
  unfold tailWord_519304
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470286455328886453666483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12627048607105181938221977 9470286455328886453666483)
  ·
    refine ⟨14205429682993329680499725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9470286455328886453666483 14205429682993329680499725)
    ·
      refine ⟨5327036131122498630187397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14205429682993329680499725 5327036131122498630187397)
      ·
        refine ⟨998819274585468493160137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5327036131122498630187397 998819274585468493160137)
        ·
          refine ⟨749114455939101369870103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998819274585468493160137 749114455939101369870103)
          ·
            refine ⟨1123671683908652054805155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749114455939101369870103 1123671683908652054805155)
            ·
              refine ⟨1685507525862978082207733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123671683908652054805155 1685507525862978082207733)
              ·
                refine ⟨158016330549654195206975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1685507525862978082207733 158016330549654195206975)
                ·
                  rfl

theorem cell19_519304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_519304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519304 prefixEnd_519304 := by exact prefixLift 519304
  have htrace : WordTrace (prefixWord ++ tailWord_519304) baseStart_519304 baseEnd_519304 := by
    simpa [prefixWord, tailWord_519304, baseEnd_519304] using wordTrace_append hprefix tailTrace_519304
  have hstable : (prefixWord ++ tailWord_519304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519304).length < 2 ^ (prefixWord ++ tailWord_519304).sum := by decide
  have hdescent : baseEnd_519304 < baseStart_519304 := by decide
  rcases family_descends (prefixWord ++ tailWord_519304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519306 : List Nat := [3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_519306 : Nat := 118140960795 + 519306 * 2 ^ 59
def prefixEnd_519306 : Nat := 4983230072969 + 3 ^ 40 * 519306 * 2
def baseEnd_519306 : Nat := 158016939119318783162525

theorem tailTrace_519306 : CollatzResearch.WordTrace tailWord_519306 prefixEnd_519306 158016939119318783162525 := by
  unfold tailWord_519306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735161464162631812226443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12627097237767018165937181 4735161464162631812226443)
  ·
    refine ⟨7102742196243947718339665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4735161464162631812226443 7102742196243947718339665)
    ·
      refine ⟨5327056647182960788754749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7102742196243947718339665 5327056647182960788754749)
      ·
        refine ⟨1997646242693610295783031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5327056647182960788754749 1997646242693610295783031)
        ·
          refine ⟨2996469364040415443674547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997646242693610295783031 2996469364040415443674547)
          ·
            refine ⟨4494704046060623165511821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996469364040415443674547 4494704046060623165511821)
            ·
              refine ⟨1685514017272733687066933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4494704046060623165511821 1685514017272733687066933)
              ·
                refine ⟨158016939119318783162525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1685514017272733687066933 158016939119318783162525)
                ·
                  rfl

theorem cell19_519306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_519306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519306 prefixEnd_519306 := by exact prefixLift 519306
  have htrace : WordTrace (prefixWord ++ tailWord_519306) baseStart_519306 baseEnd_519306 := by
    simpa [prefixWord, tailWord_519306, baseEnd_519306] using wordTrace_append hprefix tailTrace_519306
  have hstable : (prefixWord ++ tailWord_519306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519306).length < 2 ^ (prefixWord ++ tailWord_519306).sum := by decide
  have hdescent : baseEnd_519306 < baseStart_519306 := by decide
  rcases family_descends (prefixWord ++ tailWord_519306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519361 : List Nat := [1, 2, 6, 1, 1, 1, 2, 5]
def baseStart_519361 : Nat := 118140960795 + 519361 * 2 ^ 59
def prefixEnd_519361 : Nat := 4983230072969 + 3 ^ 40 * 519361 * 2
def baseEnd_519361 : Nat := 158033674785094951940153

theorem tailTrace_519361 : CollatzResearch.WordTrace tailWord_519361 prefixEnd_519361 158033674785094951940153 := by
  unfold tailWord_519361
  simp only [CollatzResearch.WordTrace]
  refine ⟨18942651871451271642157937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12628434580967514428105291 18942651871451271642157937)
  ·
    refine ⟨14206988903588453731618453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18942651871451271642157937 14206988903588453731618453)
    ·
      refine ⟨665952604855708768669615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14206988903588453731618453 665952604855708768669615)
      ·
        refine ⟨998928907283563153004423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665952604855708768669615 998928907283563153004423)
        ·
          refine ⟨1498393360925344729506635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998928907283563153004423 1498393360925344729506635)
          ·
            refine ⟨2247590041388017094259953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498393360925344729506635 2247590041388017094259953)
            ·
              refine ⟨1685692531041012820694965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2247590041388017094259953 1685692531041012820694965)
              ·
                refine ⟨158033674785094951940153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1685692531041012820694965 158033674785094951940153)
                ·
                  rfl

theorem cell19_519361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_519361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519361 prefixEnd_519361 := by exact prefixLift 519361
  have htrace : WordTrace (prefixWord ++ tailWord_519361) baseStart_519361 baseEnd_519361 := by
    simpa [prefixWord, tailWord_519361, baseEnd_519361] using wordTrace_append hprefix tailTrace_519361
  have hstable : (prefixWord ++ tailWord_519361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519361).length < 2 ^ (prefixWord ++ tailWord_519361).sum := by decide
  have hdescent : baseEnd_519361 < baseStart_519361 := by decide
  rcases family_descends (prefixWord ++ tailWord_519361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519380 : List Nat := [2, 4, 1, 4, 1, 7]
def baseStart_519380 : Nat := 118140960795 + 519380 * 2 ^ 59
def prefixEnd_519380 : Nat := 4983230072969 + 3 ^ 40 * 519380 * 2
def baseEnd_519380 : Nat := 17559939577434281946431

theorem tailTrace_519380 : CollatzResearch.WordTrace tailWord_519380 prefixEnd_519380 17559939577434281946431 := by
  unfold tailWord_519380
  simp only [CollatzResearch.WordTrace]
  refine ⟨9471672429191218943549797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12628896572254958591399729 9471672429191218943549797)
  ·
    refine ⟨1775938580473353551915587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9471672429191218943549797 1775938580473353551915587)
    ·
      refine ⟨2663907870710030327873381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775938580473353551915587 2663907870710030327873381)
      ·
        refine ⟨499482725758130686476259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2663907870710030327873381 499482725758130686476259)
        ·
          refine ⟨749224088637196029714389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499482725758130686476259 749224088637196029714389)
          ·
            refine ⟨17559939577434281946431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 749224088637196029714389 17559939577434281946431)
            ·
              rfl

theorem cell19_519380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 7].length) (baseStart_519380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519380 prefixEnd_519380 := by exact prefixLift 519380
  have htrace : WordTrace (prefixWord ++ tailWord_519380) baseStart_519380 baseEnd_519380 := by
    simpa [prefixWord, tailWord_519380, baseEnd_519380] using wordTrace_append hprefix tailTrace_519380
  have hstable : (prefixWord ++ tailWord_519380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519380).length < 2 ^ (prefixWord ++ tailWord_519380).sum := by decide
  have hdescent : baseEnd_519380 < baseStart_519380 := by decide
  rcases family_descends (prefixWord ++ tailWord_519380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519384 : List Nat := [2, 1, 2, 2, 12]
def baseStart_519384 : Nat := 118140960795 + 519384 * 2 ^ 59
def prefixEnd_519384 : Nat := 4983230072969 + 3 ^ 40 * 519384 * 2
def baseEnd_519384 : Nat := 5853358271712507904777

theorem tailTrace_519384 : CollatzResearch.WordTrace tailWord_519384 prefixEnd_519384 5853358271712507904777 := by
  unfold tailWord_519384
  simp only [CollatzResearch.WordTrace]
  refine ⟨9471745375183973285122603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12628993833578631046830137 9471745375183973285122603)
  ·
    refine ⟨14207618062775959927683905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9471745375183973285122603 14207618062775959927683905)
    ·
      refine ⟨10655713547081969945762929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14207618062775959927683905 10655713547081969945762929)
      ·
        refine ⟨7991785160311477459322197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10655713547081969945762929 7991785160311477459322197)
        ·
          refine ⟨5853358271712507904777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7991785160311477459322197 5853358271712507904777)
          ·
            rfl

theorem cell19_519384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 12].length) (baseStart_519384 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519384 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519384 prefixEnd_519384 := by exact prefixLift 519384
  have htrace : WordTrace (prefixWord ++ tailWord_519384) baseStart_519384 baseEnd_519384 := by
    simpa [prefixWord, tailWord_519384, baseEnd_519384] using wordTrace_append hprefix tailTrace_519384
  have hstable : (prefixWord ++ tailWord_519384).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519384).length < 2 ^ (prefixWord ++ tailWord_519384).sum := by decide
  have hdescent : baseEnd_519384 < baseStart_519384 := by decide
  rcases family_descends (prefixWord ++ tailWord_519384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519397 : List Nat := [1, 3, 1, 4, 4, 1, 1, 4]
def baseStart_519397 : Nat := 118140960795 + 519397 * 2 ^ 59
def prefixEnd_519397 : Nat := 4983230072969 + 3 ^ 40 * 519397 * 2
def baseEnd_519397 : Nat := 158044629039057535140055

theorem tailTrace_519397 : CollatzResearch.WordTrace tailWord_519397 prefixEnd_519397 158044629039057535140055 := by
  unfold tailWord_519397
  simp only [CollatzResearch.WordTrace]
  refine ⟨18943964899320849790468445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12629309932880566526978963 18943964899320849790468445)
  ·
    refine ⟨7103986837245318671425667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18943964899320849790468445 7103986837245318671425667)
    ·
      refine ⟨10655980255867978007138501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7103986837245318671425667 10655980255867978007138501)
      ·
        refine ⟨1997996297975245876338469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10655980255867978007138501 1997996297975245876338469)
        ·
          refine ⟨374624305870358601813463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1997996297975245876338469 374624305870358601813463)
          ·
            refine ⟨561936458805537902720195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374624305870358601813463 561936458805537902720195)
            ·
              refine ⟨842904688208306854080293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561936458805537902720195 842904688208306854080293)
              ·
                refine ⟨158044629039057535140055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 842904688208306854080293 158044629039057535140055)
                ·
                  rfl

theorem cell19_519397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 4].length) (baseStart_519397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519397 prefixEnd_519397 := by exact prefixLift 519397
  have htrace : WordTrace (prefixWord ++ tailWord_519397) baseStart_519397 baseEnd_519397 := by
    simpa [prefixWord, tailWord_519397, baseEnd_519397] using wordTrace_append hprefix tailTrace_519397
  have hstable : (prefixWord ++ tailWord_519397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519397).length < 2 ^ (prefixWord ++ tailWord_519397).sum := by decide
  have hdescent : baseEnd_519397 < baseStart_519397 := by decide
  rcases family_descends (prefixWord ++ tailWord_519397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519412 : List Nat := [2, 6, 1, 2, 1, 1, 3, 3]
def baseStart_519412 : Nat := 118140960795 + 519412 * 2 ^ 59
def prefixEnd_519412 : Nat := 4983230072969 + 3 ^ 40 * 519412 * 2
def baseEnd_519412 : Nat := 158049193311541944806681

theorem tailTrace_519412 : CollatzResearch.WordTrace tailWord_519412 prefixEnd_519412 158049193311541944806681 := by
  unfold tailWord_519412
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472255997133253676132245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12629674662844338234842993 9472255997133253676132245)
  ·
    refine ⟨444011999865621266068699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9472255997133253676132245 444011999865621266068699)
    ·
      refine ⟨666017999798431899103049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444011999865621266068699 666017999798431899103049)
      ·
        refine ⟨499513499848823924327287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666017999798431899103049 499513499848823924327287)
        ·
          refine ⟨749270249773235886490931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499513499848823924327287 749270249773235886490931)
          ·
            refine ⟨1123905374659853829736397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749270249773235886490931 1123905374659853829736397)
            ·
              refine ⟨421464515497445186151149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123905374659853829736397 421464515497445186151149)
              ·
                refine ⟨158049193311541944806681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421464515497445186151149 158049193311541944806681)
                ·
                  rfl

theorem cell19_519412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_519412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519412 prefixEnd_519412 := by exact prefixLift 519412
  have htrace : WordTrace (prefixWord ++ tailWord_519412) baseStart_519412 baseEnd_519412 := by
    simpa [prefixWord, tailWord_519412, baseEnd_519412] using wordTrace_append hprefix tailTrace_519412
  have hstable : (prefixWord ++ tailWord_519412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519412).length < 2 ^ (prefixWord ++ tailWord_519412).sum := by decide
  have hdescent : baseEnd_519412 < baseStart_519412 := by decide
  rcases family_descends (prefixWord ++ tailWord_519412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519441 : List Nat := [1, 2, 2, 1, 1, 4, 8]
def baseStart_519441 : Nat := 118140960795 + 519441 * 2 ^ 59
def prefixEnd_519441 : Nat := 4983230072969 + 3 ^ 40 * 519441 * 2
def baseEnd_519441 : Nat := 52686005857226156720719

theorem tailTrace_519441 : CollatzResearch.WordTrace tailWord_519441 prefixEnd_519441 52686005857226156720719 := by
  unfold tailWord_519441
  simp only [CollatzResearch.WordTrace]
  refine ⟨18945569711161445305070177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12630379807440963536713451 18945569711161445305070177)
  ·
    refine ⟨14209177283371083978802633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18945569711161445305070177 14209177283371083978802633)
    ·
      refine ⟨10656882962528312984101975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14209177283371083978802633 10656882962528312984101975)
      ·
        refine ⟨15985324443792469476152963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10656882962528312984101975 15985324443792469476152963)
        ·
          refine ⟨23977986665688704214229445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15985324443792469476152963 23977986665688704214229445)
          ·
            refine ⟨4495872499816632040168021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23977986665688704214229445 4495872499816632040168021)
            ·
              refine ⟨52686005857226156720719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4495872499816632040168021 52686005857226156720719)
              ·
                rfl

theorem cell19_519441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_519441 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519441 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519441 prefixEnd_519441 := by exact prefixLift 519441
  have htrace : WordTrace (prefixWord ++ tailWord_519441) baseStart_519441 baseEnd_519441 := by
    simpa [prefixWord, tailWord_519441, baseEnd_519441] using wordTrace_append hprefix tailTrace_519441
  have hstable : (prefixWord ++ tailWord_519441).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519441).length < 2 ^ (prefixWord ++ tailWord_519441).sum := by decide
  have hdescent : baseEnd_519441 < baseStart_519441 := by decide
  rcases family_descends (prefixWord ++ tailWord_519441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519475 : List Nat := [1, 1, 1, 2, 5, 4, 2, 3]
def baseStart_519475 : Nat := 118140960795 + 519475 * 2 ^ 59
def prefixEnd_519475 : Nat := 4983230072969 + 3 ^ 40 * 519475 * 2
def baseEnd_519475 : Nat := 158068363255976465406509

theorem tailTrace_519475 : CollatzResearch.WordTrace tailWord_519475 prefixEnd_519475 158068363255976465406509 := by
  unfold tailWord_519475
  simp only [CollatzResearch.WordTrace]
  refine ⟨18946809793038269111807879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12631206528692179407871919 18946809793038269111807879)
  ·
    refine ⟨28420214689557403667711819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18946809793038269111807879 28420214689557403667711819)
    ·
      refine ⟨42630322034336105501567729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28420214689557403667711819 42630322034336105501567729)
      ·
        refine ⟨31972741525752079126175797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42630322034336105501567729 31972741525752079126175797)
        ·
          refine ⟨2997444518039257418078981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31972741525752079126175797 2997444518039257418078981)
          ·
            refine ⟨562020847132360765889809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2997444518039257418078981 562020847132360765889809)
            ·
              refine ⟨421515635349270574417357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562020847132360765889809 421515635349270574417357)
              ·
                refine ⟨158068363255976465406509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421515635349270574417357 158068363255976465406509)
                ·
                  rfl

theorem cell19_519475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 3].length) (baseStart_519475 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519475 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519475 prefixEnd_519475 := by exact prefixLift 519475
  have htrace : WordTrace (prefixWord ++ tailWord_519475) baseStart_519475 baseEnd_519475 := by
    simpa [prefixWord, tailWord_519475, baseEnd_519475] using wordTrace_append hprefix tailTrace_519475
  have hstable : (prefixWord ++ tailWord_519475).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519475).length < 2 ^ (prefixWord ++ tailWord_519475).sum := by decide
  have hdescent : baseEnd_519475 < baseStart_519475 := by decide
  rcases family_descends (prefixWord ++ tailWord_519475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519477 : List Nat := [1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_519477 : Nat := 118140960795 + 519477 * 2 ^ 59
def prefixEnd_519477 : Nat := 4983230072969 + 3 ^ 40 * 519477 * 2
def baseEnd_519477 : Nat := 158068971825641053362059

theorem tailTrace_519477 : CollatzResearch.WordTrace tailWord_519477 prefixEnd_519477 158068971825641053362059 := by
  unfold tailWord_519477
  simp only [CollatzResearch.WordTrace]
  refine ⟨18946882739031023453380685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12631255159354015635587123 18946882739031023453380685)
  ·
    refine ⟨7105081027136633795017757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18946882739031023453380685 7105081027136633795017757)
    ·
      refine ⟨2664405385176237673131659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7105081027136633795017757 2664405385176237673131659)
      ·
        refine ⟨3996608077764356509697489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664405385176237673131659 3996608077764356509697489)
        ·
          refine ⟨2997456058323267382273117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3996608077764356509697489 2997456058323267382273117)
          ·
            refine ⟨1124046021871225268352419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2997456058323267382273117 1124046021871225268352419)
            ·
              refine ⟨1686069032806837902528629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124046021871225268352419 1686069032806837902528629)
              ·
                refine ⟨158068971825641053362059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1686069032806837902528629 158068971825641053362059)
                ·
                  rfl

theorem cell19_519477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_519477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519477 prefixEnd_519477 := by exact prefixLift 519477
  have htrace : WordTrace (prefixWord ++ tailWord_519477) baseStart_519477 baseEnd_519477 := by
    simpa [prefixWord, tailWord_519477, baseEnd_519477] using wordTrace_append hprefix tailTrace_519477
  have hstable : (prefixWord ++ tailWord_519477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519477).length < 2 ^ (prefixWord ++ tailWord_519477).sum := by decide
  have hdescent : baseEnd_519477 < baseStart_519477 := by decide
  rcases family_descends (prefixWord ++ tailWord_519477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519536 : List Nat := [2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_519536 : Nat := 118140960795 + 519536 * 2 ^ 59
def prefixEnd_519536 : Nat := 4983230072969 + 3 ^ 40 * 519536 * 2
def baseEnd_519536 : Nat := 158086924630746398050787

theorem tailTrace_519536 : CollatzResearch.WordTrace tailWord_519536 prefixEnd_519536 158086924630746398050787 := by
  unfold tailWord_519536
  simp only [CollatzResearch.WordTrace]
  refine ⟨9474517322908638264889231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12632689763878184353185641 9474517322908638264889231)
  ·
    refine ⟨14211775984362957397333847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9474517322908638264889231 14211775984362957397333847)
    ·
      refine ⟨21317663976544436096000771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14211775984362957397333847 21317663976544436096000771)
      ·
        refine ⟨31976495964816654144001157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21317663976544436096000771 31976495964816654144001157)
        ·
          refine ⟨5995592993403122652000217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31976495964816654144001157 5995592993403122652000217)
          ·
            refine ⟨4496694745052341989000163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5995592993403122652000217 4496694745052341989000163)
            ·
              refine ⟨6745042117578512983500245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496694745052341989000163 6745042117578512983500245)
              ·
                refine ⟨158086924630746398050787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6745042117578512983500245 158086924630746398050787)
                ·
                  rfl

theorem cell19_519536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_519536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519536 prefixEnd_519536 := by exact prefixLift 519536
  have htrace : WordTrace (prefixWord ++ tailWord_519536) baseStart_519536 baseEnd_519536 := by
    simpa [prefixWord, tailWord_519536, baseEnd_519536] using wordTrace_append hprefix tailTrace_519536
  have hstable : (prefixWord ++ tailWord_519536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519536).length < 2 ^ (prefixWord ++ tailWord_519536).sum := by decide
  have hdescent : baseEnd_519536 < baseStart_519536 := by decide
  rcases family_descends (prefixWord ++ tailWord_519536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519553 : List Nat := [1, 2, 4, 3, 2, 7]
def baseStart_519553 : Nat := 118140960795 + 519553 * 2 ^ 59
def prefixEnd_519553 : Nat := 4983230072969 + 3 ^ 40 * 519553 * 2
def baseEnd_519553 : Nat := 17565788608099488408107

theorem tailTrace_519553 : CollatzResearch.WordTrace tailWord_519553 prefixEnd_519553 17565788608099488408107 := by
  unfold tailWord_519553
  simp only [CollatzResearch.WordTrace]
  refine ⟨18949654686755688433147313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12633103124503792288764875 18949654686755688433147313)
  ·
    refine ⟨14212241015066766324860485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18949654686755688433147313 14212241015066766324860485)
    ·
      refine ⟨2664795190325018685911341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14212241015066766324860485 2664795190325018685911341)
      ·
        refine ⟨999298196371882007216753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2664795190325018685911341 999298196371882007216753)
        ·
          refine ⟨749473647278911505412565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999298196371882007216753 749473647278911505412565)
          ·
            refine ⟨17565788608099488408107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 749473647278911505412565 17565788608099488408107)
            ·
              rfl

theorem cell19_519553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 7].length) (baseStart_519553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519553 prefixEnd_519553 := by exact prefixLift 519553
  have htrace : WordTrace (prefixWord ++ tailWord_519553) baseStart_519553 baseEnd_519553 := by
    simpa [prefixWord, tailWord_519553, baseEnd_519553] using wordTrace_append hprefix tailTrace_519553
  have hstable : (prefixWord ++ tailWord_519553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519553).length < 2 ^ (prefixWord ++ tailWord_519553).sum := by decide
  have hdescent : baseEnd_519553 < baseStart_519553 := by decide
  rcases family_descends (prefixWord ++ tailWord_519553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519555 : List Nat := [1, 1, 1, 3, 5, 8]
def baseStart_519555 : Nat := 118140960795 + 519555 * 2 ^ 59
def prefixEnd_519555 : Nat := 4983230072969 + 3 ^ 40 * 519555 * 2
def baseEnd_519555 : Nat := 17565856226951109292057

theorem tailTrace_519555 : CollatzResearch.WordTrace tailWord_519555 prefixEnd_519555 17565856226951109292057 := by
  unfold tailWord_519555
  simp only [CollatzResearch.WordTrace]
  refine ⟨18949727632748442774720119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12633151755165628516480079 18949727632748442774720119)
  ·
    refine ⟨28424591449122664162080179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18949727632748442774720119 28424591449122664162080179)
    ·
      refine ⟨42636887173683996243120269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28424591449122664162080179 42636887173683996243120269)
      ·
        refine ⟨15988832690131498591170101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42636887173683996243120269 15988832690131498591170101)
        ·
          refine ⟨1498953064699827992922197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15988832690131498591170101 1498953064699827992922197)
          ·
            refine ⟨17565856226951109292057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1498953064699827992922197 17565856226951109292057)
            ·
              rfl

theorem cell19_519555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 8].length) (baseStart_519555 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519555 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519555 prefixEnd_519555 := by exact prefixLift 519555
  have htrace : WordTrace (prefixWord ++ tailWord_519555) baseStart_519555 baseEnd_519555 := by
    simpa [prefixWord, tailWord_519555, baseEnd_519555] using wordTrace_append hprefix tailTrace_519555
  have hstable : (prefixWord ++ tailWord_519555).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519555).length < 2 ^ (prefixWord ++ tailWord_519555).sum := by decide
  have hdescent : baseEnd_519555 < baseStart_519555 := by decide
  rcases family_descends (prefixWord ++ tailWord_519555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519684 : List Nat := [2, 3, 2, 3, 2, 1, 2, 4]
def baseStart_519684 : Nat := 118140960795 + 519684 * 2 ^ 59
def prefixEnd_519684 : Nat := 4983230072969 + 3 ^ 40 * 519684 * 2
def baseEnd_519684 : Nat := 158131958785925906761495

theorem tailTrace_519684 : CollatzResearch.WordTrace tailWord_519684 prefixEnd_519684 158131958785925906761495 := by
  unfold tailWord_519684
  simp only [CollatzResearch.WordTrace]
  refine ⟨9477216324640548903083053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12636288432854065204110737 9477216324640548903083053)
  ·
    refine ⟨3553956121740205838656145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9477216324640548903083053 3553956121740205838656145)
    ·
      refine ⟨2665467091305154378992109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3553956121740205838656145 2665467091305154378992109)
      ·
        refine ⟨999550159239432892122041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2665467091305154378992109 999550159239432892122041)
        ·
          refine ⟨749662619429574669091531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999550159239432892122041 749662619429574669091531)
          ·
            refine ⟨1124493929144362003637297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749662619429574669091531 1124493929144362003637297)
            ·
              refine ⟨843370446858271502727973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124493929144362003637297 843370446858271502727973)
              ·
                refine ⟨158131958785925906761495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 843370446858271502727973 158131958785925906761495)
                ·
                  rfl

theorem cell19_519684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_519684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519684 prefixEnd_519684 := by exact prefixLift 519684
  have htrace : WordTrace (prefixWord ++ tailWord_519684) baseStart_519684 baseEnd_519684 := by
    simpa [prefixWord, tailWord_519684, baseEnd_519684] using wordTrace_append hprefix tailTrace_519684
  have hstable : (prefixWord ++ tailWord_519684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519684).length < 2 ^ (prefixWord ++ tailWord_519684).sum := by decide
  have hdescent : baseEnd_519684 < baseStart_519684 := by decide
  rcases family_descends (prefixWord ++ tailWord_519684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519688 : List Nat := [2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_519688 : Nat := 118140960795 + 519688 * 2 ^ 59
def prefixEnd_519688 : Nat := 4983230072969 + 3 ^ 40 * 519688 * 2
def baseEnd_519688 : Nat := 158133175925255082672595

theorem tailTrace_519688 : CollatzResearch.WordTrace tailWord_519688 prefixEnd_519688 158133175925255082672595 := by
  unfold tailWord_519688
  simp only [CollatzResearch.WordTrace]
  refine ⟨9477289270633303244655859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12636385694177737659541145 9477289270633303244655859)
  ·
    refine ⟨14215933905949954866983789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9477289270633303244655859 14215933905949954866983789)
    ·
      refine ⟨5330975214731233075118921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14215933905949954866983789 5330975214731233075118921)
      ·
        refine ⟨3998231411048424806339191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5330975214731233075118921 3998231411048424806339191)
        ·
          refine ⟨5997347116572637209508787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998231411048424806339191 5997347116572637209508787)
          ·
            refine ⟨8996020674858955814263181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997347116572637209508787 8996020674858955814263181)
            ·
              refine ⟨3373507753072108430348693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8996020674858955814263181 3373507753072108430348693)
              ·
                refine ⟨158133175925255082672595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3373507753072108430348693 158133175925255082672595)
                ·
                  rfl

theorem cell19_519688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_519688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519688 prefixEnd_519688 := by exact prefixLift 519688
  have htrace : WordTrace (prefixWord ++ tailWord_519688) baseStart_519688 baseEnd_519688 := by
    simpa [prefixWord, tailWord_519688, baseEnd_519688] using wordTrace_append hprefix tailTrace_519688
  have hstable : (prefixWord ++ tailWord_519688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519688).length < 2 ^ (prefixWord ++ tailWord_519688).sum := by decide
  have hdescent : baseEnd_519688 < baseStart_519688 := by decide
  rcases family_descends (prefixWord ++ tailWord_519688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519741 : List Nat := [1, 4, 1, 3, 3, 2, 1, 4]
def baseStart_519741 : Nat := 118140960795 + 519741 * 2 ^ 59
def prefixEnd_519741 : Nat := 4983230072969 + 3 ^ 40 * 519741 * 2
def baseEnd_519741 : Nat := 158149303021366663494673

theorem tailTrace_519741 : CollatzResearch.WordTrace tailWord_519741 prefixEnd_519741 158149303021366663494673 := by
  unfold tailWord_519741
  simp only [CollatzResearch.WordTrace]
  refine ⟨18956511610074596540991077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12637674406716397693994051 18956511610074596540991077)
  ·
    refine ⟨3554345926888986851435827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18956511610074596540991077 3554345926888986851435827)
    ·
      refine ⟨5331518890333480277153741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3554345926888986851435827 5331518890333480277153741)
      ·
        refine ⟨1999319583875055103932653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5331518890333480277153741 1999319583875055103932653)
        ·
          refine ⟨749744843953145663974745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1999319583875055103932653 749744843953145663974745)
          ·
            refine ⟨562308632964859247981059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749744843953145663974745 562308632964859247981059)
            ·
              refine ⟨843462949447288871971589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562308632964859247981059 843462949447288871971589)
              ·
                refine ⟨158149303021366663494673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 843462949447288871971589 158149303021366663494673)
                ·
                  rfl

theorem cell19_519741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_519741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519741 prefixEnd_519741 := by exact prefixLift 519741
  have htrace : WordTrace (prefixWord ++ tailWord_519741) baseStart_519741 baseEnd_519741 := by
    simpa [prefixWord, tailWord_519741, baseEnd_519741] using wordTrace_append hprefix tailTrace_519741
  have hstable : (prefixWord ++ tailWord_519741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519741).length < 2 ^ (prefixWord ++ tailWord_519741).sum := by decide
  have hdescent : baseEnd_519741 < baseStart_519741 := by decide
  rcases family_descends (prefixWord ++ tailWord_519741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519743 : List Nat := [1, 1, 2, 2, 3, 5, 1, 4]
def baseStart_519743 : Nat := 118140960795 + 519743 * 2 ^ 59
def prefixEnd_519743 : Nat := 4983230072969 + 3 ^ 40 * 519743 * 2
def baseEnd_519743 : Nat := 158149911591031251450223

theorem tailTrace_519743 : CollatzResearch.WordTrace tailWord_519743 prefixEnd_519743 158149911591031251450223 := by
  unfold tailWord_519743
  simp only [CollatzResearch.WordTrace]
  refine ⟨18956584556067350882563883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12637723037378233921709255 18956584556067350882563883)
  ·
    refine ⟨28434876834101026323845825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18956584556067350882563883 28434876834101026323845825)
    ·
      refine ⟨21326157625575769742884369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28434876834101026323845825 21326157625575769742884369)
      ·
        refine ⟨15994618219181827307163277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21326157625575769742884369 15994618219181827307163277)
        ·
          refine ⟨5997981832193185240186229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15994618219181827307163277 5997981832193185240186229)
          ·
            refine ⟨562310796768111116267459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5997981832193185240186229 562310796768111116267459)
            ·
              refine ⟨843466195152166674401189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562310796768111116267459 843466195152166674401189)
              ·
                refine ⟨158149911591031251450223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 843466195152166674401189 158149911591031251450223)
                ·
                  rfl

theorem cell19_519743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_519743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519743 prefixEnd_519743 := by exact prefixLift 519743
  have htrace : WordTrace (prefixWord ++ tailWord_519743) baseStart_519743 baseEnd_519743 := by
    simpa [prefixWord, tailWord_519743, baseEnd_519743] using wordTrace_append hprefix tailTrace_519743
  have hstable : (prefixWord ++ tailWord_519743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519743).length < 2 ^ (prefixWord ++ tailWord_519743).sum := by decide
  have hdescent : baseEnd_519743 < baseStart_519743 := by decide
  rcases family_descends (prefixWord ++ tailWord_519743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519836 : List Nat := [2, 2, 3, 2, 4, 1, 5]
def baseStart_519836 : Nat := 118140960795 + 519836 * 2 ^ 59
def prefixEnd_519836 : Nat := 4983230072969 + 3 ^ 40 * 519836 * 2
def baseEnd_519836 : Nat := 52726070026811530461101

theorem tailTrace_519836 : CollatzResearch.WordTrace tailWord_519836 prefixEnd_519836 52726070026811530461101 := by
  unfold tailWord_519836
  simp only [CollatzResearch.WordTrace]
  refine ⟨9479988272365213882849681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12639984363153618510466241 9479988272365213882849681)
  ·
    refine ⟨7109991204273910412137261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9479988272365213882849681 7109991204273910412137261)
    ·
      refine ⟨2666246701602716404551473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7109991204273910412137261 2666246701602716404551473)
      ·
        refine ⟨1999685026202037303413605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2666246701602716404551473 1999685026202037303413605)
        ·
          refine ⟨374940942412881994390051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1999685026202037303413605 374940942412881994390051)
          ·
            refine ⟨562411413619322991585077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374940942412881994390051 562411413619322991585077)
            ·
              refine ⟨52726070026811530461101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 562411413619322991585077 52726070026811530461101)
              ·
                rfl

theorem cell19_519836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 5].length) (baseStart_519836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519836 prefixEnd_519836 := by exact prefixLift 519836
  have htrace : WordTrace (prefixWord ++ tailWord_519836) baseStart_519836 baseEnd_519836 := by
    simpa [prefixWord, tailWord_519836, baseEnd_519836] using wordTrace_append hprefix tailTrace_519836
  have hstable : (prefixWord ++ tailWord_519836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519836).length < 2 ^ (prefixWord ++ tailWord_519836).sum := by decide
  have hdescent : baseEnd_519836 < baseStart_519836 := by decide
  rcases family_descends (prefixWord ++ tailWord_519836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519838 : List Nat := [4, 3, 1, 1, 1, 2, 7]
def baseStart_519838 : Nat := 118140960795 + 519838 * 2 ^ 59
def prefixEnd_519838 : Nat := 4983230072969 + 3 ^ 40 * 519838 * 2
def baseEnd_519838 : Nat := 52726272883366393112951

theorem tailTrace_519838 : CollatzResearch.WordTrace tailWord_519838 prefixEnd_519838 52726272883366393112951 := by
  unfold tailWord_519838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370006186340397763409021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12640032993815454738181445 2370006186340397763409021)
  ·
    refine ⟨888752319877649161278383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2370006186340397763409021 888752319877649161278383)
    ·
      refine ⟨1333128479816473741917575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888752319877649161278383 1333128479816473741917575)
      ·
        refine ⟨1999692719724710612876363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333128479816473741917575 1999692719724710612876363)
        ·
          refine ⟨2999539079587065919314545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999692719724710612876363 2999539079587065919314545)
          ·
            refine ⟨2249654309690299439485909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2999539079587065919314545 2249654309690299439485909)
            ·
              refine ⟨52726272883366393112951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2249654309690299439485909 52726272883366393112951)
              ·
                rfl

theorem cell19_519838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_519838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519838 prefixEnd_519838 := by exact prefixLift 519838
  have htrace : WordTrace (prefixWord ++ tailWord_519838) baseStart_519838 baseEnd_519838 := by
    simpa [prefixWord, tailWord_519838, baseEnd_519838] using wordTrace_append hprefix tailTrace_519838
  have hstable : (prefixWord ++ tailWord_519838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519838).length < 2 ^ (prefixWord ++ tailWord_519838).sum := by decide
  have hdescent : baseEnd_519838 < baseStart_519838 := by decide
  rcases family_descends (prefixWord ++ tailWord_519838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519840 : List Nat := [2, 1, 1, 4, 3, 1, 7]
def baseStart_519840 : Nat := 118140960795 + 519840 * 2 ^ 59
def prefixEnd_519840 : Nat := 4983230072969 + 3 ^ 40 * 519840 * 2
def baseEnd_519840 : Nat := 52726475739921255764801

theorem tailTrace_519840 : CollatzResearch.WordTrace tailWord_519840 prefixEnd_519840 52726475739921255764801 := by
  unfold tailWord_519840
  simp only [CollatzResearch.WordTrace]
  refine ⟨9480061218357968224422487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12640081624477290965896649 9480061218357968224422487)
  ·
    refine ⟨14220091827536952336633731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9480061218357968224422487 14220091827536952336633731)
    ·
      refine ⟨21330137741305428504950597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14220091827536952336633731 21330137741305428504950597)
      ·
        refine ⟨3999400826494767844678237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21330137741305428504950597 3999400826494767844678237)
        ·
          refine ⟨1499775309935537941754339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3999400826494767844678237 1499775309935537941754339)
          ·
            refine ⟨2249662964903306912631509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499775309935537941754339 2249662964903306912631509)
            ·
              refine ⟨52726475739921255764801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2249662964903306912631509 52726475739921255764801)
              ·
                rfl

theorem cell19_519840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_519840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519840 prefixEnd_519840 := by exact prefixLift 519840
  have htrace : WordTrace (prefixWord ++ tailWord_519840) baseStart_519840 baseEnd_519840 := by
    simpa [prefixWord, tailWord_519840, baseEnd_519840] using wordTrace_append hprefix tailTrace_519840
  have hstable : (prefixWord ++ tailWord_519840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519840).length < 2 ^ (prefixWord ++ tailWord_519840).sum := by decide
  have hdescent : baseEnd_519840 < baseStart_519840 := by decide
  rcases family_descends (prefixWord ++ tailWord_519840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519859 : List Nat := [1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_519859 : Nat := 118140960795 + 519859 * 2 ^ 59
def prefixEnd_519859 : Nat := 4983230072969 + 3 ^ 40 * 519859 * 2
def baseEnd_519859 : Nat := 158185208631577352872129

theorem tailTrace_519859 : CollatzResearch.WordTrace tailWord_519859 prefixEnd_519859 158185208631577352872129 := by
  unfold tailWord_519859
  simp only [CollatzResearch.WordTrace]
  refine ⟨18960815423647102693786631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12640543615764735129191087 18960815423647102693786631)
  ·
    refine ⟨28441223135470654040679947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18960815423647102693786631 28441223135470654040679947)
    ·
      refine ⟨42661834703205981061019921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28441223135470654040679947 42661834703205981061019921)
      ·
        refine ⟨31996376027404485795764941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42661834703205981061019921 31996376027404485795764941)
        ·
          refine ⟨11998641010276682173411853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31996376027404485795764941 11998641010276682173411853)
          ·
            refine ⟨4499490378853755815029445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11998641010276682173411853 4499490378853755815029445)
            ·
              refine ⟨843654446035079215318021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4499490378853755815029445 843654446035079215318021)
              ·
                refine ⟨158185208631577352872129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 843654446035079215318021 158185208631577352872129)
                ·
                  rfl

theorem cell19_519859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_519859 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519859 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519859 prefixEnd_519859 := by exact prefixLift 519859
  have htrace : WordTrace (prefixWord ++ tailWord_519859) baseStart_519859 baseEnd_519859 := by
    simpa [prefixWord, tailWord_519859, baseEnd_519859] using wordTrace_append hprefix tailTrace_519859
  have hstable : (prefixWord ++ tailWord_519859).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519859).length < 2 ^ (prefixWord ++ tailWord_519859).sum := by decide
  have hdescent : baseEnd_519859 < baseStart_519859 := by decide
  rcases family_descends (prefixWord ++ tailWord_519859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519916 : List Nat := [2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_519916 : Nat := 118140960795 + 519916 * 2 ^ 59
def prefixEnd_519916 : Nat := 4983230072969 + 3 ^ 40 * 519916 * 2
def baseEnd_519916 : Nat := 158202552867018109605307

theorem tailTrace_519916 : CollatzResearch.WordTrace tailWord_519916 prefixEnd_519916 158202552867018109605307 := by
  unfold tailWord_519916
  simp only [CollatzResearch.WordTrace]
  refine ⟨9481447192220300714305801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12641929589627067619074401 9481447192220300714305801)
  ·
    refine ⟨7111085394165225535729351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9481447192220300714305801 7111085394165225535729351)
    ·
      refine ⟨10666628091247838303594027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7111085394165225535729351 10666628091247838303594027)
      ·
        refine ⟨15999942136871757455391041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10666628091247838303594027 15999942136871757455391041)
        ·
          refine ⟨11999956602653818091543281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15999942136871757455391041 11999956602653818091543281)
          ·
            refine ⟨8999967451990363568657461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11999956602653818091543281 8999967451990363568657461)
            ·
              refine ⟨843746948624096584561637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8999967451990363568657461 843746948624096584561637)
              ·
                refine ⟨158202552867018109605307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 843746948624096584561637 158202552867018109605307)
                ·
                  rfl

theorem cell19_519916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_519916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519916 prefixEnd_519916 := by exact prefixLift 519916
  have htrace : WordTrace (prefixWord ++ tailWord_519916) baseStart_519916 baseEnd_519916 := by
    simpa [prefixWord, tailWord_519916, baseEnd_519916] using wordTrace_append hprefix tailTrace_519916
  have hstable : (prefixWord ++ tailWord_519916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519916).length < 2 ^ (prefixWord ++ tailWord_519916).sum := by decide
  have hdescent : baseEnd_519916 < baseStart_519916 := by decide
  rcases family_descends (prefixWord ++ tailWord_519916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519988 : List Nat := [2, 5, 1, 1, 2, 1, 4, 3]
def baseStart_519988 : Nat := 118140960795 + 519988 * 2 ^ 59
def prefixEnd_519988 : Nat := 4983230072969 + 3 ^ 40 * 519988 * 2
def baseEnd_519988 : Nat := 158224461374943276005111

theorem tailTrace_519988 : CollatzResearch.WordTrace tailWord_519988 prefixEnd_519988 158224461374943276005111 := by
  unfold tailWord_519988
  simp only [CollatzResearch.WordTrace]
  refine ⟨9482760220089878862616309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12643680293453171816821745 9482760220089878862616309)
  ·
    refine ⟨889008770633426143370279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9482760220089878862616309 889008770633426143370279)
    ·
      refine ⟨1333513155950139215055419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 889008770633426143370279 1333513155950139215055419)
      ·
        refine ⟨2000269733925208822583129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333513155950139215055419 2000269733925208822583129)
        ·
          refine ⟨1500202300443906616937347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2000269733925208822583129 1500202300443906616937347)
          ·
            refine ⟨2250303450665859925406021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500202300443906616937347 2250303450665859925406021)
            ·
              refine ⟨421931896999848736013629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2250303450665859925406021 421931896999848736013629)
              ·
                refine ⟨158224461374943276005111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421931896999848736013629 158224461374943276005111)
                ·
                  rfl

theorem cell19_519988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_519988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519988 prefixEnd_519988 := by exact prefixLift 519988
  have htrace : WordTrace (prefixWord ++ tailWord_519988) baseStart_519988 baseEnd_519988 := by
    simpa [prefixWord, tailWord_519988, baseEnd_519988] using wordTrace_append hprefix tailTrace_519988
  have hstable : (prefixWord ++ tailWord_519988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519988).length < 2 ^ (prefixWord ++ tailWord_519988).sum := by decide
  have hdescent : baseEnd_519988 < baseStart_519988 := by decide
  rcases family_descends (prefixWord ++ tailWord_519988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519992 : List Nat := [2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_519992 : Nat := 118140960795 + 519992 * 2 ^ 59
def prefixEnd_519992 : Nat := 4983230072969 + 3 ^ 40 * 519992 * 2
def baseEnd_519992 : Nat := 158225678514272451916211

theorem tailTrace_519992 : CollatzResearch.WordTrace tailWord_519992 prefixEnd_519992 158225678514272451916211 := by
  unfold tailWord_519992
  simp only [CollatzResearch.WordTrace]
  refine ⟨9482833166082633204189115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12643777554776844272252153 9482833166082633204189115)
  ·
    refine ⟨14224249749123949806283673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9482833166082633204189115 14224249749123949806283673)
    ·
      refine ⟨10668187311842962354712755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14224249749123949806283673 10668187311842962354712755)
      ·
        refine ⟨16002280967764443532069133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10668187311842962354712755 16002280967764443532069133)
        ·
          refine ⟨6000855362911666324525925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16002280967764443532069133 6000855362911666324525925)
          ·
            refine ⟨1125160380545937435848611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6000855362911666324525925 1125160380545937435848611)
            ·
              refine ⟨1687740570818906153772917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125160380545937435848611 1687740570818906153772917)
              ·
                refine ⟨158225678514272451916211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1687740570818906153772917 158225678514272451916211)
                ·
                  rfl

theorem cell19_519992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_519992 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_519992 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_519992 prefixEnd_519992 := by exact prefixLift 519992
  have htrace : WordTrace (prefixWord ++ tailWord_519992) baseStart_519992 baseEnd_519992 := by
    simpa [prefixWord, tailWord_519992, baseEnd_519992] using wordTrace_append hprefix tailTrace_519992
  have hstable : (prefixWord ++ tailWord_519992).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519992).length < 2 ^ (prefixWord ++ tailWord_519992).sum := by decide
  have hdescent : baseEnd_519992 < baseStart_519992 := by decide
  rcases family_descends (prefixWord ++ tailWord_519992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520087 : List Nat := [1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_520087 : Nat := 118140960795 + 520087 * 2 ^ 59
def prefixEnd_520087 : Nat := 4983230072969 + 3 ^ 40 * 520087 * 2
def baseEnd_520087 : Nat := 158254585573340379804841

theorem tailTrace_520087 : CollatzResearch.WordTrace tailWord_520087 prefixEnd_520087 158254585573340379804841 := by
  unfold tailWord_520087
  simp only [CollatzResearch.WordTrace]
  refine ⟨18969131266821097633086515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12646087511214065088724343 18969131266821097633086515)
  ·
    refine ⟨28453696900231646449629773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18969131266821097633086515 28453696900231646449629773)
    ·
      refine ⟨10670136337586867418611165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28453696900231646449629773 10670136337586867418611165)
      ·
        refine ⟨4001301126595075281979187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10670136337586867418611165 4001301126595075281979187)
        ·
          refine ⟨6001951689892612922968781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001301126595075281979187 6001951689892612922968781)
          ·
            refine ⟨2250731883709729846113293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6001951689892612922968781 2250731883709729846113293)
            ·
              refine ⟨844024456391148692292485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2250731883709729846113293 844024456391148692292485)
              ·
                refine ⟨158254585573340379804841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844024456391148692292485 158254585573340379804841)
                ·
                  rfl

theorem cell19_520087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_520087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520087 prefixEnd_520087 := by exact prefixLift 520087
  have htrace : WordTrace (prefixWord ++ tailWord_520087) baseStart_520087 baseEnd_520087 := by
    simpa [prefixWord, tailWord_520087, baseEnd_520087] using wordTrace_append hprefix tailTrace_520087
  have hstable : (prefixWord ++ tailWord_520087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520087).length < 2 ^ (prefixWord ++ tailWord_520087).sum := by decide
  have hdescent : baseEnd_520087 < baseStart_520087 := by decide
  rcases family_descends (prefixWord ++ tailWord_520087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520125 : List Nat := [1, 4, 1, 2, 3, 2, 6]
def baseStart_520125 : Nat := 118140960795 + 520125 * 2 ^ 59
def prefixEnd_520125 : Nat := 4983230072969 + 3 ^ 40 * 520125 * 2
def baseEnd_520125 : Nat := 52755382798989183653431

theorem tailTrace_520125 : CollatzResearch.WordTrace tailWord_520125 prefixEnd_520125 52755382798989183653431 := by
  unfold tailWord_520125
  simp only [CollatzResearch.WordTrace]
  refine ⟨18970517240683430122969829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12647011493788953415313219 18970517240683430122969829)
  ·
    refine ⟨3556971982628143148056843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18970517240683430122969829 3556971982628143148056843)
    ·
      refine ⟨5335457973942214722085265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3556971982628143148056843 5335457973942214722085265)
      ·
        refine ⟨4001593480456661041563949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5335457973942214722085265 4001593480456661041563949)
        ·
          refine ⟨1500597555171247890586481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4001593480456661041563949 1500597555171247890586481)
          ·
            refine ⟨1125448166378435917939861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1500597555171247890586481 1125448166378435917939861)
            ·
              refine ⟨52755382798989183653431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1125448166378435917939861 52755382798989183653431)
              ·
                rfl

theorem cell19_520125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_520125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520125 prefixEnd_520125 := by exact prefixLift 520125
  have htrace : WordTrace (prefixWord ++ tailWord_520125) baseStart_520125 baseEnd_520125 := by
    simpa [prefixWord, tailWord_520125, baseEnd_520125] using wordTrace_append hprefix tailTrace_520125
  have hstable : (prefixWord ++ tailWord_520125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520125).length < 2 ^ (prefixWord ++ tailWord_520125).sum := by decide
  have hdescent : baseEnd_520125 < baseStart_520125 := by decide
  rcases family_descends (prefixWord ++ tailWord_520125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520127 : List Nat := [1, 1, 2, 2, 2, 1, 10]
def baseStart_520127 : Nat := 118140960795 + 520127 * 2 ^ 59
def prefixEnd_520127 : Nat := 4983230072969 + 3 ^ 40 * 520127 * 2
def baseEnd_520127 : Nat := 52755585655544046305281

theorem tailTrace_520127 : CollatzResearch.WordTrace tailWord_520127 prefixEnd_520127 52755585655544046305281 := by
  unfold tailWord_520127
  simp only [CollatzResearch.WordTrace]
  refine ⟨18970590186676184464542635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12647060124450789643028423 18970590186676184464542635)
  ·
    refine ⟨28455885280014276696813953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18970590186676184464542635 28455885280014276696813953)
    ·
      refine ⟨21341913960010707522610465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28455885280014276696813953 21341913960010707522610465)
      ·
        refine ⟨16006435470008030641957849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21341913960010707522610465 16006435470008030641957849)
        ·
          refine ⟨12004826602506022981468387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16006435470008030641957849 12004826602506022981468387)
          ·
            refine ⟨18007239903759034472202581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12004826602506022981468387 18007239903759034472202581)
            ·
              refine ⟨52755585655544046305281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18007239903759034472202581 52755585655544046305281)
              ·
                rfl

theorem cell19_520127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_520127 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520127 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520127 prefixEnd_520127 := by exact prefixLift 520127
  have htrace : WordTrace (prefixWord ++ tailWord_520127) baseStart_520127 baseEnd_520127 := by
    simpa [prefixWord, tailWord_520127, baseEnd_520127] using wordTrace_append hprefix tailTrace_520127
  have hstable : (prefixWord ++ tailWord_520127).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520127).length < 2 ^ (prefixWord ++ tailWord_520127).sum := by decide
  have hdescent : baseEnd_520127 < baseStart_520127 := by decide
  rcases family_descends (prefixWord ++ tailWord_520127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520157 : List Nat := [1, 4, 3, 1, 4, 1, 2, 3]
def baseStart_520157 : Nat := 118140960795 + 520157 * 2 ^ 59
def prefixEnd_520157 : Nat := 4983230072969 + 3 ^ 40 * 520157 * 2
def baseEnd_520157 : Nat := 158275885511600958249095

theorem tailTrace_520157 : CollatzResearch.WordTrace tailWord_520157 prefixEnd_520157 158275885511600958249095 := by
  unfold tailWord_520157
  simp only [CollatzResearch.WordTrace]
  refine ⟨18971684376567499588134725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12647789584378333058756483 18971684376567499588134725)
  ·
    refine ⟨3557190820606406172775261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18971684376567499588134725 3557190820606406172775261)
    ·
      refine ⟨1333946557727402314790723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3557190820606406172775261 1333946557727402314790723)
      ·
        refine ⟨2000919836591103472186085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333946557727402314790723 2000919836591103472186085)
        ·
          refine ⟨375172469360831901034891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2000919836591103472186085 375172469360831901034891)
          ·
            refine ⟨562758704041247851552337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375172469360831901034891 562758704041247851552337)
            ·
              refine ⟨422069028030935888664253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562758704041247851552337 422069028030935888664253)
              ·
                refine ⟨158275885511600958249095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422069028030935888664253 158275885511600958249095)
                ·
                  rfl

theorem cell19_520157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 3].length) (baseStart_520157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520157 prefixEnd_520157 := by exact prefixLift 520157
  have htrace : WordTrace (prefixWord ++ tailWord_520157) baseStart_520157 baseEnd_520157 := by
    simpa [prefixWord, tailWord_520157, baseEnd_520157] using wordTrace_append hprefix tailTrace_520157
  have hstable : (prefixWord ++ tailWord_520157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520157).length < 2 ^ (prefixWord ++ tailWord_520157).sum := by decide
  have hdescent : baseEnd_520157 < baseStart_520157 := by decide
  rcases family_descends (prefixWord ++ tailWord_520157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520163 : List Nat := [1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_520163 : Nat := 118140960795 + 520163 * 2 ^ 59
def prefixEnd_520163 : Nat := 4983230072969 + 3 ^ 40 * 520163 * 2
def baseEnd_520163 : Nat := 158277711220594722115745

theorem tailTrace_520163 : CollatzResearch.WordTrace tailWord_520163 prefixEnd_520163 158277711220594722115745 := by
  unfold tailWord_520163
  simp only [CollatzResearch.WordTrace]
  refine ⟨18971903214545762612853143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12647935476363841741902095 18971903214545762612853143)
  ·
    refine ⟨28457854821818643919279715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18971903214545762612853143 28457854821818643919279715)
    ·
      refine ⟨42686782232727965878919573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28457854821818643919279715 42686782232727965878919573)
      ·
        refine ⟨2000942917159123400574355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42686782232727965878919573 2000942917159123400574355)
        ·
          refine ⟨3001414375738685100861533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000942917159123400574355 3001414375738685100861533)
          ·
            refine ⟨1125530390902006912823075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3001414375738685100861533 1125530390902006912823075)
            ·
              refine ⟨1688295586353010369234613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125530390902006912823075 1688295586353010369234613)
              ·
                refine ⟨158277711220594722115745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1688295586353010369234613 158277711220594722115745)
                ·
                  rfl

theorem cell19_520163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_520163 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520163 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520163 prefixEnd_520163 := by exact prefixLift 520163
  have htrace : WordTrace (prefixWord ++ tailWord_520163) baseStart_520163 baseEnd_520163 := by
    simpa [prefixWord, tailWord_520163, baseEnd_520163] using wordTrace_append hprefix tailTrace_520163
  have hstable : (prefixWord ++ tailWord_520163).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520163).length < 2 ^ (prefixWord ++ tailWord_520163).sum := by decide
  have hdescent : baseEnd_520163 < baseStart_520163 := by decide
  rcases family_descends (prefixWord ++ tailWord_520163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520184 : List Nat := [2, 1, 2, 1, 1, 3, 9]
def baseStart_520184 : Nat := 118140960795 + 520184 * 2 ^ 59
def prefixEnd_520184 : Nat := 4983230072969 + 3 ^ 40 * 520184 * 2
def baseEnd_520184 : Nat := 52761367067357631883007

theorem tailTrace_520184 : CollatzResearch.WordTrace tailWord_520184 prefixEnd_520184 52761367067357631883007 := by
  unfold tailWord_520184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9486334573734841599683803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12648446098313122132911737 9486334573734841599683803)
  ·
    refine ⟨14229501860602262399525705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9486334573734841599683803 14229501860602262399525705)
    ·
      refine ⟨10672126395451696799644279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14229501860602262399525705 10672126395451696799644279)
      ·
        refine ⟨16008189593177545199466419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10672126395451696799644279 16008189593177545199466419)
        ·
          refine ⟨24012284389766317799199629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16008189593177545199466419 24012284389766317799199629)
          ·
            refine ⟨9004606646162369174699861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24012284389766317799199629 9004606646162369174699861)
            ·
              refine ⟨52761367067357631883007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9004606646162369174699861 52761367067357631883007)
              ·
                rfl

theorem cell19_520184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_520184 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520184 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520184 prefixEnd_520184 := by exact prefixLift 520184
  have htrace : WordTrace (prefixWord ++ tailWord_520184) baseStart_520184 baseEnd_520184 := by
    simpa [prefixWord, tailWord_520184, baseEnd_520184] using wordTrace_append hprefix tailTrace_520184
  have hstable : (prefixWord ++ tailWord_520184).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520184).length < 2 ^ (prefixWord ++ tailWord_520184).sum := by decide
  have hdescent : baseEnd_520184 < baseStart_520184 := by decide
  rcases family_descends (prefixWord ++ tailWord_520184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520220 : List Nat := [2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_520220 : Nat := 118140960795 + 520220 * 2 ^ 59
def prefixEnd_520220 : Nat := 4983230072969 + 3 ^ 40 * 520220 * 2
def baseEnd_520220 : Nat := 158295055456035478848923

theorem tailTrace_520220 : CollatzResearch.WordTrace tailWord_520220 prefixEnd_520220 158295055456035478848923 := by
  unfold tailWord_520220
  simp only [CollatzResearch.WordTrace]
  refine ⟨9486991087669630673839057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12649321450226174231785409 9486991087669630673839057)
  ·
    refine ⟨7115243315752223005379293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9486991087669630673839057 7115243315752223005379293)
    ·
      refine ⟨2668216243407083627017235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7115243315752223005379293 2668216243407083627017235)
      ·
        refine ⟨4002324365110625440525853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2668216243407083627017235 4002324365110625440525853)
        ·
          refine ⟨1500871636916484540197195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4002324365110625440525853 1500871636916484540197195)
          ·
            refine ⟨2251307455374726810295793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500871636916484540197195 2251307455374726810295793)
            ·
              refine ⟨1688480591531045107721845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2251307455374726810295793 1688480591531045107721845)
              ·
                refine ⟨158295055456035478848923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1688480591531045107721845 158295055456035478848923)
                ·
                  rfl

theorem cell19_520220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_520220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520220 prefixEnd_520220 := by exact prefixLift 520220
  have htrace : WordTrace (prefixWord ++ tailWord_520220) baseStart_520220 baseEnd_520220 := by
    simpa [prefixWord, tailWord_520220, baseEnd_520220] using wordTrace_append hprefix tailTrace_520220
  have hstable : (prefixWord ++ tailWord_520220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520220).length < 2 ^ (prefixWord ++ tailWord_520220).sum := by decide
  have hdescent : baseEnd_520220 < baseStart_520220 := by decide
  rcases family_descends (prefixWord ++ tailWord_520220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520241 : List Nat := [1, 2, 2, 3, 1, 10]
def baseStart_520241 : Nat := 118140960795 + 520241 * 2 ^ 59
def prefixEnd_520241 : Nat := 4983230072969 + 3 ^ 40 * 520241 * 2
def baseEnd_520241 : Nat := 17589049493057072486911

theorem tailTrace_520241 : CollatzResearch.WordTrace tailWord_520241 prefixEnd_520241 17589049493057072486911 := by
  unfold tailWord_520241
  simp only [CollatzResearch.WordTrace]
  refine ⟨18974748108263181934192577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12649832072175454622795051 18974748108263181934192577)
  ·
    refine ⟨14231061081197386450644433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18974748108263181934192577 14231061081197386450644433)
    ·
      refine ⟨10673295810898039837983325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14231061081197386450644433 10673295810898039837983325)
      ·
        refine ⟨4002485929086764939243747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10673295810898039837983325 4002485929086764939243747)
        ·
          refine ⟨6003728893630147408865621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4002485929086764939243747 6003728893630147408865621)
          ·
            refine ⟨17589049493057072486911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6003728893630147408865621 17589049493057072486911)
            ·
              rfl

theorem cell19_520241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 10].length) (baseStart_520241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520241 prefixEnd_520241 := by exact prefixLift 520241
  have htrace : WordTrace (prefixWord ++ tailWord_520241) baseStart_520241 baseEnd_520241 := by
    simpa [prefixWord, tailWord_520241, baseEnd_520241] using wordTrace_append hprefix tailTrace_520241
  have hstable : (prefixWord ++ tailWord_520241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520241).length < 2 ^ (prefixWord ++ tailWord_520241).sum := by decide
  have hdescent : baseEnd_520241 < baseStart_520241 := by decide
  rcases family_descends (prefixWord ++ tailWord_520241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520254 : List Nat := [4, 2, 1, 3, 2, 2, 1, 4]
def baseStart_520254 : Nat := 118140960795 + 520254 * 2 ^ 59
def prefixEnd_520254 : Nat := 4983230072969 + 3 ^ 40 * 520254 * 2
def baseEnd_520254 : Nat := 158305401140333474093275

theorem tailTrace_520254 : CollatzResearch.WordTrace tailWord_520254 prefixEnd_520254 158305401140333474093275 := by
  unfold tailWord_520254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2371902782152010644301977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12650148171477390102943877 2371902782152010644301977)
  ·
    refine ⟨1778927086614007983226483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2371902782152010644301977 1778927086614007983226483)
    ·
      refine ⟨2668390629921011974839725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1778927086614007983226483 2668390629921011974839725)
      ·
        refine ⟨1000646486220379490564897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2668390629921011974839725 1000646486220379490564897)
        ·
          refine ⟨750484864665284617923673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000646486220379490564897 750484864665284617923673)
          ·
            refine ⟨562863648498963463442755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750484864665284617923673 562863648498963463442755)
            ·
              refine ⟨844295472748445195164133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562863648498963463442755 844295472748445195164133)
              ·
                refine ⟨158305401140333474093275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844295472748445195164133 158305401140333474093275)
                ·
                  rfl

theorem cell19_520254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_520254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520254 prefixEnd_520254 := by exact prefixLift 520254
  have htrace : WordTrace (prefixWord ++ tailWord_520254) baseStart_520254 baseEnd_520254 := by
    simpa [prefixWord, tailWord_520254, baseEnd_520254] using wordTrace_append hprefix tailTrace_520254
  have hstable : (prefixWord ++ tailWord_520254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520254).length < 2 ^ (prefixWord ++ tailWord_520254).sum := by decide
  have hdescent : baseEnd_520254 < baseStart_520254 := by decide
  rcases family_descends (prefixWord ++ tailWord_520254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520279 : List Nat := [1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_520279 : Nat := 118140960795 + 520279 * 2 ^ 59
def prefixEnd_520279 : Nat := 4983230072969 + 3 ^ 40 * 520279 * 2
def baseEnd_520279 : Nat := 158313008261140823537651

theorem tailTrace_520279 : CollatzResearch.WordTrace tailWord_520279 prefixEnd_520279 158313008261140823537651 := by
  unfold tailWord_520279
  simp only [CollatzResearch.WordTrace]
  refine ⟨18976134082125514424075891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12650756054750342949383927 18976134082125514424075891)
  ·
    refine ⟨28464201123188271636113837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18976134082125514424075891 28464201123188271636113837)
    ·
      refine ⟨10674075421195601863542689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28464201123188271636113837 10674075421195601863542689)
      ·
        refine ⟨8005556565896701397657017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10674075421195601863542689 8005556565896701397657017)
        ·
          refine ⟨6004167424422526048242763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8005556565896701397657017 6004167424422526048242763)
          ·
            refine ⟨9006251136633789072364145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6004167424422526048242763 9006251136633789072364145)
            ·
              refine ⟨6754688352475341804273109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9006251136633789072364145 6754688352475341804273109)
              ·
                refine ⟨158313008261140823537651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6754688352475341804273109 158313008261140823537651)
                ·
                  rfl

theorem cell19_520279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_520279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520279 prefixEnd_520279 := by exact prefixLift 520279
  have htrace : WordTrace (prefixWord ++ tailWord_520279) baseStart_520279 baseEnd_520279 := by
    simpa [prefixWord, tailWord_520279, baseEnd_520279] using wordTrace_append hprefix tailTrace_520279
  have hstable : (prefixWord ++ tailWord_520279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520279).length < 2 ^ (prefixWord ++ tailWord_520279).sum := by decide
  have hdescent : baseEnd_520279 < baseStart_520279 := by decide
  rcases family_descends (prefixWord ++ tailWord_520279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520336 : List Nat := [2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_520336 : Nat := 118140960795 + 520336 * 2 ^ 59
def prefixEnd_520336 : Nat := 4983230072969 + 3 ^ 40 * 520336 * 2
def baseEnd_520336 : Nat := 158330352496581580270829

theorem tailTrace_520336 : CollatzResearch.WordTrace tailWord_520336 prefixEnd_520336 158330352496581580270829 := by
  unfold tailWord_520336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9489106521459506579450431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12652142028612675439267241 9489106521459506579450431)
  ·
    refine ⟨14233659782189259869175647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9489106521459506579450431 14233659782189259869175647)
    ·
      refine ⟨21350489673283889803763471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14233659782189259869175647 21350489673283889803763471)
      ·
        refine ⟨32025734509925834705645207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21350489673283889803763471 32025734509925834705645207)
        ·
          refine ⟨48038601764888752058467811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32025734509925834705645207 48038601764888752058467811)
          ·
            refine ⟨72057902647333128087701717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48038601764888752058467811 72057902647333128087701717)
            ·
              refine ⟨1688857093296870189555509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 72057902647333128087701717 1688857093296870189555509)
              ·
                refine ⟨158330352496581580270829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1688857093296870189555509 158330352496581580270829)
                ·
                  rfl

theorem cell19_520336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_520336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520336 prefixEnd_520336 := by exact prefixLift 520336
  have htrace : WordTrace (prefixWord ++ tailWord_520336) baseStart_520336 baseEnd_520336 := by
    simpa [prefixWord, tailWord_520336, baseEnd_520336] using wordTrace_append hprefix tailTrace_520336
  have hstable : (prefixWord ++ tailWord_520336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520336).length < 2 ^ (prefixWord ++ tailWord_520336).sum := by decide
  have hdescent : baseEnd_520336 < baseStart_520336 := by decide
  rcases family_descends (prefixWord ++ tailWord_520336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520353 : List Nat := [1, 2, 3, 3, 1, 4, 5]
def baseStart_520353 : Nat := 118140960795 + 520353 * 2 ^ 59
def prefixEnd_520353 : Nat := 4983230072969 + 3 ^ 40 * 520353 * 2
def baseEnd_520353 : Nat := 52778508446243525964335

theorem tailTrace_520353 : CollatzResearch.WordTrace tailWord_520353 prefixEnd_520353 52778508446243525964335 := by
  unfold tailWord_520353
  simp only [CollatzResearch.WordTrace]
  refine ⟨18978833083857425062269713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12652555389238283374846475 18978833083857425062269713)
  ·
    refine ⟨14234124812893068796702285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18978833083857425062269713 14234124812893068796702285)
    ·
      refine ⟨5337796804834900798763357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14234124812893068796702285 5337796804834900798763357)
      ·
        refine ⟨2001673801813087799536259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5337796804834900798763357 2001673801813087799536259)
        ·
          refine ⟨3002510702719631699304389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001673801813087799536259 3002510702719631699304389)
          ·
            refine ⟨562970756759930943619573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3002510702719631699304389 562970756759930943619573)
            ·
              refine ⟨52778508446243525964335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 562970756759930943619573 52778508446243525964335)
              ·
                rfl

theorem cell19_520353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_520353 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520353 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520353 prefixEnd_520353 := by exact prefixLift 520353
  have htrace : WordTrace (prefixWord ++ tailWord_520353) baseStart_520353 baseEnd_520353 := by
    simpa [prefixWord, tailWord_520353, baseEnd_520353] using wordTrace_append hprefix tailTrace_520353
  have hstable : (prefixWord ++ tailWord_520353).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520353).length < 2 ^ (prefixWord ++ tailWord_520353).sum := by decide
  have hdescent : baseEnd_520353 < baseStart_520353 := by decide
  rcases family_descends (prefixWord ++ tailWord_520353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520446 : List Nat := [4, 2, 2, 1, 1, 1, 5, 3]
def baseStart_520446 : Nat := 118140960795 + 520446 * 2 ^ 59
def prefixEnd_520446 : Nat := 4983230072969 + 3 ^ 40 * 520446 * 2
def baseEnd_520446 : Nat := 158363823828133917826085

theorem tailTrace_520446 : CollatzResearch.WordTrace tailWord_520446 prefixEnd_520446 158363823828133917826085 := by
  unfold tailWord_520446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372778134065062743175649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12654816715013667963603461 2372778134065062743175649)
  ·
    refine ⟨1779583600548797057381737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2372778134065062743175649 1779583600548797057381737)
    ·
      refine ⟨1334687700411597793036303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1779583600548797057381737 1334687700411597793036303)
      ·
        refine ⟨2002031550617396689554455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334687700411597793036303 2002031550617396689554455)
        ·
          refine ⟨3003047325926095034331683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002031550617396689554455 3003047325926095034331683)
          ·
            refine ⟨4504570988889142551497525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003047325926095034331683 4504570988889142551497525)
            ·
              refine ⟨422303530208357114202893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4504570988889142551497525 422303530208357114202893)
              ·
                refine ⟨158363823828133917826085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422303530208357114202893 158363823828133917826085)
                ·
                  rfl

theorem cell19_520446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_520446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520446 prefixEnd_520446 := by exact prefixLift 520446
  have htrace : WordTrace (prefixWord ++ tailWord_520446) baseStart_520446 baseEnd_520446 := by
    simpa [prefixWord, tailWord_520446, baseEnd_520446] using wordTrace_append hprefix tailTrace_520446
  have hstable : (prefixWord ++ tailWord_520446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520446).length < 2 ^ (prefixWord ++ tailWord_520446).sum := by decide
  have hdescent : baseEnd_520446 < baseStart_520446 := by decide
  rcases family_descends (prefixWord ++ tailWord_520446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520505 : List Nat := [1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_520505 : Nat := 118140960795 + 520505 * 2 ^ 59
def prefixEnd_520505 : Nat := 4983230072969 + 3 ^ 40 * 520505 * 2
def baseEnd_520505 : Nat := 158381776633239262514813

theorem tailTrace_520505 : CollatzResearch.WordTrace tailWord_520505 prefixEnd_520505 158381776633239262514813 := by
  unfold tailWord_520505
  simp only [CollatzResearch.WordTrace]
  refine ⟨18984376979306755021802969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12656251319537836681201979 18984376979306755021802969)
  ·
    refine ⟨14238282734480066266352227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18984376979306755021802969 14238282734480066266352227)
    ·
      refine ⟨21357424101720099399528341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14238282734480066266352227 21357424101720099399528341)
      ·
        refine ⟨1001129254768129659352891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21357424101720099399528341 1001129254768129659352891)
        ·
          refine ⟨1501693882152194489029337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001129254768129659352891 1501693882152194489029337)
          ·
            refine ⟨1126270411614145866772003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501693882152194489029337 1126270411614145866772003)
            ·
              refine ⟨1689405617421218800158005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126270411614145866772003 1689405617421218800158005)
              ·
                refine ⟨158381776633239262514813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1689405617421218800158005 158381776633239262514813)
                ·
                  rfl

theorem cell19_520505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_520505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520505 prefixEnd_520505 := by exact prefixLift 520505
  have htrace : WordTrace (prefixWord ++ tailWord_520505) baseStart_520505 baseEnd_520505 := by
    simpa [prefixWord, tailWord_520505, baseEnd_520505] using wordTrace_append hprefix tailTrace_520505
  have hstable : (prefixWord ++ tailWord_520505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520505).length < 2 ^ (prefixWord ++ tailWord_520505).sum := by decide
  have hdescent : baseEnd_520505 < baseStart_520505 := by decide
  rcases family_descends (prefixWord ++ tailWord_520505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520596 : List Nat := [2, 4, 2, 1, 4, 1, 1, 4]
def baseStart_520596 : Nat := 118140960795 + 520596 * 2 ^ 59
def prefixEnd_520596 : Nat := 4983230072969 + 3 ^ 40 * 520596 * 2
def baseEnd_520596 : Nat := 158409466552978014492343

theorem tailTrace_520596 : CollatzResearch.WordTrace tailWord_520596 prefixEnd_520596 158409466552978014492343 := by
  unfold tailWord_520596
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493848010988538781682821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12658464014651385042243761 9493848010988538781682821)
  ·
    refine ⟨1780096502060351021565529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9493848010988538781682821 1780096502060351021565529)
    ·
      refine ⟨1335072376545263266174147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1780096502060351021565529 1335072376545263266174147)
      ·
        refine ⟨2002608564817894899261221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335072376545263266174147 2002608564817894899261221)
        ·
          refine ⟨375489105903355293611479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2002608564817894899261221 375489105903355293611479)
          ·
            refine ⟨563233658855032940417219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375489105903355293611479 563233658855032940417219)
            ·
              refine ⟨844850488282549410625829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563233658855032940417219 844850488282549410625829)
              ·
                refine ⟨158409466552978014492343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844850488282549410625829 158409466552978014492343)
                ·
                  rfl

theorem cell19_520596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_520596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520596 prefixEnd_520596 := by exact prefixLift 520596
  have htrace : WordTrace (prefixWord ++ tailWord_520596) baseStart_520596 baseEnd_520596 := by
    simpa [prefixWord, tailWord_520596, baseEnd_520596] using wordTrace_append hprefix tailTrace_520596
  have hstable : (prefixWord ++ tailWord_520596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520596).length < 2 ^ (prefixWord ++ tailWord_520596).sum := by decide
  have hdescent : baseEnd_520596 < baseStart_520596 := by decide
  rcases family_descends (prefixWord ++ tailWord_520596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520600 : List Nat := [2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_520600 : Nat := 118140960795 + 520600 * 2 ^ 59
def prefixEnd_520600 : Nat := 4983230072969 + 3 ^ 40 * 520600 * 2
def baseEnd_520600 : Nat := 158410683692307190403443

theorem tailTrace_520600 : CollatzResearch.WordTrace tailWord_520600 prefixEnd_520600 158410683692307190403443 := by
  unfold tailWord_520600
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493920956981293123255627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12658561275975057497674169 9493920956981293123255627)
  ·
    refine ⟨14240881435471939684883441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9493920956981293123255627 14240881435471939684883441)
    ·
      refine ⟨10680661076603954763662581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14240881435471939684883441 10680661076603954763662581)
      ·
        refine ⟨1001311975931620759093367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10680661076603954763662581 1001311975931620759093367)
        ·
          refine ⟨1501967963897431138640051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001311975931620759093367 1501967963897431138640051)
          ·
            refine ⟨2252951945846146707960077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501967963897431138640051 2252951945846146707960077)
            ·
              refine ⟨844856979692305015485029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2252951945846146707960077 844856979692305015485029)
              ·
                refine ⟨158410683692307190403443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844856979692305015485029 158410683692307190403443)
                ·
                  rfl

theorem cell19_520600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_520600 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520600 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520600 prefixEnd_520600 := by exact prefixLift 520600
  have htrace : WordTrace (prefixWord ++ tailWord_520600) baseStart_520600 baseEnd_520600 := by
    simpa [prefixWord, tailWord_520600, baseEnd_520600] using wordTrace_append hprefix tailTrace_520600
  have hstable : (prefixWord ++ tailWord_520600).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520600).length < 2 ^ (prefixWord ++ tailWord_520600).sum := by decide
  have hdescent : baseEnd_520600 < baseStart_520600 := by decide
  rcases family_descends (prefixWord ++ tailWord_520600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520693 : List Nat := [1, 3, 5, 1, 2, 2, 5]
def baseStart_520693 : Nat := 118140960795 + 520693 * 2 ^ 59
def prefixEnd_520693 : Nat := 4983230072969 + 3 ^ 40 * 520693 * 2
def baseEnd_520693 : Nat := 52812994060570176778841

theorem tailTrace_520693 : CollatzResearch.WordTrace tailWord_520693 prefixEnd_520693 52812994060570176778841 := by
  unfold tailWord_520693
  simp only [CollatzResearch.WordTrace]
  refine ⟨18991233902625663129646733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12660822601750442086431155 18991233902625663129646733)
  ·
    refine ⟨7121712713484623673617525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18991233902625663129646733 7121712713484623673617525)
    ·
      refine ⟨667660566889183469401643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7121712713484623673617525 667660566889183469401643)
      ·
        refine ⟨1001490850333775204102465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667660566889183469401643 1001490850333775204102465)
        ·
          refine ⟨751118137750331403076849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1001490850333775204102465 751118137750331403076849)
          ·
            refine ⟨563338603312748552307637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751118137750331403076849 563338603312748552307637)
            ·
              refine ⟨52812994060570176778841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 563338603312748552307637 52812994060570176778841)
              ·
                rfl

theorem cell19_520693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_520693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520693 prefixEnd_520693 := by exact prefixLift 520693
  have htrace : WordTrace (prefixWord ++ tailWord_520693) baseStart_520693 baseEnd_520693 := by
    simpa [prefixWord, tailWord_520693, baseEnd_520693] using wordTrace_append hprefix tailTrace_520693
  have hstable : (prefixWord ++ tailWord_520693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520693).length < 2 ^ (prefixWord ++ tailWord_520693).sum := by decide
  have hdescent : baseEnd_520693 < baseStart_520693 := by decide
  rcases family_descends (prefixWord ++ tailWord_520693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520710 : List Nat := [6, 2, 1, 1, 1, 1, 1, 6]
def baseStart_520710 : Nat := 118140960795 + 520710 * 2 ^ 59
def prefixEnd_520710 : Nat := 4983230072969 + 3 ^ 40 * 520710 * 2
def baseEnd_520710 : Nat := 158444155023859527958699

theorem tailTrace_520710 : CollatzResearch.WordTrace tailWord_520710 prefixEnd_520710 158444155023859527958699 := by
  unfold tailWord_520710
  simp only [CollatzResearch.WordTrace]
  refine ⟨593495435736377344781737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12661235962376050022010389 593495435736377344781737)
  ·
    refine ⟨445121576802283008586303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 593495435736377344781737 445121576802283008586303)
    ·
      refine ⟨667682365203424512879455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445121576802283008586303 667682365203424512879455)
      ·
        refine ⟨1001523547805136769319183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667682365203424512879455 1001523547805136769319183)
        ·
          refine ⟨1502285321707705153978775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001523547805136769319183 1502285321707705153978775)
          ·
            refine ⟨2253427982561557730968163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502285321707705153978775 2253427982561557730968163)
            ·
              refine ⟨3380141973842336596452245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253427982561557730968163 3380141973842336596452245)
              ·
                refine ⟨158444155023859527958699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3380141973842336596452245 158444155023859527958699)
                ·
                  rfl

theorem cell19_520710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_520710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520710 prefixEnd_520710 := by exact prefixLift 520710
  have htrace : WordTrace (prefixWord ++ tailWord_520710) baseStart_520710 baseEnd_520710 := by
    simpa [prefixWord, tailWord_520710, baseEnd_520710] using wordTrace_append hprefix tailTrace_520710
  have hstable : (prefixWord ++ tailWord_520710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520710).length < 2 ^ (prefixWord ++ tailWord_520710).sum := by decide
  have hdescent : baseEnd_520710 < baseStart_520710 := by decide
  rcases family_descends (prefixWord ++ tailWord_520710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520716 : List Nat := [2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_520716 : Nat := 118140960795 + 520716 * 2 ^ 59
def prefixEnd_520716 : Nat := 4983230072969 + 3 ^ 40 * 520716 * 2
def baseEnd_520716 : Nat := 158445980732853291825349

theorem tailTrace_520716 : CollatzResearch.WordTrace tailWord_520716 prefixEnd_520716 158445980732853291825349 := by
  unfold tailWord_520716
  simp only [CollatzResearch.WordTrace]
  refine ⟨9496036390771169028867001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12661381854361558705156001 9496036390771169028867001)
  ·
    refine ⟨7122027293078376771650251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9496036390771169028867001 7122027293078376771650251)
    ·
      refine ⟨10683040939617565157475377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7122027293078376771650251 10683040939617565157475377)
      ·
        refine ⟨8012280704713173868106533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10683040939617565157475377 8012280704713173868106533)
        ·
          refine ⟨1502302632133720100269975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8012280704713173868106533 1502302632133720100269975)
          ·
            refine ⟨2253453948200580150404963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502302632133720100269975 2253453948200580150404963)
            ·
              refine ⟨3380180922300870225607445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253453948200580150404963 3380180922300870225607445)
              ·
                refine ⟨158445980732853291825349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3380180922300870225607445 158445980732853291825349)
                ·
                  rfl

theorem cell19_520716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_520716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520716 prefixEnd_520716 := by exact prefixLift 520716
  have htrace : WordTrace (prefixWord ++ tailWord_520716) baseStart_520716 baseEnd_520716 := by
    simpa [prefixWord, tailWord_520716, baseEnd_520716] using wordTrace_append hprefix tailTrace_520716
  have hstable : (prefixWord ++ tailWord_520716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520716).length < 2 ^ (prefixWord ++ tailWord_520716).sum := by decide
  have hdescent : baseEnd_520716 < baseStart_520716 := by decide
  rcases family_descends (prefixWord ++ tailWord_520716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520773 : List Nat := [1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_520773 : Nat := 118140960795 + 520773 * 2 ^ 59
def prefixEnd_520773 : Nat := 4983230072969 + 3 ^ 40 * 520773 * 2
def baseEnd_520773 : Nat := 158463324968294048558527

theorem tailTrace_520773 : CollatzResearch.WordTrace tailWord_520773 prefixEnd_520773 158463324968294048558527 := by
  unfold tailWord_520773
  simp only [CollatzResearch.WordTrace]
  refine ⟨18994151742335836792558973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12662767828223891195039315 18994151742335836792558973)
  ·
    refine ⟨7122806903375938797209615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18994151742335836792558973 7122806903375938797209615)
    ·
      refine ⟨10684210355063908195814423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7122806903375938797209615 10684210355063908195814423)
      ·
        refine ⟨16026315532595862293721635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10684210355063908195814423 16026315532595862293721635)
        ·
          refine ⟨24039473298893793440582453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16026315532595862293721635 24039473298893793440582453)
          ·
            refine ⟨2253700621771293135054605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24039473298893793440582453 2253700621771293135054605)
            ·
              refine ⟨845137733164234925645477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2253700621771293135054605 845137733164234925645477)
              ·
                refine ⟨158463324968294048558527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 845137733164234925645477 158463324968294048558527)
                ·
                  rfl

theorem cell19_520773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_520773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520773 prefixEnd_520773 := by exact prefixLift 520773
  have htrace : WordTrace (prefixWord ++ tailWord_520773) baseStart_520773 baseEnd_520773 := by
    simpa [prefixWord, tailWord_520773, baseEnd_520773] using wordTrace_append hprefix tailTrace_520773
  have hstable : (prefixWord ++ tailWord_520773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520773).length < 2 ^ (prefixWord ++ tailWord_520773).sum := by decide
  have hdescent : baseEnd_520773 < baseStart_520773 := by decide
  rcases family_descends (prefixWord ++ tailWord_520773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520851 : List Nat := [1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_520851 : Nat := 118140960795 + 520851 * 2 ^ 59
def prefixEnd_520851 : Nat := 4983230072969 + 3 ^ 40 * 520851 * 2
def baseEnd_520851 : Nat := 158487059185212978824981

theorem tailTrace_520851 : CollatzResearch.WordTrace tailWord_520851 prefixEnd_520851 158487059185212978824981 := by
  unfold tailWord_520851
  simp only [CollatzResearch.WordTrace]
  refine ⟨18996996636053256113898407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12664664424035504075932271 18996996636053256113898407)
  ·
    refine ⟨28495494954079884170847611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18996996636053256113898407 28495494954079884170847611)
    ·
      refine ⟨42743242431119826256271417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28495494954079884170847611 42743242431119826256271417)
      ·
        refine ⟨32057431823339869692203563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42743242431119826256271417 32057431823339869692203563)
        ·
          refine ⟨48086147735009804538305345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32057431823339869692203563 48086147735009804538305345)
          ·
            refine ⟨36064610801257353403729009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48086147735009804538305345 36064610801257353403729009)
            ·
              refine ⟨27048458100943015052796757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36064610801257353403729009 27048458100943015052796757)
              ·
                refine ⟨158487059185212978824981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27048458100943015052796757 158487059185212978824981)
                ·
                  rfl

theorem cell19_520851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_520851 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520851 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520851 prefixEnd_520851 := by exact prefixLift 520851
  have htrace : WordTrace (prefixWord ++ tailWord_520851) baseStart_520851 baseEnd_520851 := by
    simpa [prefixWord, tailWord_520851, baseEnd_520851] using wordTrace_append hprefix tailTrace_520851
  have hstable : (prefixWord ++ tailWord_520851).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520851).length < 2 ^ (prefixWord ++ tailWord_520851).sum := by decide
  have hdescent : baseEnd_520851 < baseStart_520851 := by decide
  rcases family_descends (prefixWord ++ tailWord_520851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520885 : List Nat := [1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_520885 : Nat := 118140960795 + 520885 * 2 ^ 59
def prefixEnd_520885 : Nat := 4983230072969 + 3 ^ 40 * 520885 * 2
def baseEnd_520885 : Nat := 158497404869510974069333

theorem tailTrace_520885 : CollatzResearch.WordTrace tailWord_520885 prefixEnd_520885 158497404869510974069333 := by
  unfold tailWord_520885
  simp only [CollatzResearch.WordTrace]
  refine ⟨18998236717930079920636109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12665491145286719947090739 18998236717930079920636109)
  ·
    refine ⟨7124338769223779970238541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18998236717930079920636109 7124338769223779970238541)
    ·
      refine ⟨2671627038458917488839453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7124338769223779970238541 2671627038458917488839453)
      ·
        refine ⟨1001860139422094058314795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2671627038458917488839453 1001860139422094058314795)
        ·
          refine ⟨1502790209133141087472193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001860139422094058314795 1502790209133141087472193)
          ·
            refine ⟨1127092656849855815604145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1502790209133141087472193 1127092656849855815604145)
            ·
              refine ⟨845319492637391861703109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127092656849855815604145 845319492637391861703109)
              ·
                refine ⟨158497404869510974069333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 845319492637391861703109 158497404869510974069333)
                ·
                  rfl

theorem cell19_520885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_520885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520885 prefixEnd_520885 := by exact prefixLift 520885
  have htrace : WordTrace (prefixWord ++ tailWord_520885) baseStart_520885 baseEnd_520885 := by
    simpa [prefixWord, tailWord_520885, baseEnd_520885] using wordTrace_append hprefix tailTrace_520885
  have hstable : (prefixWord ++ tailWord_520885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520885).length < 2 ^ (prefixWord ++ tailWord_520885).sum := by decide
  have hdescent : baseEnd_520885 < baseStart_520885 := by decide
  rcases family_descends (prefixWord ++ tailWord_520885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520906 : List Nat := [3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_520906 : Nat := 118140960795 + 520906 * 2 ^ 59
def prefixEnd_520906 : Nat := 4983230072969 + 3 ^ 40 * 520906 * 2
def baseEnd_520906 : Nat := 158503794850989147602609

theorem tailTrace_520906 : CollatzResearch.WordTrace tailWord_520906 prefixEnd_520906 158503794850989147602609 := by
  unfold tailWord_520906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4749750662713500126787643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12666001767236000338100381 4749750662713500126787643)
  ·
    refine ⟨7124625994070250190181465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4749750662713500126787643 7124625994070250190181465)
    ·
      refine ⟨5343469495552687642636099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7124625994070250190181465 5343469495552687642636099)
      ·
        refine ⟨8015204243329031463954149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5343469495552687642636099 8015204243329031463954149)
        ·
          refine ⟨1502850795624193399491403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8015204243329031463954149 1502850795624193399491403)
          ·
            refine ⟨2254276193436290099237105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502850795624193399491403 2254276193436290099237105)
            ·
              refine ⟨1690707145077217574427829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2254276193436290099237105 1690707145077217574427829)
              ·
                refine ⟨158503794850989147602609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1690707145077217574427829 158503794850989147602609)
                ·
                  rfl

theorem cell19_520906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_520906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520906 prefixEnd_520906 := by exact prefixLift 520906
  have htrace : WordTrace (prefixWord ++ tailWord_520906) baseStart_520906 baseEnd_520906 := by
    simpa [prefixWord, tailWord_520906, baseEnd_520906] using wordTrace_append hprefix tailTrace_520906
  have hstable : (prefixWord ++ tailWord_520906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520906).length < 2 ^ (prefixWord ++ tailWord_520906).sum := by decide
  have hdescent : baseEnd_520906 < baseStart_520906 := by decide
  rcases family_descends (prefixWord ++ tailWord_520906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520927 : List Nat := [1, 1, 2, 3, 2, 10]
def baseStart_520927 : Nat := 118140960795 + 520927 * 2 ^ 59
def prefixEnd_520927 : Nat := 4983230072969 + 3 ^ 40 * 520927 * 2
def baseEnd_520927 : Nat := 17612242759163035681765

theorem tailTrace_520927 : CollatzResearch.WordTrace tailWord_520927 prefixEnd_520927 17612242759163035681765 := by
  unfold tailWord_520927
  simp only [CollatzResearch.WordTrace]
  refine ⟨18999768583777921093665035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12666512389185280729110023 18999768583777921093665035)
  ·
    refine ⟨28499652875666881640497553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18999768583777921093665035 28499652875666881640497553)
    ·
      refine ⟨21374739656750161230373165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28499652875666881640497553 21374739656750161230373165)
      ·
        refine ⟨8015527371281310461389937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21374739656750161230373165 8015527371281310461389937)
        ·
          refine ⟨6011645528460982846042453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8015527371281310461389937 6011645528460982846042453)
          ·
            refine ⟨17612242759163035681765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6011645528460982846042453 17612242759163035681765)
            ·
              rfl

theorem cell19_520927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 10].length) (baseStart_520927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520927 prefixEnd_520927 := by exact prefixLift 520927
  have htrace : WordTrace (prefixWord ++ tailWord_520927) baseStart_520927 baseEnd_520927 := by
    simpa [prefixWord, tailWord_520927, baseEnd_520927] using wordTrace_append hprefix tailTrace_520927
  have hstable : (prefixWord ++ tailWord_520927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520927).length < 2 ^ (prefixWord ++ tailWord_520927).sum := by decide
  have hdescent : baseEnd_520927 < baseStart_520927 := by decide
  rcases family_descends (prefixWord ++ tailWord_520927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520942 : List Nat := [4, 1, 2, 1, 1, 5, 1, 4]
def baseStart_520942 : Nat := 118140960795 + 520942 * 2 ^ 59
def prefixEnd_520942 : Nat := 4983230072969 + 3 ^ 40 * 520942 * 2
def baseEnd_520942 : Nat := 158514749104951730802511

theorem tailTrace_520942 : CollatzResearch.WordTrace tailWord_520942 prefixEnd_520942 158514749104951730802511 := by
  unfold tailWord_520942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2375039459840447331932635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12666877119149052436974053 2375039459840447331932635)
  ·
    refine ⟨3562559189760670997898953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2375039459840447331932635 3562559189760670997898953)
    ·
      refine ⟨2671919392320503248424215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3562559189760670997898953 2671919392320503248424215)
      ·
        refine ⟨4007879088480754872636323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671919392320503248424215 4007879088480754872636323)
        ·
          refine ⟨6011818632721132308954485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007879088480754872636323 6011818632721132308954485)
          ·
            refine ⟨563607996817606153964483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6011818632721132308954485 563607996817606153964483)
            ·
              refine ⟨845411995226409230946725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563607996817606153964483 845411995226409230946725)
              ·
                refine ⟨158514749104951730802511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 845411995226409230946725 158514749104951730802511)
                ·
                  rfl

theorem cell19_520942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_520942 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520942 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520942 prefixEnd_520942 := by exact prefixLift 520942
  have htrace : WordTrace (prefixWord ++ tailWord_520942) baseStart_520942 baseEnd_520942 := by
    simpa [prefixWord, tailWord_520942, baseEnd_520942] using wordTrace_append hprefix tailTrace_520942
  have hstable : (prefixWord ++ tailWord_520942).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520942).length < 2 ^ (prefixWord ++ tailWord_520942).sum := by decide
  have hdescent : baseEnd_520942 < baseStart_520942 := by decide
  rcases family_descends (prefixWord ++ tailWord_520942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520965 : List Nat := [1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_520965 : Nat := 118140960795 + 520965 * 2 ^ 59
def prefixEnd_520965 : Nat := 4983230072969 + 3 ^ 40 * 520965 * 2
def baseEnd_520965 : Nat := 158521747656094492291337

theorem tailTrace_520965 : CollatzResearch.WordTrace tailWord_520965 prefixEnd_520965 158521747656094492291337 := by
  unfold tailWord_520965
  simp only [CollatzResearch.WordTrace]
  refine ⟨19001154557640253583548349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12667436371760169055698899 19001154557640253583548349)
  ·
    refine ⟨7125432959115095093830631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19001154557640253583548349 7125432959115095093830631)
    ·
      refine ⟨10688149438672642640745947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7125432959115095093830631 10688149438672642640745947)
      ·
        refine ⟨16032224158008963961118921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10688149438672642640745947 16032224158008963961118921)
        ·
          refine ⟨12024168118506722970839191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16032224158008963961118921 12024168118506722970839191)
          ·
            refine ⟨18036252177760084456258787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12024168118506722970839191 18036252177760084456258787)
            ·
              refine ⟨27054378266640126684388181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18036252177760084456258787 27054378266640126684388181)
              ·
                refine ⟨158521747656094492291337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27054378266640126684388181 158521747656094492291337)
                ·
                  rfl

theorem cell19_520965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_520965 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_520965 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_520965 prefixEnd_520965 := by exact prefixLift 520965
  have htrace : WordTrace (prefixWord ++ tailWord_520965) baseStart_520965 baseEnd_520965 := by
    simpa [prefixWord, tailWord_520965, baseEnd_520965] using wordTrace_append hprefix tailTrace_520965
  have hstable : (prefixWord ++ tailWord_520965).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520965).length < 2 ^ (prefixWord ++ tailWord_520965).sum := by decide
  have hdescent : baseEnd_520965 < baseStart_520965 := by decide
  rcases family_descends (prefixWord ++ tailWord_520965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521014 : List Nat := [5, 1, 2, 2, 2, 2, 2, 3]
def baseStart_521014 : Nat := 118140960795 + 521014 * 2 ^ 59
def prefixEnd_521014 : Nat := 4983230072969 + 3 ^ 40 * 521014 * 2
def baseEnd_521014 : Nat := 158536657612876897202315

theorem tailTrace_521014 : CollatzResearch.WordTrace tailWord_521014 prefixEnd_521014 158536657612876897202315 := by
  unfold tailWord_521014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1187683858403920934505131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12668627822975156634721397 1187683858403920934505131)
  ·
    refine ⟨1781525787605881401757697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1187683858403920934505131 1781525787605881401757697)
    ·
      refine ⟨1336144340704411051318273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1781525787605881401757697 1336144340704411051318273)
      ·
        refine ⟨1002108255528308288488705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1336144340704411051318273 1002108255528308288488705)
        ·
          refine ⟨751581191646231216366529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1002108255528308288488705 751581191646231216366529)
          ·
            refine ⟨563685893734673412274897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751581191646231216366529 563685893734673412274897)
            ·
              refine ⟨422764420301005059206173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563685893734673412274897 422764420301005059206173)
              ·
                refine ⟨158536657612876897202315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422764420301005059206173 158536657612876897202315)
                ·
                  rfl

theorem cell19_521014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_521014 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521014 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521014 prefixEnd_521014 := by exact prefixLift 521014
  have htrace : WordTrace (prefixWord ++ tailWord_521014) baseStart_521014 baseEnd_521014 := by
    simpa [prefixWord, tailWord_521014, baseEnd_521014] using wordTrace_append hprefix tailTrace_521014
  have hstable : (prefixWord ++ tailWord_521014).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521014).length < 2 ^ (prefixWord ++ tailWord_521014).sum := by decide
  have hdescent : baseEnd_521014 < baseStart_521014 := by decide
  rcases family_descends (prefixWord ++ tailWord_521014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521077 : List Nat := [1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_521077 : Nat := 118140960795 + 521077 * 2 ^ 59
def prefixEnd_521077 : Nat := 4983230072969 + 3 ^ 40 * 521077 * 2
def baseEnd_521077 : Nat := 158555827557311417802143

theorem tailTrace_521077 : CollatzResearch.WordTrace tailWord_521077 prefixEnd_521077 158555827557311417802143 := by
  unfold tailWord_521077
  simp only [CollatzResearch.WordTrace]
  refine ⟨19005239533234496711625485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12670159688822997807750323 19005239533234496711625485)
  ·
    refine ⟨7126964824962936266859557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19005239533234496711625485 7126964824962936266859557)
    ·
      refine ⟨1336305904680550550036167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7126964824962936266859557 1336305904680550550036167)
      ·
        refine ⟨2004458857020825825054251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336305904680550550036167 2004458857020825825054251)
        ·
          refine ⟨3006688285531238737581377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2004458857020825825054251 3006688285531238737581377)
          ·
            refine ⟨2255016214148429053186033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3006688285531238737581377 2255016214148429053186033)
            ·
              refine ⟨1691262160611321789889525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255016214148429053186033 1691262160611321789889525)
              ·
                refine ⟨158555827557311417802143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1691262160611321789889525 158555827557311417802143)
                ·
                  rfl

theorem cell19_521077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_521077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521077 prefixEnd_521077 := by exact prefixLift 521077
  have htrace : WordTrace (prefixWord ++ tailWord_521077) baseStart_521077 baseEnd_521077 := by
    simpa [prefixWord, tailWord_521077, baseEnd_521077] using wordTrace_append hprefix tailTrace_521077
  have hstable : (prefixWord ++ tailWord_521077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521077).length < 2 ^ (prefixWord ++ tailWord_521077).sum := by decide
  have hdescent : baseEnd_521077 < baseStart_521077 := by decide
  rcases family_descends (prefixWord ++ tailWord_521077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521189 : List Nat := [1, 3, 1, 6, 1, 1, 1, 5]
def baseStart_521189 : Nat := 118140960795 + 521189 * 2 ^ 59
def prefixEnd_521189 : Nat := 4983230072969 + 3 ^ 40 * 521189 * 2
def baseEnd_521189 : Nat := 158589907458528343312949

theorem tailTrace_521189 : CollatzResearch.WordTrace tailWord_521189 prefixEnd_521189 158589907458528343312949 := by
  unfold tailWord_521189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009324508828739839702621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12672883005885826559801747 19009324508828739839702621)
  ·
    refine ⟨7128496690810777439888483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19009324508828739839702621 7128496690810777439888483)
    ·
      refine ⟨10692745036216166159832725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7128496690810777439888483 10692745036216166159832725)
      ·
        refine ⟨501222423572632788742159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10692745036216166159832725 501222423572632788742159)
        ·
          refine ⟨751833635358949183113239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501222423572632788742159 751833635358949183113239)
          ·
            refine ⟨1127750453038423774669859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751833635358949183113239 1127750453038423774669859)
            ·
              refine ⟨1691625679557635662004789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127750453038423774669859 1691625679557635662004789)
              ·
                refine ⟨158589907458528343312949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1691625679557635662004789 158589907458528343312949)
                ·
                  rfl

theorem cell19_521189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 5].length) (baseStart_521189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521189 prefixEnd_521189 := by exact prefixLift 521189
  have htrace : WordTrace (prefixWord ++ tailWord_521189) baseStart_521189 baseEnd_521189 := by
    simpa [prefixWord, tailWord_521189, baseEnd_521189] using wordTrace_append hprefix tailTrace_521189
  have hstable : (prefixWord ++ tailWord_521189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521189).length < 2 ^ (prefixWord ++ tailWord_521189).sum := by decide
  have hdescent : baseEnd_521189 < baseStart_521189 := by decide
  rcases family_descends (prefixWord ++ tailWord_521189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521191 : List Nat := [1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_521191 : Nat := 118140960795 + 521191 * 2 ^ 59
def prefixEnd_521191 : Nat := 4983230072969 + 3 ^ 40 * 521191 * 2
def baseEnd_521191 : Nat := 158590516028192931268499

theorem tailTrace_521191 : CollatzResearch.WordTrace tailWord_521191 prefixEnd_521191 158590516028192931268499 := by
  unfold tailWord_521191
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009397454821494181275427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12672931636547662787516951 19009397454821494181275427)
  ·
    refine ⟨28514096182232241271913141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19009397454821494181275427 28514096182232241271913141)
    ·
      refine ⟨2673196517084272619241857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28514096182232241271913141 2673196517084272619241857)
      ·
        refine ⟨2004897387813204464431393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673196517084272619241857 2004897387813204464431393)
        ·
          refine ⟨1503673040859903348323545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2004897387813204464431393 1503673040859903348323545)
          ·
            refine ⟨1127754780644927511242659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503673040859903348323545 1127754780644927511242659)
            ·
              refine ⟨1691632170967391266863989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127754780644927511242659 1691632170967391266863989)
              ·
                refine ⟨158590516028192931268499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1691632170967391266863989 158590516028192931268499)
                ·
                  rfl

theorem cell19_521191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_521191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521191 prefixEnd_521191 := by exact prefixLift 521191
  have htrace : WordTrace (prefixWord ++ tailWord_521191) baseStart_521191 baseEnd_521191 := by
    simpa [prefixWord, tailWord_521191, baseEnd_521191] using wordTrace_append hprefix tailTrace_521191
  have hstable : (prefixWord ++ tailWord_521191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521191).length < 2 ^ (prefixWord ++ tailWord_521191).sum := by decide
  have hdescent : baseEnd_521191 < baseStart_521191 := by decide
  rcases family_descends (prefixWord ++ tailWord_521191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521212 : List Nat := [2, 2, 2, 1, 2, 3, 7]
def baseStart_521212 : Nat := 118140960795 + 521212 * 2 ^ 59
def prefixEnd_521212 : Nat := 4983230072969 + 3 ^ 40 * 521212 * 2
def baseEnd_521212 : Nat := 52865635336557034933925

theorem tailTrace_521212 : CollatzResearch.WordTrace tailWord_521212 prefixEnd_521212 52865635336557034933925 := by
  unfold tailWord_521212
  simp only [CollatzResearch.WordTrace]
  refine ⟨9505081693872707383894945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12673442258496943178526593 9505081693872707383894945)
  ·
    refine ⟨7128811270404530537921209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9505081693872707383894945 7128811270404530537921209)
    ·
      refine ⟨5346608452803397903440907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7128811270404530537921209 5346608452803397903440907)
      ·
        refine ⟨8019912679205096855161361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5346608452803397903440907 8019912679205096855161361)
        ·
          refine ⟨6014934509403822641371021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8019912679205096855161361 6014934509403822641371021)
          ·
            refine ⟨2255600441026433490514133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6014934509403822641371021 2255600441026433490514133)
            ·
              refine ⟨52865635336557034933925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2255600441026433490514133 52865635336557034933925)
              ·
                rfl

theorem cell19_521212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_521212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521212 prefixEnd_521212 := by exact prefixLift 521212
  have htrace : WordTrace (prefixWord ++ tailWord_521212) baseStart_521212 baseEnd_521212 := by
    simpa [prefixWord, tailWord_521212, baseEnd_521212] using wordTrace_append hprefix tailTrace_521212
  have hstable : (prefixWord ++ tailWord_521212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521212).length < 2 ^ (prefixWord ++ tailWord_521212).sum := by decide
  have hdescent : baseEnd_521212 < baseStart_521212 := by decide
  rcases family_descends (prefixWord ++ tailWord_521212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521362 : List Nat := [3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_521362 : Nat := 118140960795 + 521362 * 2 ^ 59
def prefixEnd_521362 : Nat := 4983230072969 + 3 ^ 40 * 521362 * 2
def baseEnd_521362 : Nat := 158642548734515201468033

theorem tailTrace_521362 : CollatzResearch.WordTrace tailWord_521362 prefixEnd_521362 158642548734515201468033 := by
  unfold tailWord_521362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753908584300497596437585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12677089558134660257166893 4753908584300497596437585)
  ·
    refine ⟨3565431438225373197328189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4753908584300497596437585 3565431438225373197328189)
    ·
      refine ⟨1337036789334514948998071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3565431438225373197328189 1337036789334514948998071)
      ·
        refine ⟨2005555184001772423497107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1337036789334514948998071 2005555184001772423497107)
        ·
          refine ⟨3008332776002658635245661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005555184001772423497107 3008332776002658635245661)
          ·
            refine ⟨1128124791000996988217123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3008332776002658635245661 1128124791000996988217123)
            ·
              refine ⟨1692187186501495482325685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128124791000996988217123 1692187186501495482325685)
              ·
                refine ⟨158642548734515201468033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1692187186501495482325685 158642548734515201468033)
                ·
                  rfl

theorem cell19_521362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_521362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521362 prefixEnd_521362 := by exact prefixLift 521362
  have htrace : WordTrace (prefixWord ++ tailWord_521362) baseStart_521362 baseEnd_521362 := by
    simpa [prefixWord, tailWord_521362, baseEnd_521362] using wordTrace_append hprefix tailTrace_521362
  have hstable : (prefixWord ++ tailWord_521362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521362).length < 2 ^ (prefixWord ++ tailWord_521362).sum := by decide
  have hdescent : baseEnd_521362 < baseStart_521362 := by decide
  rcases family_descends (prefixWord ++ tailWord_521362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
