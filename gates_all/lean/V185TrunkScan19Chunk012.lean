import V185TrunkScan19Chunk011

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_121567 : List Nat := [1, 1, 2, 3, 2, 3, 7]
def baseStart_121567 : Nat := 118140960795 + 121567 * 2 ^ 59
def prefixEnd_121567 : Nat := 4983230072969 + 3 ^ 40 * 121567 * 2
def baseEnd_121567 : Nat := 12330331402514785630307

theorem tailTrace_121567 : CollatzResearch.WordTrace tailWord_121567 prefixEnd_121567 12330331402514785630307 := by
  unfold tailWord_121567
  simp only [CollatzResearch.WordTrace]
  refine ⟨4433912750590995835762955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2955941833727330557175303 4433912750590995835762955)
  ·
    refine ⟨6650869125886493753644433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4433912750590995835762955 6650869125886493753644433)
    ·
      refine ⟨4988151844414870315233325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6650869125886493753644433 4988151844414870315233325)
      ·
        refine ⟨1870556941655576368212497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4988151844414870315233325 1870556941655576368212497)
        ·
          refine ⟨1402917706241682276159373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870556941655576368212497 1402917706241682276159373)
          ·
            refine ⟨526094139840630853559765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1402917706241682276159373 526094139840630853559765)
            ·
              refine ⟨12330331402514785630307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 526094139840630853559765 12330331402514785630307)
              ·
                rfl

theorem cell19_121567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_121567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121567 prefixEnd_121567 := by exact prefixLift 121567
  have htrace : WordTrace (prefixWord ++ tailWord_121567) baseStart_121567 baseEnd_121567 := by
    simpa [prefixWord, tailWord_121567, baseEnd_121567] using wordTrace_append hprefix tailTrace_121567
  have hstable : (prefixWord ++ tailWord_121567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121567).length < 2 ^ (prefixWord ++ tailWord_121567).sum := by decide
  have hdescent : baseEnd_121567 < baseStart_121567 := by decide
  rcases family_descends (prefixWord ++ tailWord_121567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121658 : List Nat := [3, 1, 1, 1, 6, 1, 3, 3]
def baseStart_121658 : Nat := 118140960795 + 121658 * 2 ^ 59
def prefixEnd_121658 : Nat := 4983230072969 + 3 ^ 40 * 121658 * 2
def baseEnd_121658 : Nat := 37018684127283108868451

theorem tailTrace_121658 : CollatzResearch.WordTrace tailWord_121658 prefixEnd_121658 37018684127283108868451 := by
  unfold tailWord_121658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1109307948315329594331407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2958154528840878918217085 1109307948315329594331407)
  ·
    refine ⟨1663961922472994391497111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1109307948315329594331407 1663961922472994391497111)
    ·
      refine ⟨2495942883709491587245667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1663961922472994391497111 2495942883709491587245667)
      ·
        refine ⟨3743914325564237380868501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495942883709491587245667 3743914325564237380868501)
        ·
          refine ⟨175495984010823627228211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3743914325564237380868501 175495984010823627228211)
          ·
            refine ⟨263243976016235440842317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175495984010823627228211 263243976016235440842317)
            ·
              refine ⟨98716491006088290315869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263243976016235440842317 98716491006088290315869)
              ·
                refine ⟨37018684127283108868451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98716491006088290315869 37018684127283108868451)
                ·
                  rfl

theorem cell19_121658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_121658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121658 prefixEnd_121658 := by exact prefixLift 121658
  have htrace : WordTrace (prefixWord ++ tailWord_121658) baseStart_121658 baseEnd_121658 := by
    simpa [prefixWord, tailWord_121658, baseEnd_121658] using wordTrace_append hprefix tailTrace_121658
  have hstable : (prefixWord ++ tailWord_121658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121658).length < 2 ^ (prefixWord ++ tailWord_121658).sum := by decide
  have hdescent : baseEnd_121658 < baseStart_121658 := by decide
  rcases family_descends (prefixWord ++ tailWord_121658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121677 : List Nat := [1, 6, 1, 2, 2, 1, 6]
def baseStart_121677 : Nat := 118140960795 + 121677 * 2 ^ 59
def prefixEnd_121677 : Nat := 4983230072969 + 3 ^ 40 * 121677 * 2
def baseEnd_121677 : Nat := 12341488513032231482059

theorem tailTrace_121677 : CollatzResearch.WordTrace tailWord_121677 prefixEnd_121677 12341488513032231482059 := by
  unfold tailWord_121677
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437924780192484622267285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2958616520128323081511523 4437924780192484622267285)
  ·
    refine ⟨208027724071522716668779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4437924780192484622267285 208027724071522716668779)
    ·
      refine ⟨312041586107284075003169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208027724071522716668779 312041586107284075003169)
      ·
        refine ⟨234031189580463056252377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312041586107284075003169 234031189580463056252377)
        ·
          refine ⟨175523392185347292189283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234031189580463056252377 175523392185347292189283)
          ·
            refine ⟨263285088278020938283925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175523392185347292189283 263285088278020938283925)
            ·
              refine ⟨12341488513032231482059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263285088278020938283925 12341488513032231482059)
              ·
                rfl

theorem cell19_121677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_121677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121677 prefixEnd_121677 := by exact prefixLift 121677
  have htrace : WordTrace (prefixWord ++ tailWord_121677) baseStart_121677 baseEnd_121677 := by
    simpa [prefixWord, tailWord_121677, baseEnd_121677] using wordTrace_append hprefix tailTrace_121677
  have hstable : (prefixWord ++ tailWord_121677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121677).length < 2 ^ (prefixWord ++ tailWord_121677).sum := by decide
  have hdescent : baseEnd_121677 < baseStart_121677 := by decide
  rcases family_descends (prefixWord ++ tailWord_121677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121717 : List Nat := [1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_121717 : Nat := 118140960795 + 121717 * 2 ^ 59
def prefixEnd_121717 : Nat := 4983230072969 + 3 ^ 40 * 121717 * 2
def baseEnd_121717 : Nat := 37036636932388453557179

theorem tailTrace_121717 : CollatzResearch.WordTrace tailWord_121717 prefixEnd_121717 37036636932388453557179 := by
  unfold tailWord_121717
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439383700047571453723405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2959589133365047635815603 4439383700047571453723405)
  ·
    refine ⟨1664768887517839295146277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4439383700047571453723405 1664768887517839295146277)
    ·
      refine ⟨312144166409594867839927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1664768887517839295146277 312144166409594867839927)
      ·
        refine ⟨468216249614392301759891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312144166409594867839927 468216249614392301759891)
        ·
          refine ⟨702324374421588452639837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468216249614392301759891 702324374421588452639837)
          ·
            refine ⟨263371640408095669739939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 702324374421588452639837 263371640408095669739939)
            ·
              refine ⟨395057460612143504609909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263371640408095669739939 395057460612143504609909)
              ·
                refine ⟨37036636932388453557179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 395057460612143504609909 37036636932388453557179)
                ·
                  rfl

theorem cell19_121717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_121717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121717 prefixEnd_121717 := by exact prefixLift 121717
  have htrace : WordTrace (prefixWord ++ tailWord_121717) baseStart_121717 baseEnd_121717 := by
    simpa [prefixWord, tailWord_121717, baseEnd_121717] using wordTrace_append hprefix tailTrace_121717
  have hstable : (prefixWord ++ tailWord_121717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121717).length < 2 ^ (prefixWord ++ tailWord_121717).sum := by decide
  have hdescent : baseEnd_121717 < baseStart_121717 := by decide
  rcases family_descends (prefixWord ++ tailWord_121717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121730 : List Nat := [3, 4, 2, 2, 2, 1, 5]
def baseStart_121730 : Nat := 118140960795 + 121730 * 2 ^ 59
def prefixEnd_121730 : Nat := 4983230072969 + 3 ^ 40 * 121730 * 2
def baseEnd_121730 : Nat := 12346864211736091756085

theorem tailTrace_121730 : CollatzResearch.WordTrace tailWord_121730 prefixEnd_121730 12346864211736091756085 := by
  unfold tailWord_121730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1109964462250118668486661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2959905232666983115964429 1109964462250118668486661)
  ·
    refine ⟨208118336671897250341249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1109964462250118668486661 208118336671897250341249)
    ·
      refine ⟨156088752503922937755937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208118336671897250341249 156088752503922937755937)
      ·
        refine ⟨117066564377942203316953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156088752503922937755937 117066564377942203316953)
        ·
          refine ⟨87799923283456652487715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117066564377942203316953 87799923283456652487715)
          ·
            refine ⟨131699884925184978731573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87799923283456652487715 131699884925184978731573)
            ·
              refine ⟨12346864211736091756085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131699884925184978731573 12346864211736091756085)
              ·
                rfl

theorem cell19_121730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 5].length) (baseStart_121730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121730 prefixEnd_121730 := by exact prefixLift 121730
  have htrace : WordTrace (prefixWord ++ tailWord_121730) baseStart_121730 baseEnd_121730 := by
    simpa [prefixWord, tailWord_121730, baseEnd_121730] using wordTrace_append hprefix tailTrace_121730
  have hstable : (prefixWord ++ tailWord_121730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121730).length < 2 ^ (prefixWord ++ tailWord_121730).sum := by decide
  have hdescent : baseEnd_121730 < baseStart_121730 := by decide
  rcases family_descends (prefixWord ++ tailWord_121730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121736 : List Nat := [2, 1, 3, 3, 2, 3, 5]
def baseStart_121736 : Nat := 118140960795 + 121736 * 2 ^ 59
def prefixEnd_121736 : Nat := 4983230072969 + 3 ^ 40 * 121736 * 2
def baseEnd_121736 : Nat := 12347472781400679711635

theorem tailTrace_121736 : CollatzResearch.WordTrace tailWord_121736 prefixEnd_121736 12347472781400679711635 := by
  unfold tailWord_121736
  simp only [CollatzResearch.WordTrace]
  refine ⟨2220038343489368849332531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2960051124652491799110041 2220038343489368849332531)
  ·
    refine ⟨3330057515234053273998797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2220038343489368849332531 3330057515234053273998797)
    ·
      refine ⟨1248771568212769977749549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3330057515234053273998797 1248771568212769977749549)
      ·
        refine ⟨468289338079788741656081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1248771568212769977749549 468289338079788741656081)
        ·
          refine ⟨351217003559841556242061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468289338079788741656081 351217003559841556242061)
          ·
            refine ⟨131706376334940583590773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351217003559841556242061 131706376334940583590773)
            ·
              refine ⟨12347472781400679711635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131706376334940583590773 12347472781400679711635)
              ·
                rfl

theorem cell19_121736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_121736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121736 prefixEnd_121736 := by exact prefixLift 121736
  have htrace : WordTrace (prefixWord ++ tailWord_121736) baseStart_121736 baseEnd_121736 := by
    simpa [prefixWord, tailWord_121736, baseEnd_121736] using wordTrace_append hprefix tailTrace_121736
  have hstable : (prefixWord ++ tailWord_121736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121736).length < 2 ^ (prefixWord ++ tailWord_121736).sum := by decide
  have hdescent : baseEnd_121736 < baseStart_121736 := by decide
  rcases family_descends (prefixWord ++ tailWord_121736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121810 : List Nat := [3, 2, 2, 3, 1, 3, 1, 4]
def baseStart_121810 : Nat := 118140960795 + 121810 * 2 ^ 59
def prefixEnd_121810 : Nat := 4983230072969 + 3 ^ 40 * 121810 * 2
def baseEnd_121810 : Nat := 37064935421791793490259

theorem tailTrace_121810 : CollatzResearch.WordTrace tailWord_121810 prefixEnd_121810 37064935421791793490259 := by
  unfold tailWord_121810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110693922177662084214721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2961850459140432224572589 1110693922177662084214721)
  ·
    refine ⟨833020441633246563161041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1110693922177662084214721 833020441633246563161041)
    ·
      refine ⟨624765331224934922370781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 833020441633246563161041 624765331224934922370781)
      ·
        refine ⟨234286999209350595889043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 624765331224934922370781 234286999209350595889043)
        ·
          refine ⟨351430498814025893833565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234286999209350595889043 351430498814025893833565)
          ·
            refine ⟨131786437055259710187587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351430498814025893833565 131786437055259710187587)
            ·
              refine ⟨197679655582889565281381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131786437055259710187587 197679655582889565281381)
              ·
                refine ⟨37064935421791793490259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197679655582889565281381 37064935421791793490259)
                ·
                  rfl

theorem cell19_121810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_121810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121810 prefixEnd_121810 := by exact prefixLift 121810
  have htrace : WordTrace (prefixWord ++ tailWord_121810) baseStart_121810 baseEnd_121810 := by
    simpa [prefixWord, tailWord_121810, baseEnd_121810] using wordTrace_append hprefix tailTrace_121810
  have hstable : (prefixWord ++ tailWord_121810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121810).length < 2 ^ (prefixWord ++ tailWord_121810).sum := by decide
  have hdescent : baseEnd_121810 < baseStart_121810 := by decide
  rcases family_descends (prefixWord ++ tailWord_121810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121812 : List Nat := [2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_121812 : Nat := 118140960795 + 121812 * 2 ^ 59
def prefixEnd_121812 : Nat := 4983230072969 + 3 ^ 40 * 121812 * 2
def baseEnd_121812 : Nat := 37065543991456381445809

theorem tailTrace_121812 : CollatzResearch.WordTrace tailWord_121812 prefixEnd_121812 37065543991456381445809 := by
  unfold tailWord_121812
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221424317351701339215845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2961899089802268452287793 2221424317351701339215845)
  ·
    refine ⟨416517059503444001102971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2221424317351701339215845 416517059503444001102971)
    ·
      refine ⟨624775589255166001654457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416517059503444001102971 624775589255166001654457)
      ·
        refine ⟨468581691941374501240843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624775589255166001654457 468581691941374501240843)
        ·
          refine ⟨702872537912061751861265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468581691941374501240843 702872537912061751861265)
          ·
            refine ⟨527154403434046313895949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702872537912061751861265 527154403434046313895949)
            ·
              refine ⟨197682901287767367710981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527154403434046313895949 197682901287767367710981)
              ·
                refine ⟨37065543991456381445809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197682901287767367710981 37065543991456381445809)
                ·
                  rfl

theorem cell19_121812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_121812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121812 prefixEnd_121812 := by exact prefixLift 121812
  have htrace : WordTrace (prefixWord ++ tailWord_121812) baseStart_121812 baseEnd_121812 := by
    simpa [prefixWord, tailWord_121812, baseEnd_121812] using wordTrace_append hprefix tailTrace_121812
  have hstable : (prefixWord ++ tailWord_121812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121812).length < 2 ^ (prefixWord ++ tailWord_121812).sum := by decide
  have hdescent : baseEnd_121812 < baseStart_121812 := by decide
  rcases family_descends (prefixWord ++ tailWord_121812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121844 : List Nat := [2, 6, 2, 1, 1, 1, 6]
def baseStart_121844 : Nat := 118140960795 + 121844 * 2 ^ 59
def prefixEnd_121844 : Nat := 4983230072969 + 3 ^ 40 * 121844 * 2
def baseEnd_121844 : Nat := 12358427035363262911537

theorem tailTrace_121844 : CollatzResearch.WordTrace tailWord_121844 prefixEnd_121844 12358427035363262911537 := by
  unfold tailWord_121844
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222007885293736071798293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2962677180391648095731057 2222007885293736071798293)
  ·
    refine ⟨104156619623143878365545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2222007885293736071798293 104156619623143878365545)
    ·
      refine ⟨78117464717357908774159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104156619623143878365545 78117464717357908774159)
      ·
        refine ⟨117176197076036863161239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78117464717357908774159 117176197076036863161239)
        ·
          refine ⟨175764295614055294741859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117176197076036863161239 175764295614055294741859)
          ·
            refine ⟨263646443421082942112789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175764295614055294741859 263646443421082942112789)
            ·
              refine ⟨12358427035363262911537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263646443421082942112789 12358427035363262911537)
              ·
                rfl

theorem cell19_121844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 6].length) (baseStart_121844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121844 prefixEnd_121844 := by exact prefixLift 121844
  have htrace : WordTrace (prefixWord ++ tailWord_121844) baseStart_121844 baseEnd_121844 := by
    simpa [prefixWord, tailWord_121844, baseEnd_121844] using wordTrace_append hprefix tailTrace_121844
  have hstable : (prefixWord ++ tailWord_121844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121844).length < 2 ^ (prefixWord ++ tailWord_121844).sum := by decide
  have hdescent : baseEnd_121844 < baseStart_121844 := by decide
  rcases family_descends (prefixWord ++ tailWord_121844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121852 : List Nat := [2, 2, 2, 1, 2, 4, 6]
def baseStart_121852 : Nat := 118140960795 + 121852 * 2 ^ 59
def prefixEnd_121852 : Nat := 4983230072969 + 3 ^ 40 * 121852 * 2
def baseEnd_121852 : Nat := 12359238461582713518937

theorem tailTrace_121852 : CollatzResearch.WordTrace tailWord_121852 prefixEnd_121852 12359238461582713518937 := by
  unfold tailWord_121852
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222153777279244754943905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2962871703038993006591873 2222153777279244754943905)
  ·
    refine ⟨1666615332959433566207929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2222153777279244754943905 1666615332959433566207929)
    ·
      refine ⟨1249961499719575174655947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1666615332959433566207929 1249961499719575174655947)
      ·
        refine ⟨1874942249579362761983921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249961499719575174655947 1874942249579362761983921)
        ·
          refine ⟨1406206687184522071487941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1874942249579362761983921 1406206687184522071487941)
          ·
            refine ⟨263663753847097888403989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1406206687184522071487941 263663753847097888403989)
            ·
              refine ⟨12359238461582713518937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263663753847097888403989 12359238461582713518937)
              ·
                rfl

theorem cell19_121852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_121852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121852 prefixEnd_121852 := by exact prefixLift 121852
  have htrace : WordTrace (prefixWord ++ tailWord_121852) baseStart_121852 baseEnd_121852 := by
    simpa [prefixWord, tailWord_121852, baseEnd_121852] using wordTrace_append hprefix tailTrace_121852
  have hstable : (prefixWord ++ tailWord_121852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121852).length < 2 ^ (prefixWord ++ tailWord_121852).sum := by decide
  have hdescent : baseEnd_121852 < baseStart_121852 := by decide
  rcases family_descends (prefixWord ++ tailWord_121852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121884 : List Nat := [2, 2, 3, 1, 5, 1, 2, 3]
def baseStart_121884 : Nat := 118140960795 + 121884 * 2 ^ 59
def prefixEnd_121884 : Nat := 4983230072969 + 3 ^ 40 * 121884 * 2
def baseEnd_121884 : Nat := 37087452499381547845613

theorem tailTrace_121884 : CollatzResearch.WordTrace tailWord_121884 prefixEnd_121884 37087452499381547845613 := by
  unfold tailWord_121884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222737345221279487526353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2963649793628372650035137 2222737345221279487526353)
  ·
    refine ⟨1667053008915959615644765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2222737345221279487526353 1667053008915959615644765)
    ·
      refine ⟨625144878343484855866787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1667053008915959615644765 625144878343484855866787)
      ·
        refine ⟨937717317515227283800181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625144878343484855866787 937717317515227283800181)
        ·
          refine ⟨87910998517052557856267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 937717317515227283800181 87910998517052557856267)
          ·
            refine ⟨131866497775578836784401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87910998517052557856267 131866497775578836784401)
            ·
              refine ⟨98899873331684127588301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131866497775578836784401 98899873331684127588301)
              ·
                refine ⟨37087452499381547845613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98899873331684127588301 37087452499381547845613)
                ·
                  rfl

theorem cell19_121884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_121884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121884 prefixEnd_121884 := by exact prefixLift 121884
  have htrace : WordTrace (prefixWord ++ tailWord_121884) baseStart_121884 baseEnd_121884 := by
    simpa [prefixWord, tailWord_121884, baseEnd_121884] using wordTrace_append hprefix tailTrace_121884
  have hstable : (prefixWord ++ tailWord_121884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121884).length < 2 ^ (prefixWord ++ tailWord_121884).sum := by decide
  have hdescent : baseEnd_121884 < baseStart_121884 := by decide
  rcases family_descends (prefixWord ++ tailWord_121884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121928 : List Nat := [2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_121928 : Nat := 118140960795 + 121928 * 2 ^ 59
def prefixEnd_121928 : Nat := 4983230072969 + 3 ^ 40 * 121928 * 2
def baseEnd_121928 : Nat := 37100841032002482867715

theorem tailTrace_121928 : CollatzResearch.WordTrace tailWord_121928 prefixEnd_121928 37100841032002482867715 := by
  unfold tailWord_121928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223539751141577244827219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2964719668188769659769625 2223539751141577244827219)
  ·
    refine ⟨3335309626712365867240829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2223539751141577244827219 3335309626712365867240829)
    ·
      refine ⟨1250741110017137200215311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3335309626712365867240829 1250741110017137200215311)
      ·
        refine ⟨1876111665025705800322967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250741110017137200215311 1876111665025705800322967)
        ·
          refine ⟨2814167497538558700484451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876111665025705800322967 2814167497538558700484451)
          ·
            refine ⟨4221251246307838050726677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814167497538558700484451 4221251246307838050726677)
            ·
              refine ⟨197871152170679908627813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4221251246307838050726677 197871152170679908627813)
              ·
                refine ⟨37100841032002482867715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197871152170679908627813 37100841032002482867715)
                ·
                  rfl

theorem cell19_121928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_121928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121928 prefixEnd_121928 := by exact prefixLift 121928
  have htrace : WordTrace (prefixWord ++ tailWord_121928) baseStart_121928 baseEnd_121928 := by
    simpa [prefixWord, tailWord_121928, baseEnd_121928] using wordTrace_append hprefix tailTrace_121928
  have hstable : (prefixWord ++ tailWord_121928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121928).length < 2 ^ (prefixWord ++ tailWord_121928).sum := by decide
  have hdescent : baseEnd_121928 < baseStart_121928 := by decide
  rcases family_descends (prefixWord ++ tailWord_121928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121966 : List Nat := [4, 1, 2, 2, 1, 9]
def baseStart_121966 : Nat := 118140960795 + 121966 * 2 ^ 59
def prefixEnd_121966 : Nat := 4983230072969 + 3 ^ 40 * 121966 * 2
def baseEnd_121966 : Nat := 4123600428403294891463

theorem tailTrace_121966 : CollatzResearch.WordTrace tailWord_121966 prefixEnd_121966 4123600428403294891463 := by
  unfold tailWord_121966
  simp only [CollatzResearch.WordTrace]
  refine ⟨556058184518185872442219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2965643650763657986358501 556058184518185872442219)
  ·
    refine ⟨834087276777278808663329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 556058184518185872442219 834087276777278808663329)
    ·
      refine ⟨625565457582959106497497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 834087276777278808663329 625565457582959106497497)
      ·
        refine ⟨469174093187219329873123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625565457582959106497497 469174093187219329873123)
        ·
          refine ⟨703761139780828994809685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469174093187219329873123 703761139780828994809685)
          ·
            refine ⟨4123600428403294891463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 703761139780828994809685 4123600428403294891463)
            ·
              rfl

theorem cell19_121966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 9].length) (baseStart_121966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121966 prefixEnd_121966 := by exact prefixLift 121966
  have htrace : WordTrace (prefixWord ++ tailWord_121966) baseStart_121966 baseEnd_121966 := by
    simpa [prefixWord, tailWord_121966, baseEnd_121966] using wordTrace_append hprefix tailTrace_121966
  have hstable : (prefixWord ++ tailWord_121966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121966).length < 2 ^ (prefixWord ++ tailWord_121966).sum := by decide
  have hdescent : baseEnd_121966 < baseStart_121966 := by decide
  rcases family_descends (prefixWord ++ tailWord_121966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122080 : List Nat := [2, 1, 1, 3, 1, 6, 5]
def baseStart_122080 : Nat := 118140960795 + 122080 * 2 ^ 59
def prefixEnd_122080 : Nat := 4983230072969 + 3 ^ 40 * 122080 * 2
def baseEnd_122080 : Nat := 12382364108837055829841

theorem tailTrace_122080 : CollatzResearch.WordTrace tailWord_122080 prefixEnd_122080 12382364108837055829841 := by
  unfold tailWord_122080
  simp only [CollatzResearch.WordTrace]
  refine ⟨2226311698866242224593847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2968415598488322966125129 2226311698866242224593847)
  ·
    refine ⟨3339467548299363336890771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2226311698866242224593847 3339467548299363336890771)
    ·
      refine ⟨5009201322449045005336157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3339467548299363336890771 5009201322449045005336157)
      ·
        refine ⟨1878450495918391877001059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5009201322449045005336157 1878450495918391877001059)
        ·
          refine ⟨2817675743877587815501589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878450495918391877001059 2817675743877587815501589)
          ·
            refine ⟨132078550494261928851637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2817675743877587815501589 132078550494261928851637)
            ·
              refine ⟨12382364108837055829841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132078550494261928851637 12382364108837055829841)
              ·
                rfl

theorem cell19_122080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_122080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122080 prefixEnd_122080 := by exact prefixLift 122080
  have htrace : WordTrace (prefixWord ++ tailWord_122080) baseStart_122080 baseEnd_122080 := by
    simpa [prefixWord, tailWord_122080, baseEnd_122080] using wordTrace_append hprefix tailTrace_122080
  have hstable : (prefixWord ++ tailWord_122080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122080).length < 2 ^ (prefixWord ++ tailWord_122080).sum := by decide
  have hdescent : baseEnd_122080 < baseStart_122080 := by decide
  rcases family_descends (prefixWord ++ tailWord_122080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122099 : List Nat := [1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_122099 : Nat := 118140960795 + 122099 * 2 ^ 59
def prefixEnd_122099 : Nat := 4983230072969 + 3 ^ 40 * 122099 * 2
def baseEnd_122099 : Nat := 37152873738324753067249

theorem tailTrace_122099 : CollatzResearch.WordTrace tailWord_122099 prefixEnd_122099 37152873738324753067249 := by
  unfold tailWord_122099
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453316384663650694129351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2968877589775767129419567 4453316384663650694129351)
  ·
    refine ⟨6679974576995476041194027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4453316384663650694129351 6679974576995476041194027)
    ·
      refine ⟨10019961865493214061791041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6679974576995476041194027 10019961865493214061791041)
      ·
        refine ⟨7514971399119910546343281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10019961865493214061791041 7514971399119910546343281)
        ·
          refine ⟨5636228549339932909757461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7514971399119910546343281 5636228549339932909757461)
          ·
            refine ⟨264198213250309355144881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5636228549339932909757461 264198213250309355144881)
            ·
              refine ⟨198148659937732016358661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264198213250309355144881 198148659937732016358661)
              ·
                refine ⟨37152873738324753067249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198148659937732016358661 37152873738324753067249)
                ·
                  rfl

theorem cell19_122099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_122099 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122099 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122099 prefixEnd_122099 := by exact prefixLift 122099
  have htrace : WordTrace (prefixWord ++ tailWord_122099) baseStart_122099 baseEnd_122099 := by
    simpa [prefixWord, tailWord_122099, baseEnd_122099] using wordTrace_append hprefix tailTrace_122099
  have hstable : (prefixWord ++ tailWord_122099).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122099).length < 2 ^ (prefixWord ++ tailWord_122099).sum := by decide
  have hdescent : baseEnd_122099 < baseStart_122099 := by decide
  rcases family_descends (prefixWord ++ tailWord_122099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122154 : List Nat := [3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_122154 : Nat := 118140960795 + 122154 * 2 ^ 59
def prefixEnd_122154 : Nat := 4983230072969 + 3 ^ 40 * 122154 * 2
def baseEnd_122154 : Nat := 37169609404100921844877

theorem tailTrace_122154 : CollatzResearch.WordTrace tailWord_122154 prefixEnd_122154 37169609404100921844877 := by
  unfold tailWord_122154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113830599866098771845379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2970214932976263391587677 1113830599866098771845379)
  ·
    refine ⟨1670745899799148157768069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1113830599866098771845379 1670745899799148157768069)
    ·
      refine ⟨313264856212340279581513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1670745899799148157768069 313264856212340279581513)
      ·
        refine ⟨234948642159255209686135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313264856212340279581513 234948642159255209686135)
        ·
          refine ⟨352422963238882814529203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234948642159255209686135 352422963238882814529203)
          ·
            refine ⟨528634444858324221793805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352422963238882814529203 528634444858324221793805)
            ·
              refine ⟨198237916821871583172677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 528634444858324221793805 198237916821871583172677)
              ·
                refine ⟨37169609404100921844877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198237916821871583172677 37169609404100921844877)
                ·
                  rfl

theorem cell19_122154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_122154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122154 prefixEnd_122154 := by exact prefixLift 122154
  have htrace : WordTrace (prefixWord ++ tailWord_122154) baseStart_122154 baseEnd_122154 := by
    simpa [prefixWord, tailWord_122154, baseEnd_122154] using wordTrace_append hprefix tailTrace_122154
  have hstable : (prefixWord ++ tailWord_122154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122154).length < 2 ^ (prefixWord ++ tailWord_122154).sum := by decide
  have hdescent : baseEnd_122154 < baseStart_122154 := by decide
  rcases family_descends (prefixWord ++ tailWord_122154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122234 : List Nat := [3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_122234 : Nat := 118140960795 + 122234 * 2 ^ 59
def prefixEnd_122234 : Nat := 4983230072969 + 3 ^ 40 * 122234 * 2
def baseEnd_122234 : Nat := 37193952190684440066881

theorem tailTrace_122234 : CollatzResearch.WordTrace tailWord_122234 prefixEnd_122234 37193952190684440066881 := by
  unfold tailWord_122234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1114560059793642187573439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2972160159449712500195837 1114560059793642187573439)
  ·
    refine ⟨1671840089690463281360159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1114560059793642187573439 1671840089690463281360159)
    ·
      refine ⟨2507760134535694922040239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1671840089690463281360159 2507760134535694922040239)
      ·
        refine ⟨3761640201803542383060359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507760134535694922040239 3761640201803542383060359)
        ·
          refine ⟨5642460302705313574590539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3761640201803542383060359 5642460302705313574590539)
          ·
            refine ⟨8463690454057970361885809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642460302705313574590539 8463690454057970361885809)
            ·
              refine ⟨6347767840543477771414357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8463690454057970361885809 6347767840543477771414357)
              ·
                refine ⟨37193952190684440066881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6347767840543477771414357 37193952190684440066881)
                ·
                  rfl

theorem cell19_122234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_122234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122234 prefixEnd_122234 := by exact prefixLift 122234
  have htrace : WordTrace (prefixWord ++ tailWord_122234) baseStart_122234 baseEnd_122234 := by
    simpa [prefixWord, tailWord_122234, baseEnd_122234] using wordTrace_append hprefix tailTrace_122234
  have hstable : (prefixWord ++ tailWord_122234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122234).length < 2 ^ (prefixWord ++ tailWord_122234).sum := by decide
  have hdescent : baseEnd_122234 < baseStart_122234 := by decide
  rcases family_descends (prefixWord ++ tailWord_122234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122249 : List Nat := [1, 2, 1, 1, 8, 1, 5]
def baseStart_122249 : Nat := 118140960795 + 122249 * 2 ^ 59
def prefixEnd_122249 : Nat := 4983230072969 + 3 ^ 40 * 122249 * 2
def baseEnd_122249 : Nat := 12399505487722949911169

theorem tailTrace_122249 : CollatzResearch.WordTrace tailWord_122249 prefixEnd_122249 12399505487722949911169 := by
  unfold tailWord_122249
  simp only [CollatzResearch.WordTrace]
  refine ⟨4458787334120226312089801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2972524889413484208059867 4458787334120226312089801)
  ·
    refine ⟨3344090500590169734067351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4458787334120226312089801 3344090500590169734067351)
    ·
      refine ⟨5016135750885254601101027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3344090500590169734067351 5016135750885254601101027)
      ·
        refine ⟨7524203626327881901651541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5016135750885254601101027 7524203626327881901651541)
        ·
          refine ⟨88174261246029866034979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 7524203626327881901651541 88174261246029866034979)
          ·
            refine ⟨132261391869044799052469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88174261246029866034979 132261391869044799052469)
            ·
              refine ⟨12399505487722949911169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132261391869044799052469 12399505487722949911169)
              ·
                rfl

theorem cell19_122249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 5].length) (baseStart_122249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122249 prefixEnd_122249 := by exact prefixLift 122249
  have htrace : WordTrace (prefixWord ++ tailWord_122249) baseStart_122249 baseEnd_122249 := by
    simpa [prefixWord, tailWord_122249, baseEnd_122249] using wordTrace_append hprefix tailTrace_122249
  have hstable : (prefixWord ++ tailWord_122249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122249).length < 2 ^ (prefixWord ++ tailWord_122249).sum := by decide
  have hdescent : baseEnd_122249 < baseStart_122249 := by decide
  rcases family_descends (prefixWord ++ tailWord_122249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122308 : List Nat := [2, 3, 3, 2, 1, 8]
def baseStart_122308 : Nat := 118140960795 + 122308 * 2 ^ 59
def prefixEnd_122308 : Nat := 4983230072969 + 3 ^ 40 * 122308 * 2
def baseEnd_122308 : Nat := 4135163252030466046915

theorem tailTrace_122308 : CollatzResearch.WordTrace tailWord_122308 prefixEnd_122308 4135163252030466046915 := by
  unfold tailWord_122308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230469620453239694243789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2973959493937652925658385 2230469620453239694243789)
  ·
    refine ⟨836426107669964885341421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2230469620453239694243789 836426107669964885341421)
    ·
      refine ⟨313659790376236832003033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 836426107669964885341421 313659790376236832003033)
      ·
        refine ⟨235244842782177624002275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313659790376236832003033 235244842782177624002275)
        ·
          refine ⟨352867264173266436003413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235244842782177624002275 352867264173266436003413)
          ·
            refine ⟨4135163252030466046915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 352867264173266436003413 4135163252030466046915)
            ·
              rfl

theorem cell19_122308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 8].length) (baseStart_122308 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122308 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122308 prefixEnd_122308 := by exact prefixLift 122308
  have htrace : WordTrace (prefixWord ++ tailWord_122308) baseStart_122308 baseEnd_122308 := by
    simpa [prefixWord, tailWord_122308, baseEnd_122308] using wordTrace_append hprefix tailTrace_122308
  have hstable : (prefixWord ++ tailWord_122308).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122308).length < 2 ^ (prefixWord ++ tailWord_122308).sum := by decide
  have hdescent : baseEnd_122308 < baseStart_122308 := by decide
  rcases family_descends (prefixWord ++ tailWord_122308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122401 : List Nat := [1, 2, 3, 2, 2, 4, 2, 3]
def baseStart_122401 : Nat := 118140960795 + 122401 * 2 ^ 59
def prefixEnd_122401 : Nat := 4983230072969 + 3 ^ 40 * 122401 * 2
def baseEnd_122401 : Nat := 37244767757677534355315

theorem tailTrace_122401 : CollatzResearch.WordTrace tailWord_122401 prefixEnd_122401 37244767757677534355315 := by
  unfold tailWord_122401
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464331229569556271623057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2976220819713037514415371 4464331229569556271623057)
  ·
    refine ⟨3348248422177167203717293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4464331229569556271623057 3348248422177167203717293)
    ·
      refine ⟨1255593158316437701393985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3348248422177167203717293 1255593158316437701393985)
      ·
        refine ⟨941694868737328276045489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1255593158316437701393985 941694868737328276045489)
        ·
          refine ⟨706271151552996207034117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941694868737328276045489 706271151552996207034117)
          ·
            refine ⟨132425840916186788818897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 706271151552996207034117 132425840916186788818897)
            ·
              refine ⟨99319380687140091614173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132425840916186788818897 99319380687140091614173)
              ·
                refine ⟨37244767757677534355315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99319380687140091614173 37244767757677534355315)
                ·
                  rfl

theorem cell19_122401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 3].length) (baseStart_122401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122401 prefixEnd_122401 := by exact prefixLift 122401
  have htrace : WordTrace (prefixWord ++ tailWord_122401) baseStart_122401 baseEnd_122401 := by
    simpa [prefixWord, tailWord_122401, baseEnd_122401] using wordTrace_append hprefix tailTrace_122401
  have hstable : (prefixWord ++ tailWord_122401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122401).length < 2 ^ (prefixWord ++ tailWord_122401).sum := by decide
  have hdescent : baseEnd_122401 < baseStart_122401 := by decide
  rcases family_descends (prefixWord ++ tailWord_122401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122403 : List Nat := [1, 1, 1, 4, 5, 1, 1, 5]
def baseStart_122403 : Nat := 118140960795 + 122403 * 2 ^ 59
def prefixEnd_122403 : Nat := 4983230072969 + 3 ^ 40 * 122403 * 2
def baseEnd_122403 : Nat := 37245376327342122310865

theorem tailTrace_122403 : CollatzResearch.WordTrace tailWord_122403 prefixEnd_122403 37245376327342122310865 := by
  unfold tailWord_122403
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464404175562310613195863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2976269450374873742130575 4464404175562310613195863)
  ·
    refine ⟨6696606263343465919793795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4464404175562310613195863 6696606263343465919793795)
    ·
      refine ⟨10044909395015198879690693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6696606263343465919793795 10044909395015198879690693)
      ·
        refine ⟨1883420511565349789942005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10044909395015198879690693 1883420511565349789942005)
        ·
          refine ⟨176570672959251542807063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1883420511565349789942005 176570672959251542807063)
          ·
            refine ⟨264856009438877314210595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176570672959251542807063 264856009438877314210595)
            ·
              refine ⟨397284014158315971315893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264856009438877314210595 397284014158315971315893)
              ·
                refine ⟨37245376327342122310865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 397284014158315971315893 37245376327342122310865)
                ·
                  rfl

theorem cell19_122403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_122403 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122403 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122403 prefixEnd_122403 := by exact prefixLift 122403
  have htrace : WordTrace (prefixWord ++ tailWord_122403) baseStart_122403 baseEnd_122403 := by
    simpa [prefixWord, tailWord_122403, baseEnd_122403] using wordTrace_append hprefix tailTrace_122403
  have hstable : (prefixWord ++ tailWord_122403).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122403).length < 2 ^ (prefixWord ++ tailWord_122403).sum := by decide
  have hdescent : baseEnd_122403 < baseStart_122403 := by decide
  rcases family_descends (prefixWord ++ tailWord_122403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122424 : List Nat := [2, 1, 2, 1, 4, 2, 7]
def baseStart_122424 : Nat := 118140960795 + 122424 * 2 ^ 59
def prefixEnd_122424 : Nat := 4983230072969 + 3 ^ 40 * 122424 * 2
def baseEnd_122424 : Nat := 12417255436273431948047

theorem tailTrace_122424 : CollatzResearch.WordTrace tailWord_122424 prefixEnd_122424 12417255436273431948047 := by
  unfold tailWord_122424
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232585054243115599855163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2976780072324154133140217 2232585054243115599855163)
  ·
    refine ⟨3348877581364673399782745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2232585054243115599855163 3348877581364673399782745)
    ·
      refine ⟨2511658186023505049837059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3348877581364673399782745 2511658186023505049837059)
      ·
        refine ⟨3767487279035257574755589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511658186023505049837059 3767487279035257574755589)
        ·
          refine ⟨706403864819110795266673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3767487279035257574755589 706403864819110795266673)
          ·
            refine ⟨529802898614333096450005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706403864819110795266673 529802898614333096450005)
            ·
              refine ⟨12417255436273431948047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 529802898614333096450005 12417255436273431948047)
              ·
                rfl

theorem cell19_122424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_122424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122424 prefixEnd_122424 := by exact prefixLift 122424
  have htrace : WordTrace (prefixWord ++ tailWord_122424) baseStart_122424 baseEnd_122424 := by
    simpa [prefixWord, tailWord_122424, baseEnd_122424] using wordTrace_append hprefix tailTrace_122424
  have hstable : (prefixWord ++ tailWord_122424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122424).length < 2 ^ (prefixWord ++ tailWord_122424).sum := by decide
  have hdescent : baseEnd_122424 < baseStart_122424 := by decide
  rcases family_descends (prefixWord ++ tailWord_122424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122460 : List Nat := [2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_122460 : Nat := 118140960795 + 122460 * 2 ^ 59
def prefixEnd_122460 : Nat := 4983230072969 + 3 ^ 40 * 122460 * 2
def baseEnd_122460 : Nat := 37262720562782879044043

theorem tailTrace_122460 : CollatzResearch.WordTrace tailWord_122460 prefixEnd_122460 37262720562782879044043 := by
  unfold tailWord_122460
  simp only [CollatzResearch.WordTrace]
  refine ⟨2233241568177904674010417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2977655424237206232013889 2233241568177904674010417)
  ·
    refine ⟨1674931176133428505507813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2233241568177904674010417 1674931176133428505507813)
    ·
      refine ⟨314049595525017844782715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1674931176133428505507813 314049595525017844782715)
      ·
        refine ⟨471074393287526767174073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314049595525017844782715 471074393287526767174073)
        ·
          refine ⟨353305794965645075380555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471074393287526767174073 353305794965645075380555)
          ·
            refine ⟨529958692448467613070833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353305794965645075380555 529958692448467613070833)
            ·
              refine ⟨397469019336350709803125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529958692448467613070833 397469019336350709803125)
              ·
                refine ⟨37262720562782879044043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 397469019336350709803125 37262720562782879044043)
                ·
                  rfl

theorem cell19_122460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_122460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122460 prefixEnd_122460 := by exact prefixLift 122460
  have htrace : WordTrace (prefixWord ++ tailWord_122460) baseStart_122460 baseEnd_122460 := by
    simpa [prefixWord, tailWord_122460, baseEnd_122460] using wordTrace_append hprefix tailTrace_122460
  have hstable : (prefixWord ++ tailWord_122460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122460).length < 2 ^ (prefixWord ++ tailWord_122460).sum := by decide
  have hdescent : baseEnd_122460 < baseStart_122460 := by decide
  rcases family_descends (prefixWord ++ tailWord_122460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122557 : List Nat := [1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_122557 : Nat := 118140960795 + 122557 * 2 ^ 59
def prefixEnd_122557 : Nat := 4983230072969 + 3 ^ 40 * 122557 * 2
def baseEnd_122557 : Nat := 37292236191515394888223

theorem tailTrace_122557 : CollatzResearch.WordTrace tailWord_122557 prefixEnd_122557 37292236191515394888223 := by
  unfold tailWord_122557
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470021017004394914301925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2980014011336263276201283 4470021017004394914301925)
  ·
    refine ⟨838128940688324046431611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4470021017004394914301925 838128940688324046431611)
    ·
      refine ⟨1257193411032486069647417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838128940688324046431611 1257193411032486069647417)
      ·
        refine ⟨942895058274364552235563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1257193411032486069647417 942895058274364552235563)
        ·
          refine ⟨1414342587411546828353345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942895058274364552235563 1414342587411546828353345)
          ·
            refine ⟨1060756940558660121265009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414342587411546828353345 1060756940558660121265009)
            ·
              refine ⟨795567705418995090948757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060756940558660121265009 795567705418995090948757)
              ·
                refine ⟨37292236191515394888223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 795567705418995090948757 37292236191515394888223)
                ·
                  rfl

theorem cell19_122557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_122557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122557 prefixEnd_122557 := by exact prefixLift 122557
  have htrace : WordTrace (prefixWord ++ tailWord_122557) baseStart_122557 baseEnd_122557 := by
    simpa [prefixWord, tailWord_122557, baseEnd_122557] using wordTrace_append hprefix tailTrace_122557
  have hstable : (prefixWord ++ tailWord_122557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122557).length < 2 ^ (prefixWord ++ tailWord_122557).sum := by decide
  have hdescent : baseEnd_122557 < baseStart_122557 := by decide
  rcases family_descends (prefixWord ++ tailWord_122557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122570 : List Nat := [3, 1, 2, 1, 6, 1, 2, 3]
def baseStart_122570 : Nat := 118140960795 + 122570 * 2 ^ 59
def prefixEnd_122570 : Nat := 4983230072969 + 3 ^ 40 * 122570 * 2
def baseEnd_122570 : Nat := 37296191894335216599299

theorem tailTrace_122570 : CollatzResearch.WordTrace tailWord_122570 prefixEnd_122570 37296191894335216599299 := by
  unfold tailWord_122570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117623791489324533631291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2980330110638198756350109 1117623791489324533631291)
  ·
    refine ⟨1676435687233986800446937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1117623791489324533631291 1676435687233986800446937)
    ·
      refine ⟨1257326765425490100335203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1676435687233986800446937 1257326765425490100335203)
      ·
        refine ⟨1885990148138235150502805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257326765425490100335203 1885990148138235150502805)
        ·
          refine ⟨88405788193979772679819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1885990148138235150502805 88405788193979772679819)
          ·
            refine ⟨132608682290969659019729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88405788193979772679819 132608682290969659019729)
            ·
              refine ⟨99456511718227244264797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132608682290969659019729 99456511718227244264797)
              ·
                refine ⟨37296191894335216599299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99456511718227244264797 37296191894335216599299)
                ·
                  rfl

theorem cell19_122570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_122570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122570 prefixEnd_122570 := by exact prefixLift 122570
  have htrace : WordTrace (prefixWord ++ tailWord_122570) baseStart_122570 baseEnd_122570 := by
    simpa [prefixWord, tailWord_122570, baseEnd_122570] using wordTrace_append hprefix tailTrace_122570
  have hstable : (prefixWord ++ tailWord_122570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122570).length < 2 ^ (prefixWord ++ tailWord_122570).sum := by decide
  have hdescent : baseEnd_122570 < baseStart_122570 := by decide
  rcases family_descends (prefixWord ++ tailWord_122570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122589 : List Nat := [1, 4, 3, 3, 2, 1, 5]
def baseStart_122589 : Nat := 118140960795 + 122589 * 2 ^ 59
def prefixEnd_122589 : Nat := 4983230072969 + 3 ^ 40 * 122589 * 2
def baseEnd_122589 : Nat := 12433991102049600725675

theorem tailTrace_122589 : CollatzResearch.WordTrace tailWord_122589 prefixEnd_122589 12433991102049600725675 := by
  unfold tailWord_122589
  simp only [CollatzResearch.WordTrace]
  refine ⟨4471188152888464379466821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2980792101925642919644547 4471188152888464379466821)
  ·
    refine ⟨838347778666587071150029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4471188152888464379466821 838347778666587071150029)
    ·
      refine ⟨314380416999970151681261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 838347778666587071150029 314380416999970151681261)
      ·
        refine ⟨117892656374988806880473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314380416999970151681261 117892656374988806880473)
        ·
          refine ⟨88419492281241605160355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117892656374988806880473 88419492281241605160355)
          ·
            refine ⟨132629238421862407740533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88419492281241605160355 132629238421862407740533)
            ·
              refine ⟨12433991102049600725675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132629238421862407740533 12433991102049600725675)
              ·
                rfl

theorem cell19_122589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 5].length) (baseStart_122589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122589 prefixEnd_122589 := by exact prefixLift 122589
  have htrace : WordTrace (prefixWord ++ tailWord_122589) baseStart_122589 baseEnd_122589 := by
    simpa [prefixWord, tailWord_122589, baseEnd_122589] using wordTrace_append hprefix tailTrace_122589
  have hstable : (prefixWord ++ tailWord_122589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122589).length < 2 ^ (prefixWord ++ tailWord_122589).sum := by decide
  have hdescent : baseEnd_122589 < baseStart_122589 := by decide
  rcases family_descends (prefixWord ++ tailWord_122589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122593 : List Nat := [1, 2, 3, 1, 5, 2, 5]
def baseStart_122593 : Nat := 118140960795 + 122593 * 2 ^ 59
def prefixEnd_122593 : Nat := 4983230072969 + 3 ^ 40 * 122593 * 2
def baseEnd_122593 : Nat := 12434396815159326029375

theorem tailTrace_122593 : CollatzResearch.WordTrace tailWord_122593 prefixEnd_122593 12434396815159326029375 := by
  unfold tailWord_122593
  simp only [CollatzResearch.WordTrace]
  refine ⟨4471334044873973062612433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2980889363249315375074955 4471334044873973062612433)
  ·
    refine ⟨3353500533655479796959325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4471334044873973062612433 3353500533655479796959325)
    ·
      refine ⟨1257562700120804923859747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3353500533655479796959325 1257562700120804923859747)
      ·
        refine ⟨1886344050181207385789621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257562700120804923859747 1886344050181207385789621)
        ·
          refine ⟨176844754704488192417777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1886344050181207385789621 176844754704488192417777)
          ·
            refine ⟨132633566028366144313333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176844754704488192417777 132633566028366144313333)
            ·
              refine ⟨12434396815159326029375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132633566028366144313333 12434396815159326029375)
              ·
                rfl

theorem cell19_122593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_122593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122593 prefixEnd_122593 := by exact prefixLift 122593
  have htrace : WordTrace (prefixWord ++ tailWord_122593) baseStart_122593 baseEnd_122593 := by
    simpa [prefixWord, tailWord_122593, baseEnd_122593] using wordTrace_append hprefix tailTrace_122593
  have hstable : (prefixWord ++ tailWord_122593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122593).length < 2 ^ (prefixWord ++ tailWord_122593).sum := by decide
  have hdescent : baseEnd_122593 < baseStart_122593 := by decide
  rcases family_descends (prefixWord ++ tailWord_122593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122686 : List Nat := [4, 2, 1, 2, 2, 2, 3, 3]
def baseStart_122686 : Nat := 118140960795 + 122686 * 2 ^ 59
def prefixEnd_122686 : Nat := 4983230072969 + 3 ^ 40 * 122686 * 2
def baseEnd_122686 : Nat := 37331488934881318021205

theorem tailTrace_122686 : CollatzResearch.WordTrace tailWord_122686 prefixEnd_122686 37331488934881318021205 := by
  unfold tailWord_122686
  simp only [CollatzResearch.WordTrace]
  refine ⟨559340754192131243218489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2983150689024699963831941 559340754192131243218489)
  ·
    refine ⟨419505565644098432413867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 559340754192131243218489 419505565644098432413867)
    ·
      refine ⟨629258348466147648620801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419505565644098432413867 629258348466147648620801)
      ·
        refine ⟨471943761349610736465601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629258348466147648620801 471943761349610736465601)
        ·
          refine ⟨353957821012208052349201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471943761349610736465601 353957821012208052349201)
          ·
            refine ⟨265468365759156039261901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353957821012208052349201 265468365759156039261901)
            ·
              refine ⟨99550637159683514723213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265468365759156039261901 99550637159683514723213)
              ·
                refine ⟨37331488934881318021205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99550637159683514723213 37331488934881318021205)
                ·
                  rfl

theorem cell19_122686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_122686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122686 prefixEnd_122686 := by exact prefixLift 122686
  have htrace : WordTrace (prefixWord ++ tailWord_122686) baseStart_122686 baseEnd_122686 := by
    simpa [prefixWord, tailWord_122686, baseEnd_122686] using wordTrace_append hprefix tailTrace_122686
  have hstable : (prefixWord ++ tailWord_122686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122686).length < 2 ^ (prefixWord ++ tailWord_122686).sum := by decide
  have hdescent : baseEnd_122686 < baseStart_122686 := by decide
  rcases family_descends (prefixWord ++ tailWord_122686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122709 : List Nat := [1, 3, 2, 2, 2, 3, 6]
def baseStart_122709 : Nat := 118140960795 + 122709 * 2 ^ 59
def prefixEnd_122709 : Nat := 4983230072969 + 3 ^ 40 * 122709 * 2
def baseEnd_122709 : Nat := 12446162495341359836677

theorem tailTrace_122709 : CollatzResearch.WordTrace tailWord_122709 prefixEnd_122709 12446162495341359836677 := by
  unfold tailWord_122709
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475564912453724873835181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2983709941635816582556787 4475564912453724873835181)
  ·
    refine ⟨1678336842170146827688193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4475564912453724873835181 1678336842170146827688193)
    ·
      refine ⟨1258752631627610120766145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1678336842170146827688193 1258752631627610120766145)
      ·
        refine ⟨944064473720707590574609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1258752631627610120766145 944064473720707590574609)
        ·
          refine ⟨708048355290530692930957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944064473720707590574609 708048355290530692930957)
          ·
            refine ⟨265518133233949009849109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708048355290530692930957 265518133233949009849109)
            ·
              refine ⟨12446162495341359836677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 265518133233949009849109 12446162495341359836677)
              ·
                rfl

theorem cell19_122709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_122709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122709 prefixEnd_122709 := by exact prefixLift 122709
  have htrace : WordTrace (prefixWord ++ tailWord_122709) baseStart_122709 baseEnd_122709 := by
    simpa [prefixWord, tailWord_122709, baseEnd_122709] using wordTrace_append hprefix tailTrace_122709
  have hstable : (prefixWord ++ tailWord_122709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122709).length < 2 ^ (prefixWord ++ tailWord_122709).sum := by decide
  have hdescent : baseEnd_122709 < baseStart_122709 := by decide
  rcases family_descends (prefixWord ++ tailWord_122709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122728 : List Nat := [2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_122728 : Nat := 118140960795 + 122728 * 2 ^ 59
def prefixEnd_122728 : Nat := 4983230072969 + 3 ^ 40 * 122728 * 2
def baseEnd_122728 : Nat := 37344268897837665087757

theorem tailTrace_122728 : CollatzResearch.WordTrace tailWord_122728 prefixEnd_122728 37344268897837665087757 := by
  unfold tailWord_122728
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238128949692445559388419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2984171932923260745851225 2238128949692445559388419)
  ·
    refine ⟨3357193424538668339082629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2238128949692445559388419 3357193424538668339082629)
    ·
      refine ⟨629473767101000313577993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3357193424538668339082629 629473767101000313577993)
      ·
        refine ⟨472105325325750235183495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629473767101000313577993 472105325325750235183495)
        ·
          refine ⟨708157987988625352775243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472105325325750235183495 708157987988625352775243)
          ·
            refine ⟨1062236981982938029162865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708157987988625352775243 1062236981982938029162865)
            ·
              refine ⟨796677736487203521872149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062236981982938029162865 796677736487203521872149)
              ·
                refine ⟨37344268897837665087757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 796677736487203521872149 37344268897837665087757)
                ·
                  rfl

theorem cell19_122728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_122728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122728 prefixEnd_122728 := by exact prefixLift 122728
  have htrace : WordTrace (prefixWord ++ tailWord_122728) baseStart_122728 baseEnd_122728 := by
    simpa [prefixWord, tailWord_122728, baseEnd_122728] using wordTrace_append hprefix tailTrace_122728
  have hstable : (prefixWord ++ tailWord_122728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122728).length < 2 ^ (prefixWord ++ tailWord_122728).sum := by decide
  have hdescent : baseEnd_122728 < baseStart_122728 := by decide
  rcases family_descends (prefixWord ++ tailWord_122728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122762 : List Nat := [3, 1, 2, 4, 3, 1, 5]
def baseStart_122762 : Nat := 118140960795 + 122762 * 2 ^ 59
def prefixEnd_122762 : Nat := 4983230072969 + 3 ^ 40 * 122762 * 2
def baseEnd_122762 : Nat := 12451538194045220110703

theorem tailTrace_122762 : CollatzResearch.WordTrace tailWord_122762 prefixEnd_122762 12451538194045220110703 := by
  unfold tailWord_122762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119374495315428731378635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2984998654174476617009693 1119374495315428731378635)
  ·
    refine ⟨1679061742973143097067953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1119374495315428731378635 1679061742973143097067953)
    ·
      refine ⟨1259296307229857322800965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1679061742973143097067953 1259296307229857322800965)
      ·
        refine ⟨236118057605598248025181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1259296307229857322800965 236118057605598248025181)
        ·
          refine ⟨88544271602099343009443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236118057605598248025181 88544271602099343009443)
          ·
            refine ⟨132816407403149014514165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88544271602099343009443 132816407403149014514165)
            ·
              refine ⟨12451538194045220110703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132816407403149014514165 12451538194045220110703)
              ·
                rfl

theorem cell19_122762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 5].length) (baseStart_122762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122762 prefixEnd_122762 := by exact prefixLift 122762
  have htrace : WordTrace (prefixWord ++ tailWord_122762) baseStart_122762 baseEnd_122762 := by
    simpa [prefixWord, tailWord_122762, baseEnd_122762] using wordTrace_append hprefix tailTrace_122762
  have hstable : (prefixWord ++ tailWord_122762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122762).length < 2 ^ (prefixWord ++ tailWord_122762).sum := by decide
  have hdescent : baseEnd_122762 < baseStart_122762 := by decide
  rcases family_descends (prefixWord ++ tailWord_122762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122783 : List Nat := [1, 1, 2, 5, 3, 1, 2, 4]
def baseStart_122783 : Nat := 118140960795 + 122783 * 2 ^ 59
def prefixEnd_122783 : Nat := 4983230072969 + 3 ^ 40 * 122783 * 2
def baseEnd_122783 : Nat := 37361004563613833865385

theorem tailTrace_122783 : CollatzResearch.WordTrace tailWord_122783 prefixEnd_122783 37361004563613833865385 := by
  unfold tailWord_122783
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478263914185635512029003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2985509276123757008019335 4478263914185635512029003)
  ·
    refine ⟨6717395871278453268043505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4478263914185635512029003 6717395871278453268043505)
    ·
      refine ⟨5038046903458839951032629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6717395871278453268043505 5038046903458839951032629)
      ·
        refine ⟨472316897199266245409309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5038046903458839951032629 472316897199266245409309)
        ·
          refine ⟨177118836449724842028491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472316897199266245409309 177118836449724842028491)
          ·
            refine ⟨265678254674587263042737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177118836449724842028491 265678254674587263042737)
            ·
              refine ⟨199258691005940447282053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265678254674587263042737 199258691005940447282053)
              ·
                refine ⟨37361004563613833865385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199258691005940447282053 37361004563613833865385)
                ·
                  rfl

theorem cell19_122783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_122783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122783 prefixEnd_122783 := by exact prefixLift 122783
  have htrace : WordTrace (prefixWord ++ tailWord_122783) baseStart_122783 baseEnd_122783 := by
    simpa [prefixWord, tailWord_122783, baseEnd_122783] using wordTrace_append hprefix tailTrace_122783
  have hstable : (prefixWord ++ tailWord_122783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122783).length < 2 ^ (prefixWord ++ tailWord_122783).sum := by decide
  have hdescent : baseEnd_122783 < baseStart_122783 := by decide
  rcases family_descends (prefixWord ++ tailWord_122783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122878 : List Nat := [4, 2, 2, 2, 1, 2, 6]
def baseStart_122878 : Nat := 118140960795 + 122878 * 2 ^ 59
def prefixEnd_122878 : Nat := 4983230072969 + 3 ^ 40 * 122878 * 2
def baseEnd_122878 : Nat := 12463303874227253918005

theorem tailTrace_122878 : CollatzResearch.WordTrace tailWord_122878 prefixEnd_122878 12463303874227253918005 := by
  unfold tailWord_122878
  simp only [CollatzResearch.WordTrace]
  refine ⟨560216106105183342092161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2987819232560977824491525 560216106105183342092161)
  ·
    refine ⟨420162079578887506569121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 560216106105183342092161 420162079578887506569121)
    ·
      refine ⟨315121559684165629926841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420162079578887506569121 315121559684165629926841)
      ·
        refine ⟨236341169763124222445131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315121559684165629926841 236341169763124222445131)
        ·
          refine ⟨354511754644686333667697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236341169763124222445131 354511754644686333667697)
          ·
            refine ⟨265883815983514750250773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354511754644686333667697 265883815983514750250773)
            ·
              refine ⟨12463303874227253918005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 265883815983514750250773 12463303874227253918005)
              ·
                rfl

theorem cell19_122878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_122878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122878 prefixEnd_122878 := by exact prefixLift 122878
  have htrace : WordTrace (prefixWord ++ tailWord_122878) baseStart_122878 baseEnd_122878 := by
    simpa [prefixWord, tailWord_122878, baseEnd_122878] using wordTrace_append hprefix tailTrace_122878
  have hstable : (prefixWord ++ tailWord_122878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122878).length < 2 ^ (prefixWord ++ tailWord_122878).sum := by decide
  have hdescent : baseEnd_122878 < baseStart_122878 := by decide
  rcases family_descends (prefixWord ++ tailWord_122878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122916 : List Nat := [2, 3, 1, 4, 2, 1, 1, 5]
def baseStart_122916 : Nat := 118140960795 + 122916 * 2 ^ 59
def prefixEnd_122916 : Nat := 4983230072969 + 3 ^ 40 * 122916 * 2
def baseEnd_122916 : Nat := 37401474446308932909467

theorem tailTrace_122916 : CollatzResearch.WordTrace tailWord_122916 prefixEnd_122916 37401474446308932909467 := by
  unfold tailWord_122916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2241557411351899613310301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2988743215135866151080401 2241557411351899613310301)
  ·
    refine ⟨840584029256962354991363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2241557411351899613310301 840584029256962354991363)
    ·
      refine ⟨1260876043885443532487045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840584029256962354991363 1260876043885443532487045)
      ·
        refine ⟨236414258228520662341321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1260876043885443532487045 236414258228520662341321)
        ·
          refine ⟨177310693671390496755991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236414258228520662341321 177310693671390496755991)
          ·
            refine ⟨265966040507085745133987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177310693671390496755991 265966040507085745133987)
            ·
              refine ⟨398949060760628617700981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265966040507085745133987 398949060760628617700981)
              ·
                refine ⟨37401474446308932909467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398949060760628617700981 37401474446308932909467)
                ·
                  rfl

theorem cell19_122916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_122916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122916 prefixEnd_122916 := by exact prefixLift 122916
  have htrace : WordTrace (prefixWord ++ tailWord_122916) baseStart_122916 baseEnd_122916 := by
    simpa [prefixWord, tailWord_122916, baseEnd_122916] using wordTrace_append hprefix tailTrace_122916
  have hstable : (prefixWord ++ tailWord_122916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122916).length < 2 ^ (prefixWord ++ tailWord_122916).sum := by decide
  have hdescent : baseEnd_122916 < baseStart_122916 := by decide
  rcases family_descends (prefixWord ++ tailWord_122916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122973 : List Nat := [1, 4, 4, 1, 1, 1, 2, 5]
def baseStart_122973 : Nat := 118140960795 + 122973 * 2 ^ 59
def prefixEnd_122973 : Nat := 4983230072969 + 3 ^ 40 * 122973 * 2
def baseEnd_122973 : Nat := 37418818681749689642645

theorem tailTrace_122973 : CollatzResearch.WordTrace tailWord_122973 prefixEnd_122973 37418818681749689642645 := by
  unfold tailWord_122973
  simp only [CollatzResearch.WordTrace]
  refine ⟨4485193783497297961445573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2990129188998198640963715 4485193783497297961445573)
  ·
    refine ⟨840973834405743367771045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4485193783497297961445573 840973834405743367771045)
    ·
      refine ⟨157682593951076881457071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 840973834405743367771045 157682593951076881457071)
      ·
        refine ⟨236523890926615322185607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157682593951076881457071 236523890926615322185607)
        ·
          refine ⟨354785836389922983278411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236523890926615322185607 354785836389922983278411)
          ·
            refine ⟨532178754584884474917617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354785836389922983278411 532178754584884474917617)
            ·
              refine ⟨399134065938663356188213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532178754584884474917617 399134065938663356188213)
              ·
                refine ⟨37418818681749689642645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399134065938663356188213 37418818681749689642645)
                ·
                  rfl

theorem cell19_122973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_122973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_122973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_122973 prefixEnd_122973 := by exact prefixLift 122973
  have htrace : WordTrace (prefixWord ++ tailWord_122973) baseStart_122973 baseEnd_122973 := by
    simpa [prefixWord, tailWord_122973, baseEnd_122973] using wordTrace_append hprefix tailTrace_122973
  have hstable : (prefixWord ++ tailWord_122973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122973).length < 2 ^ (prefixWord ++ tailWord_122973).sum := by decide
  have hdescent : baseEnd_122973 < baseStart_122973 := by decide
  rcases family_descends (prefixWord ++ tailWord_122973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123009 : List Nat := [1, 2, 4, 2, 4, 1, 1, 4]
def baseStart_123009 : Nat := 118140960795 + 123009 * 2 ^ 59
def prefixEnd_123009 : Nat := 4983230072969 + 3 ^ 40 * 123009 * 2
def baseEnd_123009 : Nat := 37429772935712272842547

theorem tailTrace_123009 : CollatzResearch.WordTrace tailWord_123009 prefixEnd_123009 37429772935712272842547 := by
  unfold tailWord_123009
  simp only [CollatzResearch.WordTrace]
  refine ⟨4486506811366876109756081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2991004540911250739837387 4486506811366876109756081)
  ·
    refine ⟨3364880108525157082317061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4486506811366876109756081 3364880108525157082317061)
    ·
      refine ⟨630915020348466952934449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3364880108525157082317061 630915020348466952934449)
      ·
        refine ⟨473186265261350214700837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630915020348466952934449 473186265261350214700837)
        ·
          refine ⟨88722424736503165256407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 473186265261350214700837 88722424736503165256407)
          ·
            refine ⟨133083637104754747884611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88722424736503165256407 133083637104754747884611)
            ·
              refine ⟨199625455657132121826917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133083637104754747884611 199625455657132121826917)
              ·
                refine ⟨37429772935712272842547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199625455657132121826917 37429772935712272842547)
                ·
                  rfl

theorem cell19_123009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 4].length) (baseStart_123009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123009 prefixEnd_123009 := by exact prefixLift 123009
  have htrace : WordTrace (prefixWord ++ tailWord_123009) baseStart_123009 baseEnd_123009 := by
    simpa [prefixWord, tailWord_123009, baseEnd_123009] using wordTrace_append hprefix tailTrace_123009
  have hstable : (prefixWord ++ tailWord_123009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123009).length < 2 ^ (prefixWord ++ tailWord_123009).sum := by decide
  have hdescent : baseEnd_123009 < baseStart_123009 := by decide
  rcases family_descends (prefixWord ++ tailWord_123009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123013 : List Nat := [1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_123013 : Nat := 118140960795 + 123013 * 2 ^ 59
def prefixEnd_123013 : Nat := 4983230072969 + 3 ^ 40 * 123013 * 2
def baseEnd_123013 : Nat := 37430990075041448753647

theorem tailTrace_123013 : CollatzResearch.WordTrace tailWord_123013 prefixEnd_123013 37430990075041448753647 := by
  unfold tailWord_123013
  simp only [CollatzResearch.WordTrace]
  refine ⟨4486652703352384792901693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2991101802234923195267795 4486652703352384792901693)
  ·
    refine ⟨1682494763757144297338135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4486652703352384792901693 1682494763757144297338135)
    ·
      refine ⟨2523742145635716446007203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1682494763757144297338135 2523742145635716446007203)
      ·
        refine ⟨3785613218453574669010805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523742145635716446007203 3785613218453574669010805)
        ·
          refine ⟨354901239230022625219763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3785613218453574669010805 354901239230022625219763)
          ·
            refine ⟨532351858845033937829645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354901239230022625219763 532351858845033937829645)
            ·
              refine ⟨199631947066887726686117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532351858845033937829645 199631947066887726686117)
              ·
                refine ⟨37430990075041448753647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199631947066887726686117 37430990075041448753647)
                ·
                  rfl

theorem cell19_123013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_123013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123013 prefixEnd_123013 := by exact prefixLift 123013
  have htrace : WordTrace (prefixWord ++ tailWord_123013) baseStart_123013 baseEnd_123013 := by
    simpa [prefixWord, tailWord_123013, baseEnd_123013] using wordTrace_append hprefix tailTrace_123013
  have hstable : (prefixWord ++ tailWord_123013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123013).length < 2 ^ (prefixWord ++ tailWord_123013).sum := by decide
  have hdescent : baseEnd_123013 < baseStart_123013 := by decide
  rcases family_descends (prefixWord ++ tailWord_123013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123089 : List Nat := [1, 2, 2, 1, 2, 2, 6, 3]
def baseStart_123089 : Nat := 118140960795 + 123089 * 2 ^ 59
def prefixEnd_123089 : Nat := 4983230072969 + 3 ^ 40 * 123089 * 2
def baseEnd_123089 : Nat := 37454115722295791064551

theorem tailTrace_123089 : CollatzResearch.WordTrace tailWord_123089 prefixEnd_123089 37454115722295791064551 := by
  unfold tailWord_123089
  simp only [CollatzResearch.WordTrace]
  refine ⟨4489424651077049772668321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2992949767384699848445547 4489424651077049772668321)
  ·
    refine ⟨3367068488307787329501241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4489424651077049772668321 3367068488307787329501241)
    ·
      refine ⟨2525301366230840497125931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3367068488307787329501241 2525301366230840497125931)
      ·
        refine ⟨3787952049346260745688897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525301366230840497125931 3787952049346260745688897)
        ·
          refine ⟨2840964037009695559266673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787952049346260745688897 2840964037009695559266673)
          ·
            refine ⟨2130723027757271669450005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840964037009695559266673 2130723027757271669450005)
            ·
              refine ⟨99877641926122109505469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2130723027757271669450005 99877641926122109505469)
              ·
                refine ⟨37454115722295791064551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99877641926122109505469 37454115722295791064551)
                ·
                  rfl

theorem cell19_123089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 3].length) (baseStart_123089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123089 prefixEnd_123089 := by exact prefixLift 123089
  have htrace : WordTrace (prefixWord ++ tailWord_123089) baseStart_123089 baseEnd_123089 := by
    simpa [prefixWord, tailWord_123089, baseEnd_123089] using wordTrace_append hprefix tailTrace_123089
  have hstable : (prefixWord ++ tailWord_123089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123089).length < 2 ^ (prefixWord ++ tailWord_123089).sum := by decide
  have hdescent : baseEnd_123089 < baseStart_123089 := by decide
  rcases family_descends (prefixWord ++ tailWord_123089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123148 : List Nat := [2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_123148 : Nat := 118140960795 + 123148 * 2 ^ 59
def prefixEnd_123148 : Nat := 4983230072969 + 3 ^ 40 * 123148 * 2
def baseEnd_123148 : Nat := 37472068527401135753279

theorem tailTrace_123148 : CollatzResearch.WordTrace tailWord_123148 prefixEnd_123148 37472068527401135753279 := by
  unfold tailWord_123148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245788278931651424533049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2994384371908868566044065 2245788278931651424533049)
  ·
    refine ⟨1684341209198738568399787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2245788278931651424533049 1684341209198738568399787)
    ·
      refine ⟨2526511813798107852599681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1684341209198738568399787 2526511813798107852599681)
      ·
        refine ⟨1894883860348580889449761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2526511813798107852599681 1894883860348580889449761)
        ·
          refine ⟨1421162895261435667087321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1894883860348580889449761 1421162895261435667087321)
          ·
            refine ⟨1065872171446076750315491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421162895261435667087321 1065872171446076750315491)
            ·
              refine ⟨1598808257169115125473237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065872171446076750315491 1598808257169115125473237)
              ·
                refine ⟨37472068527401135753279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1598808257169115125473237 37472068527401135753279)
                ·
                  rfl

theorem cell19_123148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_123148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123148 prefixEnd_123148 := by exact prefixLift 123148
  have htrace : WordTrace (prefixWord ++ tailWord_123148) baseStart_123148 baseEnd_123148 := by
    simpa [prefixWord, tailWord_123148, baseEnd_123148] using wordTrace_append hprefix tailTrace_123148
  have hstable : (prefixWord ++ tailWord_123148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123148).length < 2 ^ (prefixWord ++ tailWord_123148).sum := by decide
  have hdescent : baseEnd_123148 < baseStart_123148 := by decide
  rcases family_descends (prefixWord ++ tailWord_123148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123165 : List Nat := [1, 4, 2, 3, 2, 7]
def baseStart_123165 : Nat := 118140960795 + 123165 * 2 ^ 59
def prefixEnd_123165 : Nat := 4983230072969 + 3 ^ 40 * 123165 * 2
def baseEnd_123165 : Nat := 4164137929950014819495

theorem tailTrace_123165 : CollatzResearch.WordTrace tailWord_123165 prefixEnd_123165 4164137929950014819495 := by
  unfold tailWord_123165
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492196598801714752434949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2994797732534476501623299 4492196598801714752434949)
  ·
    refine ⟨842286862275321516081553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4492196598801714752434949 842286862275321516081553)
    ·
      refine ⟨631715146706491137061165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 842286862275321516081553 631715146706491137061165)
      ·
        refine ⟨236893180014934176397937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631715146706491137061165 236893180014934176397937)
        ·
          refine ⟨177669885011200632298453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236893180014934176397937 177669885011200632298453)
          ·
            refine ⟨4164137929950014819495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 177669885011200632298453 4164137929950014819495)
            ·
              rfl

theorem cell19_123165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 7].length) (baseStart_123165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123165 prefixEnd_123165 := by exact prefixLift 123165
  have htrace : WordTrace (prefixWord ++ tailWord_123165) baseStart_123165 baseEnd_123165 := by
    simpa [prefixWord, tailWord_123165, baseEnd_123165] using wordTrace_append hprefix tailTrace_123165
  have hstable : (prefixWord ++ tailWord_123165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123165).length < 2 ^ (prefixWord ++ tailWord_123165).sum := by decide
  have hdescent : baseEnd_123165 < baseStart_123165 := by decide
  rcases family_descends (prefixWord ++ tailWord_123165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123167 : List Nat := [1, 1, 2, 4, 3, 8]
def baseStart_123167 : Nat := 118140960795 + 123167 * 2 ^ 59
def prefixEnd_123167 : Nat := 4983230072969 + 3 ^ 40 * 123167 * 2
def baseEnd_123167 : Nat := 4164205548801635703445

theorem tailTrace_123167 : CollatzResearch.WordTrace tailWord_123167 prefixEnd_123167 4164205548801635703445 := by
  unfold tailWord_123167
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492269544794469094007755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2994846363196312729338503 4492269544794469094007755)
  ·
    refine ⟨6738404317191703641011633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4492269544794469094007755 6738404317191703641011633)
    ·
      refine ⟨5053803237893777730758725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6738404317191703641011633 5053803237893777730758725)
      ·
        refine ⟨947588107105083324517261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5053803237893777730758725 947588107105083324517261)
        ·
          refine ⟨355345540164406246693973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 947588107105083324517261 355345540164406246693973)
          ·
            refine ⟨4164205548801635703445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 355345540164406246693973 4164205548801635703445)
            ·
              rfl

theorem cell19_123167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 8].length) (baseStart_123167 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123167 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123167 prefixEnd_123167 := by exact prefixLift 123167
  have htrace : WordTrace (prefixWord ++ tailWord_123167) baseStart_123167 baseEnd_123167 := by
    simpa [prefixWord, tailWord_123167, baseEnd_123167] using wordTrace_append hprefix tailTrace_123167
  have hstable : (prefixWord ++ tailWord_123167).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123167).length < 2 ^ (prefixWord ++ tailWord_123167).sum := by decide
  have hdescent : baseEnd_123167 < baseStart_123167 := by decide
  rcases family_descends (prefixWord ++ tailWord_123167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123254 : List Nat := [5, 1, 1, 4, 1, 2, 2, 3]
def baseStart_123254 : Nat := 118140960795 + 123254 * 2 ^ 59
def prefixEnd_123254 : Nat := 4983230072969 + 3 ^ 40 * 123254 * 2
def baseEnd_123254 : Nat := 37504322719624297397435

theorem tailTrace_123254 : CollatzResearch.WordTrace tailWord_123254 prefixEnd_123254 37504322719624297397435 := by
  unfold tailWord_123254
  simp only [CollatzResearch.WordTrace]
  refine ⟨280965168467455184526551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2996961796986188634949877 280965168467455184526551)
  ·
    refine ⟨421447752701182776789827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280965168467455184526551 421447752701182776789827)
    ·
      refine ⟨632171629051774165184741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421447752701182776789827 632171629051774165184741)
      ·
        refine ⟨118532180447207655972139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 632171629051774165184741 118532180447207655972139)
        ·
          refine ⟨177798270670811483958209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118532180447207655972139 177798270670811483958209)
          ·
            refine ⟨133348703003108612968657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177798270670811483958209 133348703003108612968657)
            ·
              refine ⟨100011527252331459726493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133348703003108612968657 100011527252331459726493)
              ·
                refine ⟨37504322719624297397435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100011527252331459726493 37504322719624297397435)
                ·
                  rfl

theorem cell19_123254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_123254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123254 prefixEnd_123254 := by exact prefixLift 123254
  have htrace : WordTrace (prefixWord ++ tailWord_123254) baseStart_123254 baseEnd_123254 := by
    simpa [prefixWord, tailWord_123254, baseEnd_123254] using wordTrace_append hprefix tailTrace_123254
  have hstable : (prefixWord ++ tailWord_123254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123254).length < 2 ^ (prefixWord ++ tailWord_123254).sum := by decide
  have hdescent : baseEnd_123254 < baseStart_123254 := by decide
  rcases family_descends (prefixWord ++ tailWord_123254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123298 : List Nat := [3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_123298 : Nat := 118140960795 + 123298 * 2 ^ 59
def prefixEnd_123298 : Nat := 4983230072969 + 3 ^ 40 * 123298 * 2
def baseEnd_123298 : Nat := 37517711252245232419537

theorem tailTrace_123298 : CollatzResearch.WordTrace tailWord_123298 prefixEnd_123298 37517711252245232419537 := by
  unfold tailWord_123298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124261876829969616756637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2998031671546585644684365 1124261876829969616756637)
  ·
    refine ⟨421598203811238606283739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1124261876829969616756637 421598203811238606283739)
    ·
      refine ⟨632397305716857909425609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421598203811238606283739 632397305716857909425609)
      ·
        refine ⟨474297979287643432069207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632397305716857909425609 474297979287643432069207)
        ·
          refine ⟨711446968931465148103811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474297979287643432069207 711446968931465148103811)
          ·
            refine ⟨1067170453397197722155717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711446968931465148103811 1067170453397197722155717)
            ·
              refine ⟨200094460011974572904197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1067170453397197722155717 200094460011974572904197)
              ·
                refine ⟨37517711252245232419537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200094460011974572904197 37517711252245232419537)
                ·
                  rfl

theorem cell19_123298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_123298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123298 prefixEnd_123298 := by exact prefixLift 123298
  have htrace : WordTrace (prefixWord ++ tailWord_123298) baseStart_123298 baseEnd_123298 := by
    simpa [prefixWord, tailWord_123298, baseEnd_123298] using wordTrace_append hprefix tailTrace_123298
  have hstable : (prefixWord ++ tailWord_123298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123298).length < 2 ^ (prefixWord ++ tailWord_123298).sum := by decide
  have hdescent : baseEnd_123298 < baseStart_123298 := by decide
  rcases family_descends (prefixWord ++ tailWord_123298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123300 : List Nat := [2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_123300 : Nat := 118140960795 + 123300 * 2 ^ 59
def prefixEnd_123300 : Nat := 4983230072969 + 3 ^ 40 * 123300 * 2
def baseEnd_123300 : Nat := 37518319821909820375087

theorem tailTrace_123300 : CollatzResearch.WordTrace tailWord_123300 prefixEnd_123300 37518319821909820375087 := by
  unfold tailWord_123300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248560226656316404299677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2998080302208421872399569 2248560226656316404299677)
  ·
    refine ⟨843210084996118651612379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2248560226656316404299677 843210084996118651612379)
    ·
      refine ⟨1264815127494177977418569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843210084996118651612379 1264815127494177977418569)
      ·
        refine ⟨948611345620633483063927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1264815127494177977418569 948611345620633483063927)
        ·
          refine ⟨1422917018430950224595891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948611345620633483063927 1422917018430950224595891)
          ·
            refine ⟨2134375527646425336893837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422917018430950224595891 2134375527646425336893837)
            ·
              refine ⟨800390822867409501335189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2134375527646425336893837 800390822867409501335189)
              ·
                refine ⟨37518319821909820375087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 800390822867409501335189 37518319821909820375087)
                ·
                  rfl

theorem cell19_123300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_123300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123300 prefixEnd_123300 := by exact prefixLift 123300
  have htrace : WordTrace (prefixWord ++ tailWord_123300) baseStart_123300 baseEnd_123300 := by
    simpa [prefixWord, tailWord_123300, baseEnd_123300] using wordTrace_append hprefix tailTrace_123300
  have hstable : (prefixWord ++ tailWord_123300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123300).length < 2 ^ (prefixWord ++ tailWord_123300).sum := by decide
  have hdescent : baseEnd_123300 < baseStart_123300 := by decide
  rcases family_descends (prefixWord ++ tailWord_123300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123319 : List Nat := [1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_123319 : Nat := 118140960795 + 123319 * 2 ^ 59
def prefixEnd_123319 : Nat := 4983230072969 + 3 ^ 40 * 123319 * 2
def baseEnd_123319 : Nat := 37524101233723405952813

theorem tailTrace_123319 : CollatzResearch.WordTrace tailWord_123319 prefixEnd_123319 37524101233723405952813 := by
  unfold tailWord_123319
  simp only [CollatzResearch.WordTrace]
  refine ⟨4497813440243799053541011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2998542293495866035694007 4497813440243799053541011)
  ·
    refine ⟨6746720160365698580311517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4497813440243799053541011 6746720160365698580311517)
    ·
      refine ⟨2530020060137136967616819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6746720160365698580311517 2530020060137136967616819)
      ·
        refine ⟨3795030090205705451425229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2530020060137136967616819 3795030090205705451425229)
        ·
          refine ⟨1423136283827139544284461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3795030090205705451425229 1423136283827139544284461)
          ·
            refine ⟨533676106435177329106673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1423136283827139544284461 533676106435177329106673)
            ·
              refine ⟨400257079826382996830005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533676106435177329106673 400257079826382996830005)
              ·
                refine ⟨37524101233723405952813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 400257079826382996830005 37524101233723405952813)
                ·
                  rfl

theorem cell19_123319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_123319 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123319 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123319 prefixEnd_123319 := by exact prefixLift 123319
  have htrace : WordTrace (prefixWord ++ tailWord_123319) baseStart_123319 baseEnd_123319 := by
    simpa [prefixWord, tailWord_123319, baseEnd_123319] using wordTrace_append hprefix tailTrace_123319
  have hstable : (prefixWord ++ tailWord_123319).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123319).length < 2 ^ (prefixWord ++ tailWord_123319).sum := by decide
  have hdescent : baseEnd_123319 < baseStart_123319 := by decide
  rcases family_descends (prefixWord ++ tailWord_123319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123452 : List Nat := [2, 2, 2, 2, 3, 1, 7]
def baseStart_123452 : Nat := 118140960795 + 123452 * 2 ^ 59
def prefixEnd_123452 : Nat := 4983230072969 + 3 ^ 40 * 123452 * 2
def baseEnd_123452 : Nat := 12521523705472834998965

theorem tailTrace_123452 : CollatzResearch.WordTrace tailWord_123452 prefixEnd_123452 12521523705472834998965 := by
  unfold tailWord_123452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251332174380981384066305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3001776232507975178755073 2251332174380981384066305)
  ·
    refine ⟨1688499130785736038049729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2251332174380981384066305 1688499130785736038049729)
    ·
      refine ⟨1266374348089302028537297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1688499130785736038049729 1266374348089302028537297)
      ·
        refine ⟨949780761066976521402973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1266374348089302028537297 949780761066976521402973)
        ·
          refine ⟨356167785400116195526115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 949780761066976521402973 356167785400116195526115)
          ·
            refine ⟨534251678100174293289173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356167785400116195526115 534251678100174293289173)
            ·
              refine ⟨12521523705472834998965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 534251678100174293289173 12521523705472834998965)
              ·
                rfl

theorem cell19_123452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_123452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123452 prefixEnd_123452 := by exact prefixLift 123452
  have htrace : WordTrace (prefixWord ++ tailWord_123452) baseStart_123452 baseEnd_123452 := by
    simpa [prefixWord, tailWord_123452, baseEnd_123452] using wordTrace_append hprefix tailTrace_123452
  have hstable : (prefixWord ++ tailWord_123452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123452).length < 2 ^ (prefixWord ++ tailWord_123452).sum := by decide
  have hdescent : baseEnd_123452 < baseStart_123452 := by decide
  rcases family_descends (prefixWord ++ tailWord_123452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123469 : List Nat := [1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_123469 : Nat := 118140960795 + 123469 * 2 ^ 59
def prefixEnd_123469 : Nat := 4983230072969 + 3 ^ 40 * 123469 * 2
def baseEnd_123469 : Nat := 37569743958567502619071

theorem tailTrace_123469 : CollatzResearch.WordTrace tailWord_123469 prefixEnd_123469 37569743958567502619071 := by
  unfold tailWord_123469
  simp only [CollatzResearch.WordTrace]
  refine ⟨4503284389700374671501461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3002189593133583114334307 4503284389700374671501461)
  ·
    refine ⟨211091455767205062726631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4503284389700374671501461 211091455767205062726631)
    ·
      refine ⟨316637183650807594089947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211091455767205062726631 316637183650807594089947)
      ·
        refine ⟨474955775476211391134921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316637183650807594089947 474955775476211391134921)
        ·
          refine ⟨356216831607158543351191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474955775476211391134921 356216831607158543351191)
          ·
            refine ⟨534325247410737815026787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356216831607158543351191 534325247410737815026787)
            ·
              refine ⟨801487871116106722540181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534325247410737815026787 801487871116106722540181)
              ·
                refine ⟨37569743958567502619071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 801487871116106722540181 37569743958567502619071)
                ·
                  rfl

theorem cell19_123469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_123469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123469 prefixEnd_123469 := by exact prefixLift 123469
  have htrace : WordTrace (prefixWord ++ tailWord_123469) baseStart_123469 baseEnd_123469 := by
    simpa [prefixWord, tailWord_123469, baseEnd_123469] using wordTrace_append hprefix tailTrace_123469
  have hstable : (prefixWord ++ tailWord_123469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123469).length < 2 ^ (prefixWord ++ tailWord_123469).sum := by decide
  have hdescent : baseEnd_123469 < baseStart_123469 := by decide
  rcases family_descends (prefixWord ++ tailWord_123469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123509 : List Nat := [1, 3, 4, 2, 9]
def baseStart_123509 : Nat := 118140960795 + 123509 * 2 ^ 59
def prefixEnd_123509 : Nat := 4983230072969 + 3 ^ 40 * 123509 * 2
def baseEnd_123509 : Nat := 1391922790809602286299

theorem tailTrace_123509 : CollatzResearch.WordTrace tailWord_123509 prefixEnd_123509 1391922790809602286299 := by
  unfold tailWord_123509
  simp only [CollatzResearch.WordTrace]
  refine ⟨4504743309555461502957581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3003162206370307668638387 4504743309555461502957581)
  ·
    refine ⟨1689278741083298063609093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4504743309555461502957581 1689278741083298063609093)
    ·
      refine ⟨316739763953118386926705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1689278741083298063609093 316739763953118386926705)
      ·
        refine ⟨237554822964838790195029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316739763953118386926705 237554822964838790195029)
        ·
          refine ⟨1391922790809602286299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 237554822964838790195029 1391922790809602286299)
          ·
            rfl

theorem cell19_123509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 9].length) (baseStart_123509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123509 prefixEnd_123509 := by exact prefixLift 123509
  have htrace : WordTrace (prefixWord ++ tailWord_123509) baseStart_123509 baseEnd_123509 := by
    simpa [prefixWord, tailWord_123509, baseEnd_123509] using wordTrace_append hprefix tailTrace_123509
  have hstable : (prefixWord ++ tailWord_123509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123509).length < 2 ^ (prefixWord ++ tailWord_123509).sum := by decide
  have hdescent : baseEnd_123509 < baseStart_123509 := by decide
  rcases family_descends (prefixWord ++ tailWord_123509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123562 : List Nat := [3, 1, 5, 2, 1, 1, 6]
def baseStart_123562 : Nat := 118140960795 + 123562 * 2 ^ 59
def prefixEnd_123562 : Nat := 4983230072969 + 3 ^ 40 * 123562 * 2
def baseEnd_123562 : Nat := 12532680815990280850717

theorem tailTrace_123562 : CollatzResearch.WordTrace tailWord_123562 prefixEnd_123562 12532680815990280850717 := by
  unfold tailWord_123562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1126669094590862888659235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3004450918908967703091293 1126669094590862888659235)
  ·
    refine ⟨1690003641886294332988853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1126669094590862888659235 1690003641886294332988853)
    ·
      refine ⟨158437841426840093717705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1690003641886294332988853 158437841426840093717705)
      ·
        refine ⟨118828381070130070288279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158437841426840093717705 118828381070130070288279)
        ·
          refine ⟨178242571605195105432419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118828381070130070288279 178242571605195105432419)
          ·
            refine ⟨267363857407792658148629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178242571605195105432419 267363857407792658148629)
            ·
              refine ⟨12532680815990280850717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 267363857407792658148629 12532680815990280850717)
              ·
                rfl

theorem cell19_123562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 6].length) (baseStart_123562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123562 prefixEnd_123562 := by exact prefixLift 123562
  have htrace : WordTrace (prefixWord ++ tailWord_123562) baseStart_123562 baseEnd_123562 := by
    simpa [prefixWord, tailWord_123562, baseEnd_123562] using wordTrace_append hprefix tailTrace_123562
  have hstable : (prefixWord ++ tailWord_123562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123562).length < 2 ^ (prefixWord ++ tailWord_123562).sum := by decide
  have hdescent : baseEnd_123562 < baseStart_123562 := by decide
  rcases family_descends (prefixWord ++ tailWord_123562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123602 : List Nat := [3, 2, 2, 2, 3, 1, 1, 5]
def baseStart_123602 : Nat := 118140960795 + 123602 * 2 ^ 59
def prefixEnd_123602 : Nat := 4983230072969 + 3 ^ 40 * 123602 * 2
def baseEnd_123602 : Nat := 37610213841262601663153

theorem tailTrace_123602 : CollatzResearch.WordTrace tailWord_123602 prefixEnd_123602 37610213841262601663153 := by
  unfold tailWord_123602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127033824554634596523265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3005423532145692257395373 1127033824554634596523265)
  ·
    refine ⟨845275368415975947392449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1127033824554634596523265 845275368415975947392449)
    ·
      refine ⟨633956526311981960544337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 845275368415975947392449 633956526311981960544337)
      ·
        refine ⟨475467394733986470408253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633956526311981960544337 475467394733986470408253)
        ·
          refine ⟨178300273025244926403095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475467394733986470408253 178300273025244926403095)
          ·
            refine ⟨267450409537867389604643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178300273025244926403095 267450409537867389604643)
            ·
              refine ⟨401175614306801084406965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267450409537867389604643 401175614306801084406965)
              ·
                refine ⟨37610213841262601663153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 401175614306801084406965 37610213841262601663153)
                ·
                  rfl

theorem cell19_123602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_123602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123602 prefixEnd_123602 := by exact prefixLift 123602
  have htrace : WordTrace (prefixWord ++ tailWord_123602) baseStart_123602 baseEnd_123602 := by
    simpa [prefixWord, tailWord_123602, baseEnd_123602] using wordTrace_append hprefix tailTrace_123602
  have hstable : (prefixWord ++ tailWord_123602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123602).length < 2 ^ (prefixWord ++ tailWord_123602).sum := by decide
  have hdescent : baseEnd_123602 < baseStart_123602 := by decide
  rcases family_descends (prefixWord ++ tailWord_123602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123625 : List Nat := [1, 2, 1, 1, 1, 2, 11]
def baseStart_123625 : Nat := 118140960795 + 123625 * 2 ^ 59
def prefixEnd_123625 : Nat := 4983230072969 + 3 ^ 40 * 123625 * 2
def baseEnd_123625 : Nat := 12539070797468454383993

theorem tailTrace_123625 : CollatzResearch.WordTrace tailWord_123625 prefixEnd_123625 12539070797468454383993 := by
  unfold tailWord_123625
  simp only [CollatzResearch.WordTrace]
  refine ⟨4508974177135213314180329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3005982784756808876120219 4508974177135213314180329)
  ·
    refine ⟨3381730632851409985635247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4508974177135213314180329 3381730632851409985635247)
    ·
      refine ⟨5072595949277114978452871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3381730632851409985635247 5072595949277114978452871)
      ·
        refine ⟨7608893923915672467679307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072595949277114978452871 7608893923915672467679307)
        ·
          refine ⟨11413340885873508701518961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608893923915672467679307 11413340885873508701518961)
          ·
            refine ⟨8560005664405131526139221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11413340885873508701518961 8560005664405131526139221)
            ·
              refine ⟨12539070797468454383993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8560005664405131526139221 12539070797468454383993)
              ·
                rfl

theorem cell19_123625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_123625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123625 prefixEnd_123625 := by exact prefixLift 123625
  have htrace : WordTrace (prefixWord ++ tailWord_123625) baseStart_123625 baseEnd_123625 := by
    simpa [prefixWord, tailWord_123625, baseEnd_123625] using wordTrace_append hprefix tailTrace_123625
  have hstable : (prefixWord ++ tailWord_123625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123625).length < 2 ^ (prefixWord ++ tailWord_123625).sum := by decide
  have hdescent : baseEnd_123625 < baseStart_123625 := by decide
  rcases family_descends (prefixWord ++ tailWord_123625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123636 : List Nat := [2, 6, 1, 1, 2, 1, 2, 4]
def baseStart_123636 : Nat := 118140960795 + 123636 * 2 ^ 59
def prefixEnd_123636 : Nat := 4983230072969 + 3 ^ 40 * 123636 * 2
def baseEnd_123636 : Nat := 37620559525560596907505

theorem tailTrace_123636 : CollatzResearch.WordTrace tailWord_123636 prefixEnd_123636 37620559525560596907505 := by
  unfold tailWord_123636
  simp only [CollatzResearch.WordTrace]
  refine ⟨2254687690047681096415381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3006250253396908128553841 2254687690047681096415381)
  ·
    refine ⟨105688485470985051394471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2254687690047681096415381 105688485470985051394471)
    ·
      refine ⟨158532728206477577091707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105688485470985051394471 158532728206477577091707)
      ·
        refine ⟨237799092309716365637561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158532728206477577091707 237799092309716365637561)
        ·
          refine ⟨178349319232287274228171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237799092309716365637561 178349319232287274228171)
          ·
            refine ⟨267523978848430911342257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178349319232287274228171 267523978848430911342257)
            ·
              refine ⟨200642984136323183506693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267523978848430911342257 200642984136323183506693)
              ·
                refine ⟨37620559525560596907505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200642984136323183506693 37620559525560596907505)
                ·
                  rfl

theorem cell19_123636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_123636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123636 prefixEnd_123636 := by exact prefixLift 123636
  have htrace : WordTrace (prefixWord ++ tailWord_123636) baseStart_123636 baseEnd_123636 := by
    simpa [prefixWord, tailWord_123636, baseEnd_123636] using wordTrace_append hprefix tailTrace_123636
  have hstable : (prefixWord ++ tailWord_123636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123636).length < 2 ^ (prefixWord ++ tailWord_123636).sum := by decide
  have hdescent : baseEnd_123636 < baseStart_123636 := by decide
  rcases family_descends (prefixWord ++ tailWord_123636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123663 : List Nat := [1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_123663 : Nat := 118140960795 + 123663 * 2 ^ 59
def prefixEnd_123663 : Nat := 4983230072969 + 3 ^ 40 * 123663 * 2
def baseEnd_123663 : Nat := 37628775216032534307431

theorem tailTrace_123663 : CollatzResearch.WordTrace tailWord_123663 prefixEnd_123663 37628775216032534307431 := by
  unfold tailWord_123663
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510360150997545804063643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3006906767331697202709095 4510360150997545804063643)
  ·
    refine ⟨6765540226496318706095465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4510360150997545804063643 6765540226496318706095465)
    ·
      refine ⟨5074155169872239029571599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6765540226496318706095465 5074155169872239029571599)
      ·
        refine ⟨7611232754808358544357399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5074155169872239029571599 7611232754808358544357399)
        ·
          refine ⟨11416849132212537816536099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7611232754808358544357399 11416849132212537816536099)
          ·
            refine ⟨17125273698318806724804149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11416849132212537816536099 17125273698318806724804149)
            ·
              refine ⟨1605494409217388130450389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17125273698318806724804149 1605494409217388130450389)
              ·
                refine ⟨37628775216032534307431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1605494409217388130450389 37628775216032534307431)
                ·
                  rfl

theorem cell19_123663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_123663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123663 prefixEnd_123663 := by exact prefixLift 123663
  have htrace : WordTrace (prefixWord ++ tailWord_123663) baseStart_123663 baseEnd_123663 := by
    simpa [prefixWord, tailWord_123663, baseEnd_123663] using wordTrace_append hprefix tailTrace_123663
  have hstable : (prefixWord ++ tailWord_123663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123663).length < 2 ^ (prefixWord ++ tailWord_123663).sum := by decide
  have hdescent : baseEnd_123663 < baseStart_123663 := by decide
  rcases family_descends (prefixWord ++ tailWord_123663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123693 : List Nat := [1, 5, 3, 2, 1, 2, 1, 4]
def baseStart_123693 : Nat := 118140960795 + 123693 * 2 ^ 59
def prefixEnd_123693 : Nat := 4983230072969 + 3 ^ 40 * 123693 * 2
def baseEnd_123693 : Nat := 37637903761001353640683

theorem tailTrace_123693 : CollatzResearch.WordTrace tailWord_123693 prefixEnd_123693 37637903761001353640683 := by
  unfold tailWord_123693
  simp only [CollatzResearch.WordTrace]
  refine ⟨4511454340888860927655733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3007636227259240618437155 4511454340888860927655733)
  ·
    refine ⟨422948844458330711967725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4511454340888860927655733 422948844458330711967725)
    ·
      refine ⟨158605816671874016987897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422948844458330711967725 158605816671874016987897)
      ·
        refine ⟨118954362503905512740923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158605816671874016987897 118954362503905512740923)
        ·
          refine ⟨178431543755858269111385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118954362503905512740923 178431543755858269111385)
          ·
            refine ⟨133823657816893701833539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178431543755858269111385 133823657816893701833539)
            ·
              refine ⟨200735486725340552750309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133823657816893701833539 200735486725340552750309)
              ·
                refine ⟨37637903761001353640683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200735486725340552750309 37637903761001353640683)
                ·
                  rfl

theorem cell19_123693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 4].length) (baseStart_123693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123693 prefixEnd_123693 := by exact prefixLift 123693
  have htrace : WordTrace (prefixWord ++ tailWord_123693) baseStart_123693 baseEnd_123693 := by
    simpa [prefixWord, tailWord_123693, baseEnd_123693] using wordTrace_append hprefix tailTrace_123693
  have hstable : (prefixWord ++ tailWord_123693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123693).length < 2 ^ (prefixWord ++ tailWord_123693).sum := by decide
  have hdescent : baseEnd_123693 < baseStart_123693 := by decide
  rcases family_descends (prefixWord ++ tailWord_123693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123699 : List Nat := [1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_123699 : Nat := 118140960795 + 123699 * 2 ^ 59
def prefixEnd_123699 : Nat := 4983230072969 + 3 ^ 40 * 123699 * 2
def baseEnd_123699 : Nat := 37639729469995117507333

theorem tailTrace_123699 : CollatzResearch.WordTrace tailWord_123699 prefixEnd_123699 37639729469995117507333 := by
  unfold tailWord_123699
  simp only [CollatzResearch.WordTrace]
  refine ⟨4511673178867123952374151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3007782119244749301582767 4511673178867123952374151)
  ·
    refine ⟨6767509768300685928561227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4511673178867123952374151 6767509768300685928561227)
    ·
      refine ⟨10151264652451028892841841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6767509768300685928561227 10151264652451028892841841)
      ·
        refine ⟨7613448489338271669631381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10151264652451028892841841 7613448489338271669631381)
        ·
          refine ⟨356880397937731484513971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7613448489338271669631381 356880397937731484513971)
          ·
            refine ⟨535320596906597226770957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356880397937731484513971 535320596906597226770957)
            ·
              refine ⟨200745223839973960039109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535320596906597226770957 200745223839973960039109)
              ·
                refine ⟨37639729469995117507333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200745223839973960039109 37639729469995117507333)
                ·
                  rfl

theorem cell19_123699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_123699 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123699 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123699 prefixEnd_123699 := by exact prefixLift 123699
  have htrace : WordTrace (prefixWord ++ tailWord_123699) baseStart_123699 baseEnd_123699 := by
    simpa [prefixWord, tailWord_123699, baseEnd_123699] using wordTrace_append hprefix tailTrace_123699
  have hstable : (prefixWord ++ tailWord_123699).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123699).length < 2 ^ (prefixWord ++ tailWord_123699).sum := by decide
  have hdescent : baseEnd_123699 < baseStart_123699 := by decide
  rcases family_descends (prefixWord ++ tailWord_123699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123775 : List Nat := [1, 1, 2, 2, 1, 1, 8, 3]
def baseStart_123775 : Nat := 118140960795 + 123775 * 2 ^ 59
def prefixEnd_123775 : Nat := 4983230072969 + 3 ^ 40 * 123775 * 2
def baseEnd_123775 : Nat := 37662855117249459818237

theorem tailTrace_123775 : CollatzResearch.WordTrace tailWord_123775 prefixEnd_123775 37662855117249459818237 := by
  unfold tailWord_123775
  simp only [CollatzResearch.WordTrace]
  refine ⟨4514445126591788932140779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3009630084394525954760519 4514445126591788932140779)
  ·
    refine ⟨6771667689887683398211169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4514445126591788932140779 6771667689887683398211169)
    ·
      refine ⟨5078750767415762548658377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6771667689887683398211169 5078750767415762548658377)
      ·
        refine ⟨3809063075561821911493783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5078750767415762548658377 3809063075561821911493783)
        ·
          refine ⟨5713594613342732867240675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3809063075561821911493783 5713594613342732867240675)
          ·
            refine ⟨8570391920014099300861013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713594613342732867240675 8570391920014099300861013)
            ·
              refine ⟨100434280312665226181965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 8570391920014099300861013 100434280312665226181965)
              ·
                refine ⟨37662855117249459818237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100434280312665226181965 37662855117249459818237)
                ·
                  rfl

theorem cell19_123775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 3].length) (baseStart_123775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123775 prefixEnd_123775 := by exact prefixLift 123775
  have htrace : WordTrace (prefixWord ++ tailWord_123775) baseStart_123775 baseEnd_123775 := by
    simpa [prefixWord, tailWord_123775, baseEnd_123775] using wordTrace_append hprefix tailTrace_123775
  have hstable : (prefixWord ++ tailWord_123775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123775).length < 2 ^ (prefixWord ++ tailWord_123775).sum := by decide
  have hdescent : baseEnd_123775 < baseStart_123775 := by decide
  rcases family_descends (prefixWord ++ tailWord_123775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123834 : List Nat := [3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_123834 : Nat := 118140960795 + 123834 * 2 ^ 59
def prefixEnd_123834 : Nat := 4983230072969 + 3 ^ 40 * 123834 * 2
def baseEnd_123834 : Nat := 37680807922354804506965

theorem tailTrace_123834 : CollatzResearch.WordTrace tailWord_123834 prefixEnd_123834 37680807922354804506965 := by
  unfold tailWord_123834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129149258344510502134639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3011064688918694672359037 1129149258344510502134639)
  ·
    refine ⟨1693723887516765753201959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1129149258344510502134639 1693723887516765753201959)
    ·
      refine ⟨2540585831275148629802939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1693723887516765753201959 2540585831275148629802939)
      ·
        refine ⟨3810878746912722944704409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540585831275148629802939 3810878746912722944704409)
        ·
          refine ⟨2858159060184542208528307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3810878746912722944704409 2858159060184542208528307)
          ·
            refine ⟨4287238590276813312792461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858159060184542208528307 4287238590276813312792461)
            ·
              refine ⟨1607714471353804992297173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4287238590276813312792461 1607714471353804992297173)
              ·
                refine ⟨37680807922354804506965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1607714471353804992297173 37680807922354804506965)
                ·
                  rfl

theorem cell19_123834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_123834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123834 prefixEnd_123834 := by exact prefixLift 123834
  have htrace : WordTrace (prefixWord ++ tailWord_123834) baseStart_123834 baseEnd_123834 := by
    simpa [prefixWord, tailWord_123834, baseEnd_123834] using wordTrace_append hprefix tailTrace_123834
  have hstable : (prefixWord ++ tailWord_123834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123834).length < 2 ^ (prefixWord ++ tailWord_123834).sum := by decide
  have hdescent : baseEnd_123834 < baseStart_123834 := by decide
  rcases family_descends (prefixWord ++ tailWord_123834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123948 : List Nat := [2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_123948 : Nat := 118140960795 + 123948 * 2 ^ 59
def prefixEnd_123948 : Nat := 4983230072969 + 3 ^ 40 * 123948 * 2
def baseEnd_123948 : Nat := 37715496393236317973321

theorem tailTrace_123948 : CollatzResearch.WordTrace tailWord_123948 prefixEnd_123948 37715496393236317973321 := by
  unfold tailWord_123948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2260377477482519739094249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3013836636643359652125665 2260377477482519739094249)
  ·
    refine ⟨1695283108111889804320687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2260377477482519739094249 1695283108111889804320687)
    ·
      refine ⟨2542924662167834706481031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695283108111889804320687 2542924662167834706481031)
      ·
        refine ⟨3814386993251752059721547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2542924662167834706481031 3814386993251752059721547)
        ·
          refine ⟨5721580489877628089582321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3814386993251752059721547 5721580489877628089582321)
          ·
            refine ⟨4291185367408221067186741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5721580489877628089582321 4291185367408221067186741)
            ·
              refine ⟨402298628194520725048757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4291185367408221067186741 402298628194520725048757)
              ·
                refine ⟨37715496393236317973321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 402298628194520725048757 37715496393236317973321)
                ·
                  rfl

theorem cell19_123948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_123948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123948 prefixEnd_123948 := by exact prefixLift 123948
  have htrace : WordTrace (prefixWord ++ tailWord_123948) baseStart_123948 baseEnd_123948 := by
    simpa [prefixWord, tailWord_123948, baseEnd_123948] using wordTrace_append hprefix tailTrace_123948
  have hstable : (prefixWord ++ tailWord_123948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123948).length < 2 ^ (prefixWord ++ tailWord_123948).sum := by decide
  have hdescent : baseEnd_123948 < baseStart_123948 := by decide
  rcases family_descends (prefixWord ++ tailWord_123948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123965 : List Nat := [1, 4, 1, 3, 1, 4, 5]
def baseStart_123965 : Nat := 118140960795 + 123965 * 2 ^ 59
def prefixEnd_123965 : Nat := 4983230072969 + 3 ^ 40 * 123965 * 2
def baseEnd_123965 : Nat := 12573556411795105198499

theorem tailTrace_123965 : CollatzResearch.WordTrace tailWord_123965 prefixEnd_123965 12573556411795105198499 := by
  unfold tailWord_123965
  simp only [CollatzResearch.WordTrace]
  refine ⟨4521374995903451381557349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3014249997268967587704899 4521374995903451381557349)
  ·
    refine ⟨847757811731897134042003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4521374995903451381557349 847757811731897134042003)
    ·
      refine ⟨1271636717597845701063005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847757811731897134042003 1271636717597845701063005)
      ·
        refine ⟨476863769099192137898627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1271636717597845701063005 476863769099192137898627)
        ·
          refine ⟨715295653648788206847941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476863769099192137898627 715295653648788206847941)
          ·
            refine ⟨134117935059147788783989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 715295653648788206847941 134117935059147788783989)
            ·
              refine ⟨12573556411795105198499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134117935059147788783989 12573556411795105198499)
              ·
                rfl

theorem cell19_123965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_123965 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_123965 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_123965 prefixEnd_123965 := by exact prefixLift 123965
  have htrace : WordTrace (prefixWord ++ tailWord_123965) baseStart_123965 baseEnd_123965 := by
    simpa [prefixWord, tailWord_123965, baseEnd_123965] using wordTrace_append hprefix tailTrace_123965
  have hstable : (prefixWord ++ tailWord_123965).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123965).length < 2 ^ (prefixWord ++ tailWord_123965).sum := by decide
  have hdescent : baseEnd_123965 < baseStart_123965 := by decide
  rcases family_descends (prefixWord ++ tailWord_123965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124005 : List Nat := [1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_124005 : Nat := 118140960795 + 124005 * 2 ^ 59
def prefixEnd_124005 : Nat := 4983230072969 + 3 ^ 40 * 124005 * 2
def baseEnd_124005 : Nat := 37732840628677074706499

theorem tailTrace_124005 : CollatzResearch.WordTrace tailWord_124005 prefixEnd_124005 37732840628677074706499 := by
  unfold tailWord_124005
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522833915758538213013469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3015222610505692142008979 4522833915758538213013469)
  ·
    refine ⟨1696062718409451829880051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4522833915758538213013469 1696062718409451829880051)
    ·
      refine ⟨2544094077614177744820077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696062718409451829880051 2544094077614177744820077)
      ·
        refine ⟨954035279105316654307529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2544094077614177744820077 954035279105316654307529)
        ·
          refine ⟨715526459328987490730647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954035279105316654307529 715526459328987490730647)
          ·
            refine ⟨1073289688993481236095971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715526459328987490730647 1073289688993481236095971)
            ·
              refine ⟨1609934533490221854143957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073289688993481236095971 1609934533490221854143957)
              ·
                refine ⟨37732840628677074706499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1609934533490221854143957 37732840628677074706499)
                ·
                  rfl

theorem cell19_124005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_124005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124005 prefixEnd_124005 := by exact prefixLift 124005
  have htrace : WordTrace (prefixWord ++ tailWord_124005) baseStart_124005 baseEnd_124005 := by
    simpa [prefixWord, tailWord_124005, baseEnd_124005] using wordTrace_append hprefix tailTrace_124005
  have hstable : (prefixWord ++ tailWord_124005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124005).length < 2 ^ (prefixWord ++ tailWord_124005).sum := by decide
  have hdescent : baseEnd_124005 < baseStart_124005 := by decide
  rcases family_descends (prefixWord ++ tailWord_124005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124041 : List Nat := [1, 2, 1, 1, 4, 5, 1, 4]
def baseStart_124041 : Nat := 118140960795 + 124041 * 2 ^ 59
def prefixEnd_124041 : Nat := 4983230072969 + 3 ^ 40 * 124041 * 2
def baseEnd_124041 : Nat := 37743794882639657906401

theorem tailTrace_124041 : CollatzResearch.WordTrace tailWord_124041 prefixEnd_124041 37743794882639657906401 := by
  unfold tailWord_124041
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524146943628116361323977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3016097962418744240882651 4524146943628116361323977)
  ·
    refine ⟨3393110207721087270992983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4524146943628116361323977 3393110207721087270992983)
    ·
      refine ⟨5089665311581630906489475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3393110207721087270992983 5089665311581630906489475)
      ·
        refine ⟨7634497967372446359734213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089665311581630906489475 7634497967372446359734213)
        ·
          refine ⟨1431468368882333692450165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7634497967372446359734213 1431468368882333692450165)
          ·
            refine ⟨134200159582718783667203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1431468368882333692450165 134200159582718783667203)
            ·
              refine ⟨201300239374078175500805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134200159582718783667203 201300239374078175500805)
              ·
                refine ⟨37743794882639657906401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201300239374078175500805 37743794882639657906401)
                ·
                  rfl

theorem cell19_124041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_124041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124041 prefixEnd_124041 := by exact prefixLift 124041
  have htrace : WordTrace (prefixWord ++ tailWord_124041) baseStart_124041 baseEnd_124041 := by
    simpa [prefixWord, tailWord_124041, baseEnd_124041] using wordTrace_append hprefix tailTrace_124041
  have hstable : (prefixWord ++ tailWord_124041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124041).length < 2 ^ (prefixWord ++ tailWord_124041).sum := by decide
  have hdescent : baseEnd_124041 < baseStart_124041 := by decide
  rcases family_descends (prefixWord ++ tailWord_124041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124058 : List Nat := [3, 1, 1, 5, 1, 2, 3, 3]
def baseStart_124058 : Nat := 118140960795 + 124058 * 2 ^ 59
def prefixEnd_124058 : Nat := 4983230072969 + 3 ^ 40 * 124058 * 2
def baseEnd_124058 : Nat := 37748967724788655528577

theorem tailTrace_124058 : CollatzResearch.WordTrace tailWord_124058 prefixEnd_124058 37748967724788655528577 := by
  unfold tailWord_124058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1131191746141632066173207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3016511323044352176461885 1131191746141632066173207)
  ·
    refine ⟨1696787619212448099259811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1131191746141632066173207 1696787619212448099259811)
    ·
      refine ⟨2545181428818672148889717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696787619212448099259811 2545181428818672148889717)
      ·
        refine ⟨238610758951750513958411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2545181428818672148889717 238610758951750513958411)
        ·
          refine ⟨357916138427625770937617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238610758951750513958411 357916138427625770937617)
          ·
            refine ⟨268437103820719328203213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357916138427625770937617 268437103820719328203213)
            ·
              refine ⟨100663913932769748076205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268437103820719328203213 100663913932769748076205)
              ·
                refine ⟨37748967724788655528577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100663913932769748076205 37748967724788655528577)
                ·
                  rfl

theorem cell19_124058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_124058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124058 prefixEnd_124058 := by exact prefixLift 124058
  have htrace : WordTrace (prefixWord ++ tailWord_124058) baseStart_124058 baseEnd_124058 := by
    simpa [prefixWord, tailWord_124058, baseEnd_124058] using wordTrace_append hprefix tailTrace_124058
  have hstable : (prefixWord ++ tailWord_124058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124058).length < 2 ^ (prefixWord ++ tailWord_124058).sum := by decide
  have hdescent : baseEnd_124058 < baseStart_124058 := by decide
  rcases family_descends (prefixWord ++ tailWord_124058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124109 : List Nat := [1, 6, 2, 2, 2, 1, 2, 3]
def baseStart_124109 : Nat := 118140960795 + 124109 * 2 ^ 59
def prefixEnd_124109 : Nat := 4983230072969 + 3 ^ 40 * 124109 * 2
def baseEnd_124109 : Nat := 37764486251235648395105

theorem tailTrace_124109 : CollatzResearch.WordTrace tailWord_124109 prefixEnd_124109 37764486251235648395105 := by
  unfold tailWord_124109
  simp only [CollatzResearch.WordTrace]
  refine ⟨4526627107381763974799381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3017751404921175983199587 4526627107381763974799381)
  ·
    refine ⟨212185645658520186318721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4526627107381763974799381 212185645658520186318721)
    ·
      refine ⟨159139234243890139739041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212185645658520186318721 159139234243890139739041)
      ·
        refine ⟨119354425682917604804281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159139234243890139739041 119354425682917604804281)
        ·
          refine ⟨89515819262188203603211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119354425682917604804281 89515819262188203603211)
          ·
            refine ⟨134273728893282305404817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89515819262188203603211 134273728893282305404817)
            ·
              refine ⟨100705296669961729053613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134273728893282305404817 100705296669961729053613)
              ·
                refine ⟨37764486251235648395105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100705296669961729053613 37764486251235648395105)
                ·
                  rfl

theorem cell19_124109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 3].length) (baseStart_124109 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124109 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124109 prefixEnd_124109 := by exact prefixLift 124109
  have htrace : WordTrace (prefixWord ++ tailWord_124109) baseStart_124109 baseEnd_124109 := by
    simpa [prefixWord, tailWord_124109, baseEnd_124109] using wordTrace_append hprefix tailTrace_124109
  have hstable : (prefixWord ++ tailWord_124109).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124109).length < 2 ^ (prefixWord ++ tailWord_124109).sum := by decide
  have hdescent : baseEnd_124109 < baseStart_124109 := by decide
  rcases family_descends (prefixWord ++ tailWord_124109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124117 : List Nat := [1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_124117 : Nat := 118140960795 + 124117 * 2 ^ 59
def prefixEnd_124117 : Nat := 4983230072969 + 3 ^ 40 * 124117 * 2
def baseEnd_124117 : Nat := 37766920529894000217305

theorem tailTrace_124117 : CollatzResearch.WordTrace tailWord_124117 prefixEnd_124117 37766920529894000217305 := by
  unfold tailWord_124117
  simp only [CollatzResearch.WordTrace]
  refine ⟨4526918891352781341090605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3017945927568520894060403 4526918891352781341090605)
  ·
    refine ⟨1697594584257293002908977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4526918891352781341090605 1697594584257293002908977)
    ·
      refine ⟨1273195938192969752181733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1697594584257293002908977 1273195938192969752181733)
      ·
        refine ⟨238724238411181828534075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1273195938192969752181733 238724238411181828534075)
        ·
          refine ⟨358086357616772742801113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238724238411181828534075 358086357616772742801113)
          ·
            refine ⟨268564768212579557100835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358086357616772742801113 268564768212579557100835)
            ·
              refine ⟨402847152318869335651253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268564768212579557100835 402847152318869335651253)
              ·
                refine ⟨37766920529894000217305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 402847152318869335651253 37766920529894000217305)
                ·
                  rfl

theorem cell19_124117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_124117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124117 prefixEnd_124117 := by exact prefixLift 124117
  have htrace : WordTrace (prefixWord ++ tailWord_124117) baseStart_124117 baseEnd_124117 := by
    simpa [prefixWord, tailWord_124117, baseEnd_124117] using wordTrace_append hprefix tailTrace_124117
  have hstable : (prefixWord ++ tailWord_124117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124117).length < 2 ^ (prefixWord ++ tailWord_124117).sum := by decide
  have hdescent : baseEnd_124117 < baseStart_124117 := by decide
  rcases family_descends (prefixWord ++ tailWord_124117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124138 : List Nat := [3, 1, 3, 1, 1, 3, 7]
def baseStart_124138 : Nat := 118140960795 + 124138 * 2 ^ 59
def prefixEnd_124138 : Nat := 4983230072969 + 3 ^ 40 * 124138 * 2
def baseEnd_124138 : Nat := 12591103503790724583527

theorem tailTrace_124138 : CollatzResearch.WordTrace tailWord_124138 prefixEnd_124138 12591103503790724583527 := by
  unfold tailWord_124138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1131921206069175481901267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3018456549517801285070045 1131921206069175481901267)
  ·
    refine ⟨1697881809103763222851901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1131921206069175481901267 1697881809103763222851901)
    ·
      refine ⟨636705678413911208569463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1697881809103763222851901 636705678413911208569463)
      ·
        refine ⟨955058517620866812854195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636705678413911208569463 955058517620866812854195)
        ·
          refine ⟨1432587776431300219281293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955058517620866812854195 1432587776431300219281293)
          ·
            refine ⟨537220416161737582230485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1432587776431300219281293 537220416161737582230485)
            ·
              refine ⟨12591103503790724583527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 537220416161737582230485 12591103503790724583527)
              ·
                rfl

theorem cell19_124138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_124138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124138 prefixEnd_124138 := by exact prefixLift 124138
  have htrace : WordTrace (prefixWord ++ tailWord_124138) baseStart_124138 baseEnd_124138 := by
    simpa [prefixWord, tailWord_124138, baseEnd_124138] using wordTrace_append hprefix tailTrace_124138
  have hstable : (prefixWord ++ tailWord_124138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124138).length < 2 ^ (prefixWord ++ tailWord_124138).sum := by decide
  have hdescent : baseEnd_124138 < baseStart_124138 := by decide
  rcases family_descends (prefixWord ++ tailWord_124138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124231 : List Nat := [1, 1, 4, 1, 2, 4, 3, 3]
def baseStart_124231 : Nat := 118140960795 + 124231 * 2 ^ 59
def prefixEnd_124231 : Nat := 4983230072969 + 3 ^ 40 * 124231 * 2
def baseEnd_124231 : Nat := 37801609000775513683661

theorem tailTrace_124231 : CollatzResearch.WordTrace tailWord_124231 prefixEnd_124231 37801609000775513683661 := by
  unfold tailWord_124231
  simp only [CollatzResearch.WordTrace]
  refine ⟨4531076812939778810740547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3020717875293185873827031 4531076812939778810740547)
  ·
    refine ⟨6796615219409668216110821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4531076812939778810740547 6796615219409668216110821)
    ·
      refine ⟨1274365353639312790520779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6796615219409668216110821 1274365353639312790520779)
      ·
        refine ⟨1911548030458969185781169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274365353639312790520779 1911548030458969185781169)
        ·
          refine ⟨1433661022844226889335877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1911548030458969185781169 1433661022844226889335877)
          ·
            refine ⟨268811441783292541750477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1433661022844226889335877 268811441783292541750477)
            ·
              refine ⟨100804290668734703156429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268811441783292541750477 100804290668734703156429)
              ·
                refine ⟨37801609000775513683661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100804290668734703156429 37801609000775513683661)
                ·
                  rfl

theorem cell19_124231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 3].length) (baseStart_124231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124231 prefixEnd_124231 := by exact prefixLift 124231
  have htrace : WordTrace (prefixWord ++ tailWord_124231) baseStart_124231 baseEnd_124231 := by
    simpa [prefixWord, tailWord_124231, baseEnd_124231] using wordTrace_append hprefix tailTrace_124231
  have hstable : (prefixWord ++ tailWord_124231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124231).length < 2 ^ (prefixWord ++ tailWord_124231).sum := by decide
  have hdescent : baseEnd_124231 < baseStart_124231 := by decide
  rcases family_descends (prefixWord ++ tailWord_124231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124385 : List Nat := [1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_124385 : Nat := 118140960795 + 124385 * 2 ^ 59
def prefixEnd_124385 : Nat := 4983230072969 + 3 ^ 40 * 124385 * 2
def baseEnd_124385 : Nat := 37848468864948786261019

theorem tailTrace_124385 : CollatzResearch.WordTrace tailWord_124385 prefixEnd_124385 37848468864948786261019 := by
  unfold tailWord_124385
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536693654381863111846609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3024462436254575407897739 4536693654381863111846609)
  ·
    refine ⟨3402520240786397333884957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4536693654381863111846609 3402520240786397333884957)
    ·
      refine ⟨1275945090294899000206859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3402520240786397333884957 1275945090294899000206859)
      ·
        refine ⟨1913917635442348500310289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275945090294899000206859 1913917635442348500310289)
        ·
          refine ⟨1435438226581761375232717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1913917635442348500310289 1435438226581761375232717)
          ·
            refine ⟨538289334968160515712269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1435438226581761375232717 538289334968160515712269)
            ·
              refine ⟨201858500613060193392101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 538289334968160515712269 201858500613060193392101)
              ·
                refine ⟨37848468864948786261019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201858500613060193392101 37848468864948786261019)
                ·
                  rfl

theorem cell19_124385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_124385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124385 prefixEnd_124385 := by exact prefixLift 124385
  have htrace : WordTrace (prefixWord ++ tailWord_124385) baseStart_124385 baseEnd_124385 := by
    simpa [prefixWord, tailWord_124385, baseEnd_124385] using wordTrace_append hprefix tailTrace_124385
  have hstable : (prefixWord ++ tailWord_124385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124385).length < 2 ^ (prefixWord ++ tailWord_124385).sum := by decide
  have hdescent : baseEnd_124385 < baseStart_124385 := by decide
  rcases family_descends (prefixWord ++ tailWord_124385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124423 : List Nat := [1, 1, 4, 3, 2, 2, 6]
def baseStart_124423 : Nat := 118140960795 + 124423 * 2 ^ 59
def prefixEnd_124423 : Nat := 4983230072969 + 3 ^ 40 * 124423 * 2
def baseEnd_124423 : Nat := 12620010562858652472157

theorem tailTrace_124423 : CollatzResearch.WordTrace tailWord_124423 prefixEnd_124423 12620010562858652472157 := by
  unfold tailWord_124423
  simp only [CollatzResearch.WordTrace]
  refine ⟨4538079628244195601729923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3025386418829463734486615 4538079628244195601729923)
  ·
    refine ⟨6807119442366293402594885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4538079628244195601729923 6807119442366293402594885)
    ·
      refine ⟨1276334895443680012986541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6807119442366293402594885 1276334895443680012986541)
      ·
        refine ⟨478625585791380004869953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1276334895443680012986541 478625585791380004869953)
        ·
          refine ⟨358969189343535003652465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478625585791380004869953 358969189343535003652465)
          ·
            refine ⟨269226892007651252739349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358969189343535003652465 269226892007651252739349)
            ·
              refine ⟨12620010562858652472157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269226892007651252739349 12620010562858652472157)
              ·
                rfl

theorem cell19_124423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_124423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124423 prefixEnd_124423 := by exact prefixLift 124423
  have htrace : WordTrace (prefixWord ++ tailWord_124423) baseStart_124423 baseEnd_124423 := by
    simpa [prefixWord, tailWord_124423, baseEnd_124423] using wordTrace_append hprefix tailTrace_124423
  have hstable : (prefixWord ++ tailWord_124423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124423).length < 2 ^ (prefixWord ++ tailWord_124423).sum := by decide
  have hdescent : baseEnd_124423 < baseStart_124423 := by decide
  rcases family_descends (prefixWord ++ tailWord_124423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124425 : List Nat := [1, 2, 1, 1, 3, 1, 10]
def baseStart_124425 : Nat := 118140960795 + 124425 * 2 ^ 59
def prefixEnd_124425 : Nat := 4983230072969 + 3 ^ 40 * 124425 * 2
def baseEnd_124425 : Nat := 12620213419413515124007

theorem tailTrace_124425 : CollatzResearch.WordTrace tailWord_124425 prefixEnd_124425 12620213419413515124007 := by
  unfold tailWord_124425
  simp only [CollatzResearch.WordTrace]
  refine ⟨4538152574236949943302729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3025435049491299962201819 4538152574236949943302729)
  ·
    refine ⟨3403614430677712457477047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4538152574236949943302729 3403614430677712457477047)
    ·
      refine ⟨5105421646016568686215571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3403614430677712457477047 5105421646016568686215571)
      ·
        refine ⟨7658132469024853029323357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5105421646016568686215571 7658132469024853029323357)
        ·
          refine ⟨2871799675884319885996259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7658132469024853029323357 2871799675884319885996259)
          ·
            refine ⟨4307699513826479828994389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871799675884319885996259 4307699513826479828994389)
            ·
              refine ⟨12620213419413515124007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4307699513826479828994389 12620213419413515124007)
              ·
                rfl

theorem cell19_124425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_124425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124425 prefixEnd_124425 := by exact prefixLift 124425
  have htrace : WordTrace (prefixWord ++ tailWord_124425) baseStart_124425 baseEnd_124425 := by
    simpa [prefixWord, tailWord_124425, baseEnd_124425] using wordTrace_append hprefix tailTrace_124425
  have hstable : (prefixWord ++ tailWord_124425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124425).length < 2 ^ (prefixWord ++ tailWord_124425).sum := by decide
  have hdescent : baseEnd_124425 < baseStart_124425 := by decide
  rcases family_descends (prefixWord ++ tailWord_124425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124552 : List Nat := [2, 1, 3, 5, 1, 2, 1, 4]
def baseStart_124552 : Nat := 118140960795 + 124552 * 2 ^ 59
def prefixEnd_124552 : Nat := 4983230072969 + 3 ^ 40 * 124552 * 2
def baseEnd_124552 : Nat := 37899284431941880549453

theorem tailTrace_124552 : CollatzResearch.WordTrace tailWord_124552 prefixEnd_124552 37899284431941880549453 := by
  unfold tailWord_124552
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271392322388425316587955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3028523096517900422117273 2271392322388425316587955)
  ·
    refine ⟨3407088483582637974881933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271392322388425316587955 3407088483582637974881933)
    ·
      refine ⟨1277658181343489240580725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3407088483582637974881933 1277658181343489240580725)
      ·
        refine ⟨119780454500952116304443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1277658181343489240580725 119780454500952116304443)
        ·
          refine ⟨179670681751428174456665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119780454500952116304443 179670681751428174456665)
          ·
            refine ⟨134753011313571130842499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179670681751428174456665 134753011313571130842499)
            ·
              refine ⟨202129516970356696263749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134753011313571130842499 202129516970356696263749)
              ·
                refine ⟨37899284431941880549453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202129516970356696263749 37899284431941880549453)
                ·
                  rfl

theorem cell19_124552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_124552 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124552 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124552 prefixEnd_124552 := by exact prefixLift 124552
  have htrace : WordTrace (prefixWord ++ tailWord_124552) baseStart_124552 baseEnd_124552 := by
    simpa [prefixWord, tailWord_124552, baseEnd_124552] using wordTrace_append hprefix tailTrace_124552
  have hstable : (prefixWord ++ tailWord_124552).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124552).length < 2 ^ (prefixWord ++ tailWord_124552).sum := by decide
  have hdescent : baseEnd_124552 < baseStart_124552 := by decide
  rcases family_descends (prefixWord ++ tailWord_124552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124554 : List Nat := [3, 1, 2, 3, 2, 3, 1, 4]
def baseStart_124554 : Nat := 118140960795 + 124554 * 2 ^ 59
def prefixEnd_124554 : Nat := 4983230072969 + 3 ^ 40 * 124554 * 2
def baseEnd_124554 : Nat := 37899893001606468505003

theorem tailTrace_124554 : CollatzResearch.WordTrace tailWord_124554 prefixEnd_124554 37899893001606468505003 := by
  unfold tailWord_124554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135714397692401243687179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3028571727179736649832477 1135714397692401243687179)
  ·
    refine ⟨1703571596538601865530769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1135714397692401243687179 1703571596538601865530769)
    ·
      refine ⟨1277678697403951399148077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1703571596538601865530769 1277678697403951399148077)
      ·
        refine ⟨479129511526481774680529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1277678697403951399148077 479129511526481774680529)
        ·
          refine ⟨359347133644861331010397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479129511526481774680529 359347133644861331010397)
          ·
            refine ⟨134755175116822999128899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359347133644861331010397 134755175116822999128899)
            ·
              refine ⟨202132762675234498693349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134755175116822999128899 202132762675234498693349)
              ·
                refine ⟨37899893001606468505003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202132762675234498693349 37899893001606468505003)
                ·
                  rfl

theorem cell19_124554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_124554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124554 prefixEnd_124554 := by exact prefixLift 124554
  have htrace : WordTrace (prefixWord ++ tailWord_124554) baseStart_124554 baseEnd_124554 := by
    simpa [prefixWord, tailWord_124554, baseEnd_124554] using wordTrace_append hprefix tailTrace_124554
  have hstable : (prefixWord ++ tailWord_124554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124554).length < 2 ^ (prefixWord ++ tailWord_124554).sum := by decide
  have hdescent : baseEnd_124554 < baseStart_124554 := by decide
  rcases family_descends (prefixWord ++ tailWord_124554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124615 : List Nat := [1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_124615 : Nat := 118140960795 + 124615 * 2 ^ 59
def prefixEnd_124615 : Nat := 4983230072969 + 3 ^ 40 * 124615 * 2
def baseEnd_124615 : Nat := 37918454376376401149281

theorem tailTrace_124615 : CollatzResearch.WordTrace tailWord_124615 prefixEnd_124615 37918454376376401149281 := by
  unfold tailWord_124615
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545082443548612392719299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3030054962365741595146199 4545082443548612392719299)
  ·
    refine ⟨6817623665322918589078949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4545082443548612392719299 6817623665322918589078949)
    ·
      refine ⟨1278304437248047235452303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6817623665322918589078949 1278304437248047235452303)
      ·
        refine ⟨1917456655872070853178455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278304437248047235452303 1917456655872070853178455)
        ·
          refine ⟨2876184983808106279767683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917456655872070853178455 2876184983808106279767683)
          ·
            refine ⟨4314277475712159419651525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876184983808106279767683 4314277475712159419651525)
            ·
              refine ⟨808927026696029891184661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4314277475712159419651525 808927026696029891184661)
              ·
                refine ⟨37918454376376401149281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 808927026696029891184661 37918454376376401149281)
                ·
                  rfl

theorem cell19_124615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_124615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124615 prefixEnd_124615 := by exact prefixLift 124615
  have htrace : WordTrace (prefixWord ++ tailWord_124615) baseStart_124615 baseEnd_124615 := by
    simpa [prefixWord, tailWord_124615, baseEnd_124615] using wordTrace_append hprefix tailTrace_124615
  have hstable : (prefixWord ++ tailWord_124615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124615).length < 2 ^ (prefixWord ++ tailWord_124615).sum := by decide
  have hdescent : baseEnd_124615 < baseStart_124615 := by decide
  rcases family_descends (prefixWord ++ tailWord_124615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124628 : List Nat := [2, 4, 1, 3, 1, 3, 2, 3]
def baseStart_124628 : Nat := 118140960795 + 124628 * 2 ^ 59
def prefixEnd_124628 : Nat := 4983230072969 + 3 ^ 40 * 124628 * 2
def baseEnd_124628 : Nat := 37922410079196222860357

theorem tailTrace_124628 : CollatzResearch.WordTrace tailWord_124628 prefixEnd_124628 37922410079196222860357 := by
  unfold tailWord_124628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2272778296250757806471269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3030371061667677075295025 2272778296250757806471269)
  ·
    refine ⟨426145930547017088713363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2272778296250757806471269 426145930547017088713363)
    ·
      refine ⟨639218895820525633070045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426145930547017088713363 639218895820525633070045)
      ·
        refine ⟨239707085932697112401267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639218895820525633070045 239707085932697112401267)
        ·
          refine ⟨359560628899045668601901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239707085932697112401267 359560628899045668601901)
          ·
            refine ⟨134835235837142125725713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359560628899045668601901 134835235837142125725713)
            ·
              refine ⟨101126426877856594294285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134835235837142125725713 101126426877856594294285)
              ·
                refine ⟨37922410079196222860357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101126426877856594294285 37922410079196222860357)
                ·
                  rfl

theorem cell19_124628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_124628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124628 prefixEnd_124628 := by exact prefixLift 124628
  have htrace : WordTrace (prefixWord ++ tailWord_124628) baseStart_124628 baseEnd_124628 := by
    simpa [prefixWord, tailWord_124628, baseEnd_124628] using wordTrace_append hprefix tailTrace_124628
  have hstable : (prefixWord ++ tailWord_124628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124628).length < 2 ^ (prefixWord ++ tailWord_124628).sum := by decide
  have hdescent : baseEnd_124628 < baseStart_124628 := by decide
  rcases family_descends (prefixWord ++ tailWord_124628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124647 : List Nat := [1, 1, 5, 4, 2, 1, 5]
def baseStart_124647 : Nat := 118140960795 + 124647 * 2 ^ 59
def prefixEnd_124647 : Nat := 4983230072969 + 3 ^ 40 * 124647 * 2
def baseEnd_124647 : Nat := 12642730497003269479361

theorem tailTrace_124647 : CollatzResearch.WordTrace tailWord_124647 prefixEnd_124647 12642730497003269479361 := by
  unfold tailWord_124647
  simp only [CollatzResearch.WordTrace]
  refine ⟨4546249579432681857884195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3030833052955121238589463 4546249579432681857884195)
  ·
    refine ⟨6819374369149022786826293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4546249579432681857884195 6819374369149022786826293)
    ·
      refine ⟨639316347107720886264965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6819374369149022786826293 639316347107720886264965)
      ·
        refine ⟨119871815082697666174681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 639316347107720886264965 119871815082697666174681)
        ·
          refine ⟨89903861312023249631011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119871815082697666174681 89903861312023249631011)
          ·
            refine ⟨134855791968034874446517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89903861312023249631011 134855791968034874446517)
            ·
              refine ⟨12642730497003269479361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134855791968034874446517 12642730497003269479361)
              ·
                rfl

theorem cell19_124647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 5].length) (baseStart_124647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124647 prefixEnd_124647 := by exact prefixLift 124647
  have htrace : WordTrace (prefixWord ++ tailWord_124647) baseStart_124647 baseEnd_124647 := by
    simpa [prefixWord, tailWord_124647, baseEnd_124647] using wordTrace_append hprefix tailTrace_124647
  have hstable : (prefixWord ++ tailWord_124647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124647).length < 2 ^ (prefixWord ++ tailWord_124647).sum := by decide
  have hdescent : baseEnd_124647 < baseStart_124647 := by decide
  rcases family_descends (prefixWord ++ tailWord_124647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124725 : List Nat := [1, 3, 3, 1, 4, 2, 1, 4]
def baseStart_124725 : Nat := 118140960795 + 124725 * 2 ^ 59
def prefixEnd_124725 : Nat := 4983230072969 + 3 ^ 40 * 124725 * 2
def baseEnd_124725 : Nat := 37951925707928738704537

theorem tailTrace_124725 : CollatzResearch.WordTrace tailWord_124725 prefixEnd_124725 37951925707928738704537 := by
  unfold tailWord_124725
  simp only [CollatzResearch.WordTrace]
  refine ⟨4549094473150101179223629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3032729648766734119482419 4549094473150101179223629)
  ·
    refine ⟨1705910427431287942208861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4549094473150101179223629 1705910427431287942208861)
    ·
      refine ⟨639716410286732978328323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1705910427431287942208861 639716410286732978328323)
      ·
        refine ⟨959574615430099467492485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639716410286732978328323 959574615430099467492485)
        ·
          refine ⟨179920240393143650154841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 959574615430099467492485 179920240393143650154841)
          ·
            refine ⟨134940180294857737616131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179920240393143650154841 134940180294857737616131)
            ·
              refine ⟨202410270442286606424197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134940180294857737616131 202410270442286606424197)
              ·
                refine ⟨37951925707928738704537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202410270442286606424197 37951925707928738704537)
                ·
                  rfl

theorem cell19_124725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_124725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124725 prefixEnd_124725 := by exact prefixLift 124725
  have htrace : WordTrace (prefixWord ++ tailWord_124725) baseStart_124725 baseEnd_124725 := by
    simpa [prefixWord, tailWord_124725, baseEnd_124725] using wordTrace_append hprefix tailTrace_124725
  have hstable : (prefixWord ++ tailWord_124725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124725).length < 2 ^ (prefixWord ++ tailWord_124725).sum := by decide
  have hdescent : baseEnd_124725 < baseStart_124725 := by decide
  rcases family_descends (prefixWord ++ tailWord_124725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124746 : List Nat := [3, 1, 2, 1, 1, 1, 7, 3]
def baseStart_124746 : Nat := 118140960795 + 124746 * 2 ^ 59
def prefixEnd_124746 : Nat := 4983230072969 + 3 ^ 40 * 124746 * 2
def baseEnd_124746 : Nat := 37958315689406912237813

theorem tailTrace_124746 : CollatzResearch.WordTrace tailWord_124746 prefixEnd_124746 37958315689406912237813 := by
  unfold tailWord_124746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1137465101518505441434523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3033240270716014510492061 1137465101518505441434523)
  ·
    refine ⟨1706197652277758162151785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1137465101518505441434523 1706197652277758162151785)
    ·
      refine ⟨1279648239208318621613839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1706197652277758162151785 1279648239208318621613839)
      ·
        refine ⟨1919472358812477932420759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279648239208318621613839 1919472358812477932420759)
        ·
          refine ⟨2879208538218716898631139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919472358812477932420759 2879208538218716898631139)
          ·
            refine ⟨4318812807328075347946709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879208538218716898631139 4318812807328075347946709)
            ·
              refine ⟨101222175171751765967501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4318812807328075347946709 101222175171751765967501)
              ·
                refine ⟨37958315689406912237813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101222175171751765967501 37958315689406912237813)
                ·
                  rfl

theorem cell19_124746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_124746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124746 prefixEnd_124746 := by exact prefixLift 124746
  have htrace : WordTrace (prefixWord ++ tailWord_124746) baseStart_124746 baseEnd_124746 := by
    simpa [prefixWord, tailWord_124746, baseEnd_124746] using wordTrace_append hprefix tailTrace_124746
  have hstable : (prefixWord ++ tailWord_124746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124746).length < 2 ^ (prefixWord ++ tailWord_124746).sum := by decide
  have hdescent : baseEnd_124746 < baseStart_124746 := by decide
  rcases family_descends (prefixWord ++ tailWord_124746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124767 : List Nat := [1, 1, 2, 3, 1, 5, 6]
def baseStart_124767 : Nat := 118140960795 + 124767 * 2 ^ 59
def prefixEnd_124767 : Nat := 4983230072969 + 3 ^ 40 * 124767 * 2
def baseEnd_124767 : Nat := 12654901890295028590363

theorem tailTrace_124767 : CollatzResearch.WordTrace tailWord_124767 prefixEnd_124767 12654901890295028590363 := by
  unfold tailWord_124767
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550626338997942352252555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3033750892665294901501703 4550626338997942352252555)
  ·
    refine ⟨6825939508496913528378833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4550626338997942352252555 6825939508496913528378833)
    ·
      refine ⟨5119454631372685146284125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6825939508496913528378833 5119454631372685146284125)
      ·
        refine ⟨1919795486764756929856547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5119454631372685146284125 1919795486764756929856547)
        ·
          refine ⟨2879693230147135394784821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919795486764756929856547 2879693230147135394784821)
          ·
            refine ⟨269971240326293943261077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2879693230147135394784821 269971240326293943261077)
            ·
              refine ⟨12654901890295028590363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269971240326293943261077 12654901890295028590363)
              ·
                rfl

theorem cell19_124767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_124767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124767 prefixEnd_124767 := by exact prefixLift 124767
  have htrace : WordTrace (prefixWord ++ tailWord_124767) baseStart_124767 baseEnd_124767 := by
    simpa [prefixWord, tailWord_124767, baseEnd_124767] using wordTrace_append hprefix tailTrace_124767
  have hstable : (prefixWord ++ tailWord_124767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124767).length < 2 ^ (prefixWord ++ tailWord_124767).sum := by decide
  have hdescent : baseEnd_124767 < baseStart_124767 := by decide
  rcases family_descends (prefixWord ++ tailWord_124767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124786 : List Nat := [3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_124786 : Nat := 118140960795 + 124786 * 2 ^ 59
def prefixEnd_124786 : Nat := 4983230072969 + 3 ^ 40 * 124786 * 2
def baseEnd_124786 : Nat := 37970487082698671348815

theorem tailTrace_124786 : CollatzResearch.WordTrace tailWord_124786 prefixEnd_124786 37970487082698671348815 := by
  unfold tailWord_124786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1137829831482277149298553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3034212883952739064796141 1137829831482277149298553)
  ·
    refine ⟨853372373611707861973915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1137829831482277149298553 853372373611707861973915)
    ·
      refine ⟨1280058560417561792960873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 853372373611707861973915 1280058560417561792960873)
      ·
        refine ⟨960043920313171344720655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1280058560417561792960873 960043920313171344720655)
        ·
          refine ⟨1440065880469757017080983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960043920313171344720655 1440065880469757017080983)
          ·
            refine ⟨2160098820704635525621475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440065880469757017080983 2160098820704635525621475)
            ·
              refine ⟨3240148231056953288432213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160098820704635525621475 3240148231056953288432213)
              ·
                refine ⟨37970487082698671348815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3240148231056953288432213 37970487082698671348815)
                ·
                  rfl

theorem cell19_124786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_124786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124786 prefixEnd_124786 := by exact prefixLift 124786
  have htrace : WordTrace (prefixWord ++ tailWord_124786) baseStart_124786 baseEnd_124786 := by
    simpa [prefixWord, tailWord_124786, baseEnd_124786] using wordTrace_append hprefix tailTrace_124786
  have hstable : (prefixWord ++ tailWord_124786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124786).length < 2 ^ (prefixWord ++ tailWord_124786).sum := by decide
  have hdescent : baseEnd_124786 < baseStart_124786 := by decide
  rcases family_descends (prefixWord ++ tailWord_124786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124801 : List Nat := [1, 2, 4, 4, 1, 1, 1, 5]
def baseStart_124801 : Nat := 118140960795 + 124801 * 2 ^ 59
def prefixEnd_124801 : Nat := 4983230072969 + 3 ^ 40 * 124801 * 2
def baseEnd_124801 : Nat := 37975051355183081015441

theorem tailTrace_124801 : CollatzResearch.WordTrace tailWord_124801 prefixEnd_124801 37975051355183081015441 := by
  unfold tailWord_124801
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551866420874766158990257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3034577613916510772660171 4551866420874766158990257)
  ·
    refine ⟨3413899815656074619242693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4551866420874766158990257 3413899815656074619242693)
    ·
      refine ⟨640106215435513991108005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3413899815656074619242693 640106215435513991108005)
      ·
        refine ⟨120019915394158873332751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 640106215435513991108005 120019915394158873332751)
        ·
          refine ⟨180029873091238309999127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120019915394158873332751 180029873091238309999127)
          ·
            refine ⟨270044809636857464998691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180029873091238309999127 270044809636857464998691)
            ·
              refine ⟨405067214455286197498037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270044809636857464998691 405067214455286197498037)
              ·
                refine ⟨37975051355183081015441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405067214455286197498037 37975051355183081015441)
                ·
                  rfl

theorem cell19_124801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 5].length) (baseStart_124801 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124801 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124801 prefixEnd_124801 := by exact prefixLift 124801
  have htrace : WordTrace (prefixWord ++ tailWord_124801) baseStart_124801 baseEnd_124801 := by
    simpa [prefixWord, tailWord_124801, baseEnd_124801] using wordTrace_append hprefix tailTrace_124801
  have hstable : (prefixWord ++ tailWord_124801).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124801).length < 2 ^ (prefixWord ++ tailWord_124801).sum := by decide
  have hdescent : baseEnd_124801 < baseStart_124801 := by decide
  rcases family_descends (prefixWord ++ tailWord_124801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124803 : List Nat := [1, 1, 1, 3, 4, 2, 4, 3]
def baseStart_124803 : Nat := 118140960795 + 124803 * 2 ^ 59
def prefixEnd_124803 : Nat := 4983230072969 + 3 ^ 40 * 124803 * 2
def baseEnd_124803 : Nat := 37975659924847668970991

theorem tailTrace_124803 : CollatzResearch.WordTrace tailWord_124803 prefixEnd_124803 37975659924847668970991 := by
  unfold tailWord_124803
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551939366867520500563063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3034626244578347000375375 4551939366867520500563063)
  ·
    refine ⟨6827909050301280750844595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4551939366867520500563063 6827909050301280750844595)
    ·
      refine ⟨10241863575451921126266893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6827909050301280750844595 10241863575451921126266893)
      ·
        refine ⟨3840698840794470422350085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10241863575451921126266893 3840698840794470422350085)
        ·
          refine ⟨720131032648963204190641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3840698840794470422350085 720131032648963204190641)
          ·
            refine ⟨540098274486722403142981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720131032648963204190641 540098274486722403142981)
            ·
              refine ⟨101268426466260450589309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540098274486722403142981 101268426466260450589309)
              ·
                refine ⟨37975659924847668970991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101268426466260450589309 37975659924847668970991)
                ·
                  rfl

theorem cell19_124803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 3].length) (baseStart_124803 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124803 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124803 prefixEnd_124803 := by exact prefixLift 124803
  have htrace : WordTrace (prefixWord ++ tailWord_124803) baseStart_124803 baseEnd_124803 := by
    simpa [prefixWord, tailWord_124803, baseEnd_124803] using wordTrace_append hprefix tailTrace_124803
  have hstable : (prefixWord ++ tailWord_124803).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124803).length < 2 ^ (prefixWord ++ tailWord_124803).sum := by decide
  have hdescent : baseEnd_124803 < baseStart_124803 := by decide
  rcases family_descends (prefixWord ++ tailWord_124803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124805 : List Nat := [1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_124805 : Nat := 118140960795 + 124805 * 2 ^ 59
def prefixEnd_124805 : Nat := 4983230072969 + 3 ^ 40 * 124805 * 2
def baseEnd_124805 : Nat := 37976268494512256926541

theorem tailTrace_124805 : CollatzResearch.WordTrace tailWord_124805 prefixEnd_124805 37976268494512256926541 := by
  unfold tailWord_124805
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552012312860274842135869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3034674875240183228090579 4552012312860274842135869)
  ·
    refine ⟨1707004617322603065800951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4552012312860274842135869 1707004617322603065800951)
    ·
      refine ⟨2560506925983904598701427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1707004617322603065800951 2560506925983904598701427)
      ·
        refine ⟨3840760388975856898052141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2560506925983904598701427 3840760388975856898052141)
        ·
          refine ⟨1440285145865946336769553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3840760388975856898052141 1440285145865946336769553)
          ·
            refine ⟨1080213859399459752577165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1440285145865946336769553 1080213859399459752577165)
            ·
              refine ⟨405080197274797407216437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1080213859399459752577165 405080197274797407216437)
              ·
                refine ⟨37976268494512256926541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405080197274797407216437 37976268494512256926541)
                ·
                  rfl

theorem cell19_124805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_124805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124805 prefixEnd_124805 := by exact prefixLift 124805
  have htrace : WordTrace (prefixWord ++ tailWord_124805) baseStart_124805 baseEnd_124805 := by
    simpa [prefixWord, tailWord_124805, baseEnd_124805] using wordTrace_append hprefix tailTrace_124805
  have hstable : (prefixWord ++ tailWord_124805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124805).length < 2 ^ (prefixWord ++ tailWord_124805).sum := by decide
  have hdescent : baseEnd_124805 < baseStart_124805 := by decide
  rcases family_descends (prefixWord ++ tailWord_124805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124892 : List Nat := [2, 2, 6, 1, 1, 2, 1, 4]
def baseStart_124892 : Nat := 118140960795 + 124892 * 2 ^ 59
def prefixEnd_124892 : Nat := 4983230072969 + 3 ^ 40 * 124892 * 2
def baseEnd_124892 : Nat := 38002741274921832992971

theorem tailTrace_124892 : CollatzResearch.WordTrace tailWord_124892 prefixEnd_124892 38002741274921832992971 := by
  unfold tailWord_124892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277592731772544350276465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3036790309030059133701953 2277592731772544350276465)
  ·
    refine ⟨1708194548829408262707349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2277592731772544350276465 1708194548829408262707349)
    ·
      refine ⟨80071619476378512314407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1708194548829408262707349 80071619476378512314407)
      ·
        refine ⟨120107429214567768471611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80071619476378512314407 120107429214567768471611)
        ·
          refine ⟨180161143821851652707417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120107429214567768471611 180161143821851652707417)
          ·
            refine ⟨135120857866388739530563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180161143821851652707417 135120857866388739530563)
            ·
              refine ⟨202681286799583109295845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135120857866388739530563 202681286799583109295845)
              ·
                refine ⟨38002741274921832992971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202681286799583109295845 38002741274921832992971)
                ·
                  rfl

theorem cell19_124892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_124892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124892 prefixEnd_124892 := by exact prefixLift 124892
  have htrace : WordTrace (prefixWord ++ tailWord_124892) baseStart_124892 baseEnd_124892 := by
    simpa [prefixWord, tailWord_124892, baseEnd_124892] using wordTrace_append hprefix tailTrace_124892
  have hstable : (prefixWord ++ tailWord_124892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124892).length < 2 ^ (prefixWord ++ tailWord_124892).sum := by decide
  have hdescent : baseEnd_124892 < baseStart_124892 := by decide
  rcases family_descends (prefixWord ++ tailWord_124892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124968 : List Nat := [2, 1, 5, 3, 2, 1, 2, 3]
def baseStart_124968 : Nat := 118140960795 + 124968 * 2 ^ 59
def prefixEnd_124968 : Nat := 4983230072969 + 3 ^ 40 * 124968 * 2
def baseEnd_124968 : Nat := 38025866922176175303875

theorem tailTrace_124968 : CollatzResearch.WordTrace tailWord_124968 prefixEnd_124968 38025866922176175303875 := by
  unfold tailWord_124968
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278978705634876840159779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3038638274179835786879705 2278978705634876840159779)
  ·
    refine ⟨3418468058452315260239669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2278978705634876840159779 3418468058452315260239669)
    ·
      refine ⟨320481380479904555647469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3418468058452315260239669 320481380479904555647469)
      ·
        refine ⟨120180517679964208367801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320481380479904555647469 120180517679964208367801)
        ·
          refine ⟨90135388259973156275851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120180517679964208367801 90135388259973156275851)
          ·
            refine ⟨135203082389959734413777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90135388259973156275851 135203082389959734413777)
            ·
              refine ⟨101402311792469800810333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135203082389959734413777 101402311792469800810333)
              ·
                refine ⟨38025866922176175303875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101402311792469800810333 38025866922176175303875)
                ·
                  rfl

theorem cell19_124968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_124968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124968 prefixEnd_124968 := by exact prefixLift 124968
  have htrace : WordTrace (prefixWord ++ tailWord_124968) baseStart_124968 baseEnd_124968 := by
    simpa [prefixWord, tailWord_124968, baseEnd_124968] using wordTrace_append hprefix tailTrace_124968
  have hstable : (prefixWord ++ tailWord_124968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124968).length < 2 ^ (prefixWord ++ tailWord_124968).sum := by decide
  have hdescent : baseEnd_124968 < baseStart_124968 := by decide
  rcases family_descends (prefixWord ++ tailWord_124968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124974 : List Nat := [4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_124974 : Nat := 118140960795 + 124974 * 2 ^ 59
def prefixEnd_124974 : Nat := 4983230072969 + 3 ^ 40 * 124974 * 2
def baseEnd_124974 : Nat := 38027692631169939170525

theorem tailTrace_124974 : CollatzResearch.WordTrace tailWord_124974 prefixEnd_124974 38027692631169939170525 := by
  unfold tailWord_124974
  simp only [CollatzResearch.WordTrace]
  refine ⟨569772031156002088129747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3038784166165344470025317 569772031156002088129747)
  ·
    refine ⟨854658046734003132194621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 569772031156002088129747 854658046734003132194621)
    ·
      refine ⟨320496767525251174572983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 854658046734003132194621 320496767525251174572983)
      ·
        refine ⟨480745151287876761859475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320496767525251174572983 480745151287876761859475)
        ·
          refine ⟨721117726931815142789213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480745151287876761859475 721117726931815142789213)
          ·
            refine ⟨270419147599430678545955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 721117726931815142789213 270419147599430678545955)
            ·
              refine ⟨405628721399146017818933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270419147599430678545955 405628721399146017818933)
              ·
                refine ⟨38027692631169939170525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405628721399146017818933 38027692631169939170525)
                ·
                  rfl

theorem cell19_124974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_124974 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124974 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124974 prefixEnd_124974 := by exact prefixLift 124974
  have htrace : WordTrace (prefixWord ++ tailWord_124974) baseStart_124974 baseEnd_124974 := by
    simpa [prefixWord, tailWord_124974, baseEnd_124974] using wordTrace_append hprefix tailTrace_124974
  have hstable : (prefixWord ++ tailWord_124974).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124974).length < 2 ^ (prefixWord ++ tailWord_124974).sum := by decide
  have hdescent : baseEnd_124974 < baseStart_124974 := by decide
  rcases family_descends (prefixWord ++ tailWord_124974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124976 : List Nat := [2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_124976 : Nat := 118140960795 + 124976 * 2 ^ 59
def prefixEnd_124976 : Nat := 4983230072969 + 3 ^ 40 * 124976 * 2
def baseEnd_124976 : Nat := 38028301200834527126075

theorem tailTrace_124976 : CollatzResearch.WordTrace tailWord_124976 prefixEnd_124976 38028301200834527126075 := by
  unfold tailWord_124976
  simp only [CollatzResearch.WordTrace]
  refine ⟨2279124597620385523305391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3038832796827180697740521 2279124597620385523305391)
  ·
    refine ⟨3418686896430578284958087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2279124597620385523305391 3418686896430578284958087)
    ·
      refine ⟨5128030344645867427437131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3418686896430578284958087 5128030344645867427437131)
      ·
        refine ⟨7692045516968801141155697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5128030344645867427437131 7692045516968801141155697)
        ·
          refine ⟨5769034137726600855866773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7692045516968801141155697 5769034137726600855866773)
          ·
            refine ⟨270423475205934415118755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5769034137726600855866773 270423475205934415118755)
            ·
              refine ⟨405635212808901622678133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270423475205934415118755 405635212808901622678133)
              ·
                refine ⟨38028301200834527126075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405635212808901622678133 38028301200834527126075)
                ·
                  rfl

theorem cell19_124976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_124976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124976 prefixEnd_124976 := by exact prefixLift 124976
  have htrace : WordTrace (prefixWord ++ tailWord_124976) baseStart_124976 baseEnd_124976 := by
    simpa [prefixWord, tailWord_124976, baseEnd_124976] using wordTrace_append hprefix tailTrace_124976
  have hstable : (prefixWord ++ tailWord_124976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124976).length < 2 ^ (prefixWord ++ tailWord_124976).sum := by decide
  have hdescent : baseEnd_124976 < baseStart_124976 := by decide
  rcases family_descends (prefixWord ++ tailWord_124976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124993 : List Nat := [1, 2, 5, 1, 2, 3, 5]
def baseStart_124993 : Nat := 118140960795 + 124993 * 2 ^ 59
def prefixEnd_124993 : Nat := 4983230072969 + 3 ^ 40 * 124993 * 2
def baseEnd_124993 : Nat := 12677824680994508249417

theorem tailTrace_124993 : CollatzResearch.WordTrace tailWord_124993 prefixEnd_124993 12677824680994508249417 := by
  unfold tailWord_124993
  simp only [CollatzResearch.WordTrace]
  refine ⟨4558869236179182949979633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3039246157452788633319755 4558869236179182949979633)
  ·
    refine ⟨3419151927134387212484725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4558869236179182949979633 3419151927134387212484725)
    ·
      refine ⟨320545493168848801170443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3419151927134387212484725 320545493168848801170443)
      ·
        refine ⟨480818239753273201755665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320545493168848801170443 480818239753273201755665)
        ·
          refine ⟨360613679814954901316749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480818239753273201755665 360613679814954901316749)
          ·
            refine ⟨135230129930608087993781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360613679814954901316749 135230129930608087993781)
            ·
              refine ⟨12677824680994508249417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135230129930608087993781 12677824680994508249417)
              ·
                rfl

theorem cell19_124993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_124993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_124993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_124993 prefixEnd_124993 := by exact prefixLift 124993
  have htrace : WordTrace (prefixWord ++ tailWord_124993) baseStart_124993 baseEnd_124993 := by
    simpa [prefixWord, tailWord_124993, baseEnd_124993] using wordTrace_append hprefix tailTrace_124993
  have hstable : (prefixWord ++ tailWord_124993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124993).length < 2 ^ (prefixWord ++ tailWord_124993).sum := by decide
  have hdescent : baseEnd_124993 < baseStart_124993 := by decide
  rcases family_descends (prefixWord ++ tailWord_124993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125088 : List Nat := [2, 1, 1, 4, 2, 3, 3, 3]
def baseStart_125088 : Nat := 118140960795 + 125088 * 2 ^ 59
def prefixEnd_125088 : Nat := 4983230072969 + 3 ^ 40 * 125088 * 2
def baseEnd_125088 : Nat := 38062381102051452636881

theorem tailTrace_125088 : CollatzResearch.WordTrace tailWord_125088 prefixEnd_125088 38062381102051452636881 := by
  unfold tailWord_125088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281167085417507087343959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3041556113890009449791945 2281167085417507087343959)
  ·
    refine ⟨3421750628126260631015939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2281167085417507087343959 3421750628126260631015939)
    ·
      refine ⟨5132625942189390946523909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421750628126260631015939 5132625942189390946523909)
      ·
        refine ⟨962367364160510802473233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5132625942189390946523909 962367364160510802473233)
        ·
          refine ⟨721775523120383101854925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962367364160510802473233 721775523120383101854925)
          ·
            refine ⟨270665821170143663195597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 721775523120383101854925 270665821170143663195597)
            ·
              refine ⟨101499682938803873698349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270665821170143663195597 101499682938803873698349)
              ·
                refine ⟨38062381102051452636881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101499682938803873698349 38062381102051452636881)
                ·
                  rfl

theorem cell19_125088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_125088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125088 prefixEnd_125088 := by exact prefixLift 125088
  have htrace : WordTrace (prefixWord ++ tailWord_125088) baseStart_125088 baseEnd_125088 := by
    simpa [prefixWord, tailWord_125088, baseEnd_125088] using wordTrace_append hprefix tailTrace_125088
  have hstable : (prefixWord ++ tailWord_125088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125088).length < 2 ^ (prefixWord ++ tailWord_125088).sum := by decide
  have hdescent : baseEnd_125088 < baseStart_125088 := by decide
  rcases family_descends (prefixWord ++ tailWord_125088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125141 : List Nat := [1, 3, 2, 4, 3, 1, 2, 3]
def baseStart_125141 : Nat := 118140960795 + 125141 * 2 ^ 59
def prefixEnd_125141 : Nat := 4983230072969 + 3 ^ 40 * 125141 * 2
def baseEnd_125141 : Nat := 38078508198163033458959

theorem tailTrace_125141 : CollatzResearch.WordTrace tailWord_125141 prefixEnd_125141 38078508198163033458959 := by
  unfold tailWord_125141
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564267239643004226367277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3042844826428669484244851 4564267239643004226367277)
  ·
    refine ⟨1711600214866126584887729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4564267239643004226367277 1711600214866126584887729)
    ·
      refine ⟨1283700161149594938665797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1711600214866126584887729 1283700161149594938665797)
      ·
        refine ⟨240693780215549050999837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1283700161149594938665797 240693780215549050999837)
        ·
          refine ⟨90260167580830894124939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240693780215549050999837 90260167580830894124939)
          ·
            refine ⟨135390251371246341187409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90260167580830894124939 135390251371246341187409)
            ·
              refine ⟨101542688528434755890557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135390251371246341187409 101542688528434755890557)
              ·
                refine ⟨38078508198163033458959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101542688528434755890557 38078508198163033458959)
                ·
                  rfl

theorem cell19_125141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 3].length) (baseStart_125141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125141 prefixEnd_125141 := by exact prefixLift 125141
  have htrace : WordTrace (prefixWord ++ tailWord_125141) baseStart_125141 baseEnd_125141 := by
    simpa [prefixWord, tailWord_125141, baseEnd_125141] using wordTrace_append hprefix tailTrace_125141
  have hstable : (prefixWord ++ tailWord_125141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125141).length < 2 ^ (prefixWord ++ tailWord_125141).sum := by decide
  have hdescent : baseEnd_125141 < baseStart_125141 := by decide
  rcases family_descends (prefixWord ++ tailWord_125141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125185 : List Nat := [1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_125185 : Nat := 118140960795 + 125185 * 2 ^ 59
def prefixEnd_125185 : Nat := 4983230072969 + 3 ^ 40 * 125185 * 2
def baseEnd_125185 : Nat := 38091896730783968481061

theorem tailTrace_125185 : CollatzResearch.WordTrace tailWord_125185 prefixEnd_125185 38091896730783968481061 := by
  unfold tailWord_125185
  simp only [CollatzResearch.WordTrace]
  refine ⟨4565872051483599740969009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3043914700989066493979339 4565872051483599740969009)
  ·
    refine ⟨3424404038612699805726757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4565872051483599740969009 3424404038612699805726757)
    ·
      refine ⟨642075757239881213573767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3424404038612699805726757 642075757239881213573767)
      ·
        refine ⟨963113635859821820360651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642075757239881213573767 963113635859821820360651)
        ·
          refine ⟨1444670453789732730540977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963113635859821820360651 1444670453789732730540977)
          ·
            refine ⟨1083502840342299547905733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1444670453789732730540977 1083502840342299547905733)
            ·
              refine ⟨203156782564181165232325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1083502840342299547905733 203156782564181165232325)
              ·
                refine ⟨38091896730783968481061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203156782564181165232325 38091896730783968481061)
                ·
                  rfl

theorem cell19_125185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_125185 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125185 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125185 prefixEnd_125185 := by exact prefixLift 125185
  have htrace : WordTrace (prefixWord ++ tailWord_125185) baseStart_125185 baseEnd_125185 := by
    simpa [prefixWord, tailWord_125185, baseEnd_125185] using wordTrace_append hprefix tailTrace_125185
  have hstable : (prefixWord ++ tailWord_125185).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125185).length < 2 ^ (prefixWord ++ tailWord_125185).sum := by decide
  have hdescent : baseEnd_125185 < baseStart_125185 := by decide
  rcases family_descends (prefixWord ++ tailWord_125185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125242 : List Nat := [3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_125242 : Nat := 118140960795 + 125242 * 2 ^ 59
def prefixEnd_125242 : Nat := 4983230072969 + 3 ^ 40 * 125242 * 2
def baseEnd_125242 : Nat := 38109240966224725214239

theorem tailTrace_125242 : CollatzResearch.WordTrace tailWord_125242 prefixEnd_125242 38109240966224725214239 := by
  unfold tailWord_125242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1141987753069274618948495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3045300674851398983862653 1141987753069274618948495)
  ·
    refine ⟨1712981629603911928422743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1141987753069274618948495 1712981629603911928422743)
    ·
      refine ⟨2569472444405867892634115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1712981629603911928422743 2569472444405867892634115)
      ·
        refine ⟨3854208666608801838951173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569472444405867892634115 3854208666608801838951173)
        ·
          refine ⟨722664124989150344803345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3854208666608801838951173 722664124989150344803345)
          ·
            refine ⟨541998093741862758602509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722664124989150344803345 541998093741862758602509)
            ·
              refine ⟨203249285153198534475941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541998093741862758602509 203249285153198534475941)
              ·
                refine ⟨38109240966224725214239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203249285153198534475941 38109240966224725214239)
                ·
                  rfl

theorem cell19_125242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_125242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125242 prefixEnd_125242 := by exact prefixLift 125242
  have htrace : WordTrace (prefixWord ++ tailWord_125242) baseStart_125242 baseEnd_125242 := by
    simpa [prefixWord, tailWord_125242, baseEnd_125242] using wordTrace_append hprefix tailTrace_125242
  have hstable : (prefixWord ++ tailWord_125242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125242).length < 2 ^ (prefixWord ++ tailWord_125242).sum := by decide
  have hdescent : baseEnd_125242 < baseStart_125242 := by decide
  rcases family_descends (prefixWord ++ tailWord_125242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125280 : List Nat := [2, 1, 1, 3, 5, 1, 6]
def baseStart_125280 : Nat := 118140960795 + 125280 * 2 ^ 59
def prefixEnd_125280 : Nat := 4983230072969 + 3 ^ 40 * 125280 * 2
def baseEnd_125280 : Nat := 12706934596617298789897

theorem tailTrace_125280 : CollatzResearch.WordTrace tailWord_125280 prefixEnd_125280 12706934596617298789897 := by
  unfold tailWord_125280
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284668493069715482838647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3046224657426287310451529 2284668493069715482838647)
  ·
    refine ⟨3427002739604573224257971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2284668493069715482838647 3427002739604573224257971)
    ·
      refine ⟨5140504109406859836386957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427002739604573224257971 5140504109406859836386957)
      ·
        refine ⟨1927689041027572438645109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5140504109406859836386957 1927689041027572438645109)
        ·
          refine ⟨180720847596334916122979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1927689041027572438645109 180720847596334916122979)
          ·
            refine ⟨271081271394502374184469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180720847596334916122979 271081271394502374184469)
            ·
              refine ⟨12706934596617298789897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271081271394502374184469 12706934596617298789897)
              ·
                rfl

theorem cell19_125280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_125280 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125280 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125280 prefixEnd_125280 := by exact prefixLift 125280
  have htrace : WordTrace (prefixWord ++ tailWord_125280) baseStart_125280 baseEnd_125280 := by
    simpa [prefixWord, tailWord_125280, baseEnd_125280] using wordTrace_append hprefix tailTrace_125280
  have hstable : (prefixWord ++ tailWord_125280).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125280).length < 2 ^ (prefixWord ++ tailWord_125280).sum := by decide
  have hdescent : baseEnd_125280 < baseStart_125280 := by decide
  rcases family_descends (prefixWord ++ tailWord_125280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125314 : List Nat := [3, 4, 2, 1, 2, 1, 1, 5]
def baseStart_125314 : Nat := 118140960795 + 125314 * 2 ^ 59
def prefixEnd_125314 : Nat := 4983230072969 + 3 ^ 40 * 125314 * 2
def baseEnd_125314 : Nat := 38131149474149891614043

theorem tailTrace_125314 : CollatzResearch.WordTrace tailWord_125314 prefixEnd_125314 38131149474149891614043 := by
  unfold tailWord_125314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142644267004063693103749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3047051378677503181609997 1142644267004063693103749)
  ·
    refine ⟨214245800063261942456953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1142644267004063693103749 214245800063261942456953)
    ·
      refine ⟨160684350047446456842715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214245800063261942456953 160684350047446456842715)
      ·
        refine ⟨241026525071169685264073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160684350047446456842715 241026525071169685264073)
        ·
          refine ⟨180769893803377263948055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241026525071169685264073 180769893803377263948055)
          ·
            refine ⟨271154840705065895922083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180769893803377263948055 271154840705065895922083)
            ·
              refine ⟨406732261057598843883125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271154840705065895922083 406732261057598843883125)
              ·
                refine ⟨38131149474149891614043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 406732261057598843883125 38131149474149891614043)
                ·
                  rfl

theorem cell19_125314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_125314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125314 prefixEnd_125314 := by exact prefixLift 125314
  have htrace : WordTrace (prefixWord ++ tailWord_125314) baseStart_125314 baseEnd_125314 := by
    simpa [prefixWord, tailWord_125314, baseEnd_125314] using wordTrace_append hprefix tailTrace_125314
  have hstable : (prefixWord ++ tailWord_125314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125314).length < 2 ^ (prefixWord ++ tailWord_125314).sum := by decide
  have hdescent : baseEnd_125314 < baseStart_125314 := by decide
  rcases family_descends (prefixWord ++ tailWord_125314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125394 : List Nat := [3, 2, 2, 4, 8]
def baseStart_125394 : Nat := 118140960795 + 125394 * 2 ^ 59
def prefixEnd_125394 : Nat := 4983230072969 + 3 ^ 40 * 125394 * 2
def baseEnd_125394 : Nat := 1413166380027163327261

theorem tailTrace_125394 : CollatzResearch.WordTrace tailWord_125394 prefixEnd_125394 1413166380027163327261 := by
  unfold tailWord_125394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1143373726931607108831809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3048996605150952290218157 1143373726931607108831809)
  ·
    refine ⟨857530295198705331623857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1143373726931607108831809 857530295198705331623857)
    ·
      refine ⟨643147721399028998717893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 857530295198705331623857 643147721399028998717893)
      ·
        refine ⟨120590197762317937259605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 643147721399028998717893 120590197762317937259605)
        ·
          refine ⟨1413166380027163327261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 120590197762317937259605 1413166380027163327261)
          ·
            rfl

theorem cell19_125394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 8].length) (baseStart_125394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125394 prefixEnd_125394 := by exact prefixLift 125394
  have htrace : WordTrace (prefixWord ++ tailWord_125394) baseStart_125394 baseEnd_125394 := by
    simpa [prefixWord, tailWord_125394, baseEnd_125394] using wordTrace_append hprefix tailTrace_125394
  have hstable : (prefixWord ++ tailWord_125394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125394).length < 2 ^ (prefixWord ++ tailWord_125394).sum := by decide
  have hdescent : baseEnd_125394 < baseStart_125394 := by decide
  rcases family_descends (prefixWord ++ tailWord_125394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125411 : List Nat := [1, 1, 1, 6, 3, 2, 1, 4]
def baseStart_125411 : Nat := 118140960795 + 125411 * 2 ^ 59
def prefixEnd_125411 : Nat := 4983230072969 + 3 ^ 40 * 125411 * 2
def baseEnd_125411 : Nat := 38160665102882407458223

theorem tailTrace_125411 : CollatzResearch.WordTrace tailWord_125411 prefixEnd_125411 38160665102882407458223 := by
  unfold tailWord_125411
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574114948664840338696087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3049409965776560225797391 4574114948664840338696087)
  ·
    refine ⟨6861172422997260508044131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4574114948664840338696087 6861172422997260508044131)
    ·
      refine ⟨10291758634495890762066197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6861172422997260508044131 10291758634495890762066197)
      ·
        refine ⟨482426185991994879471853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10291758634495890762066197 482426185991994879471853)
        ·
          refine ⟨180909819746998079801945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482426185991994879471853 180909819746998079801945)
          ·
            refine ⟨135682364810248559851459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180909819746998079801945 135682364810248559851459)
            ·
              refine ⟨203523547215372839777189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135682364810248559851459 203523547215372839777189)
              ·
                refine ⟨38160665102882407458223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203523547215372839777189 38160665102882407458223)
                ·
                  rfl

theorem cell19_125411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_125411 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125411 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125411 prefixEnd_125411 := by exact prefixLift 125411
  have htrace : WordTrace (prefixWord ++ tailWord_125411) baseStart_125411 baseEnd_125411 := by
    simpa [prefixWord, tailWord_125411, baseEnd_125411] using wordTrace_append hprefix tailTrace_125411
  have hstable : (prefixWord ++ tailWord_125411).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125411).length < 2 ^ (prefixWord ++ tailWord_125411).sum := by decide
  have hdescent : baseEnd_125411 < baseStart_125411 := by decide
  rcases family_descends (prefixWord ++ tailWord_125411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125430 : List Nat := [5, 1, 1, 1, 2, 1, 5, 3]
def baseStart_125430 : Nat := 118140960795 + 125430 * 2 ^ 59
def prefixEnd_125430 : Nat := 4983230072969 + 3 ^ 40 * 125430 * 2
def baseEnd_125430 : Nat := 38166446514695993035949

theorem tailTrace_125430 : CollatzResearch.WordTrace tailWord_125430 prefixEnd_125430 38166446514695993035949 := by
  unfold tailWord_125430
  simp only [CollatzResearch.WordTrace]
  refine ⟨285925495974750411477359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3049871957064004389091829 285925495974750411477359)
  ·
    refine ⟨428888243962125617216039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285925495974750411477359 428888243962125617216039)
    ·
      refine ⟨643332365943188425824059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428888243962125617216039 643332365943188425824059)
      ·
        refine ⟨964998548914782638736089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643332365943188425824059 964998548914782638736089)
        ·
          refine ⟨723748911686086979052067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964998548914782638736089 723748911686086979052067)
          ·
            refine ⟨1085623367529130468578101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723748911686086979052067 1085623367529130468578101)
            ·
              refine ⟨101777190705855981429197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1085623367529130468578101 101777190705855981429197)
              ·
                refine ⟨38166446514695993035949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101777190705855981429197 38166446514695993035949)
                ·
                  rfl

theorem cell19_125430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_125430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125430 prefixEnd_125430 := by exact prefixLift 125430
  have htrace : WordTrace (prefixWord ++ tailWord_125430) baseStart_125430 baseEnd_125430 := by
    simpa [prefixWord, tailWord_125430, baseEnd_125430] using wordTrace_append hprefix tailTrace_125430
  have hstable : (prefixWord ++ tailWord_125430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125430).length < 2 ^ (prefixWord ++ tailWord_125430).sum := by decide
  have hdescent : baseEnd_125430 < baseStart_125430 := by decide
  rcases family_descends (prefixWord ++ tailWord_125430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125432 : List Nat := [2, 1, 2, 1, 1, 4, 5, 3]
def baseStart_125432 : Nat := 118140960795 + 125432 * 2 ^ 59
def prefixEnd_125432 : Nat := 4983230072969 + 3 ^ 40 * 125432 * 2
def baseEnd_125432 : Nat := 38167055084360580991499

theorem tailTrace_125432 : CollatzResearch.WordTrace tailWord_125432 prefixEnd_125432 38167055084360580991499 := by
  unfold tailWord_125432
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287440440794380462605275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3049920587725840616807033 2287440440794380462605275)
  ·
    refine ⟨3431160661191570693907913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287440440794380462605275 3431160661191570693907913)
    ·
      refine ⟨2573370495893678020430935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3431160661191570693907913 2573370495893678020430935)
      ·
        refine ⟨3860055743840517030646403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2573370495893678020430935 3860055743840517030646403)
        ·
          refine ⟨5790083615760775545969605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860055743840517030646403 5790083615760775545969605)
          ·
            refine ⟨1085640677955145414869301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5790083615760775545969605 1085640677955145414869301)
            ·
              refine ⟨101778813558294882643997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1085640677955145414869301 101778813558294882643997)
              ·
                refine ⟨38167055084360580991499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101778813558294882643997 38167055084360580991499)
                ·
                  rfl

theorem cell19_125432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_125432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125432 prefixEnd_125432 := by exact prefixLift 125432
  have htrace : WordTrace (prefixWord ++ tailWord_125432) baseStart_125432 baseEnd_125432 := by
    simpa [prefixWord, tailWord_125432, baseEnd_125432] using wordTrace_append hprefix tailTrace_125432
  have hstable : (prefixWord ++ tailWord_125432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125432).length < 2 ^ (prefixWord ++ tailWord_125432).sum := by decide
  have hdescent : baseEnd_125432 < baseStart_125432 := by decide
  rcases family_descends (prefixWord ++ tailWord_125432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125489 : List Nat := [1, 2, 2, 3, 1, 1, 6, 3]
def baseStart_125489 : Nat := 118140960795 + 125489 * 2 ^ 59
def prefixEnd_125489 : Nat := 4983230072969 + 3 ^ 40 * 125489 * 2
def baseEnd_125489 : Nat := 38184399319801337724677

theorem tailTrace_125489 : CollatzResearch.WordTrace tailWord_125489 prefixEnd_125489 38184399319801337724677 := by
  unfold tailWord_125489
  simp only [CollatzResearch.WordTrace]
  refine ⟨4576959842382259660035521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3051306561588173106690347 4576959842382259660035521)
  ·
    refine ⟨3432719881786694745026641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4576959842382259660035521 3432719881786694745026641)
    ·
      refine ⟨2574539911340021058769981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3432719881786694745026641 2574539911340021058769981)
      ·
        refine ⟨965452466752507897038743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2574539911340021058769981 965452466752507897038743)
        ·
          refine ⟨1448178700128761845558115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965452466752507897038743 1448178700128761845558115)
          ·
            refine ⟨2172268050193142768337173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448178700128761845558115 2172268050193142768337173)
            ·
              refine ⟨101825064852803567265805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2172268050193142768337173 101825064852803567265805)
              ·
                refine ⟨38184399319801337724677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101825064852803567265805 38184399319801337724677)
                ·
                  rfl

theorem cell19_125489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 3].length) (baseStart_125489 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125489 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125489 prefixEnd_125489 := by exact prefixLift 125489
  have htrace : WordTrace (prefixWord ++ tailWord_125489) baseStart_125489 baseEnd_125489 := by
    simpa [prefixWord, tailWord_125489, baseEnd_125489] using wordTrace_append hprefix tailTrace_125489
  have hstable : (prefixWord ++ tailWord_125489).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125489).length < 2 ^ (prefixWord ++ tailWord_125489).sum := by decide
  have hdescent : baseEnd_125489 < baseStart_125489 := by decide
  rcases family_descends (prefixWord ++ tailWord_125489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125491 : List Nat := [1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_125491 : Nat := 118140960795 + 125491 * 2 ^ 59
def prefixEnd_125491 : Nat := 4983230072969 + 3 ^ 40 * 125491 * 2
def baseEnd_125491 : Nat := 38185007889465925680227

theorem tailTrace_125491 : CollatzResearch.WordTrace tailWord_125491 prefixEnd_125491 38185007889465925680227 := by
  unfold tailWord_125491
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577032788375014001608327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3051355192250009334405551 4577032788375014001608327)
  ·
    refine ⟨6865549182562521002412491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4577032788375014001608327 6865549182562521002412491)
    ·
      refine ⟨10298323773843781503618737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6865549182562521002412491 10298323773843781503618737)
      ·
        refine ⟨7723742830382836127714053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10298323773843781503618737 7723742830382836127714053)
        ·
          refine ⟨1448201780696781773946385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7723742830382836127714053 1448201780696781773946385)
          ·
            refine ⟨1086151335522586330459789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448201780696781773946385 1086151335522586330459789)
            ·
              refine ⟨407306750820969873922421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1086151335522586330459789 407306750820969873922421)
              ·
                refine ⟨38185007889465925680227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 407306750820969873922421 38185007889465925680227)
                ·
                  rfl

theorem cell19_125491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_125491 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125491 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125491 prefixEnd_125491 := by exact prefixLift 125491
  have htrace : WordTrace (prefixWord ++ tailWord_125491) baseStart_125491 baseEnd_125491 := by
    simpa [prefixWord, tailWord_125491, baseEnd_125491] using wordTrace_append hprefix tailTrace_125491
  have hstable : (prefixWord ++ tailWord_125491).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125491).length < 2 ^ (prefixWord ++ tailWord_125491).sum := by decide
  have hdescent : baseEnd_125491 < baseStart_125491 := by decide
  rcases family_descends (prefixWord ++ tailWord_125491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125548 : List Nat := [2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_125548 : Nat := 118140960795 + 125548 * 2 ^ 59
def prefixEnd_125548 : Nat := 4983230072969 + 3 ^ 40 * 125548 * 2
def baseEnd_125548 : Nat := 38202352124906682413405

theorem tailTrace_125548 : CollatzResearch.WordTrace tailWord_125548 prefixEnd_125548 38202352124906682413405 := by
  unfold tailWord_125548
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289555874584256368216649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3052741166112341824288865 2289555874584256368216649)
  ·
    refine ⟨1717166905938192276162487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2289555874584256368216649 1717166905938192276162487)
    ·
      refine ⟨2575750358907288414243731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717166905938192276162487 2575750358907288414243731)
      ·
        refine ⟨3863625538360932621365597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575750358907288414243731 3863625538360932621365597)
        ·
          refine ⟨1448859576885349733012099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3863625538360932621365597 1448859576885349733012099)
          ·
            refine ⟨2173289365328024599518149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448859576885349733012099 2173289365328024599518149)
            ·
              refine ⟨407491755999004612409653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2173289365328024599518149 407491755999004612409653)
              ·
                refine ⟨38202352124906682413405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 407491755999004612409653 38202352124906682413405)
                ·
                  rfl

theorem cell19_125548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_125548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125548 prefixEnd_125548 := by exact prefixLift 125548
  have htrace : WordTrace (prefixWord ++ tailWord_125548) baseStart_125548 baseEnd_125548 := by
    simpa [prefixWord, tailWord_125548, baseEnd_125548] using wordTrace_append hprefix tailTrace_125548
  have hstable : (prefixWord ++ tailWord_125548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125548).length < 2 ^ (prefixWord ++ tailWord_125548).sum := by decide
  have hdescent : baseEnd_125548 < baseStart_125548 := by decide
  rcases family_descends (prefixWord ++ tailWord_125548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125565 : List Nat := [1, 4, 1, 1, 6, 6]
def baseStart_125565 : Nat := 118140960795 + 125565 * 2 ^ 59
def prefixEnd_125565 : Nat := 4983230072969 + 3 ^ 40 * 125565 * 2
def baseEnd_125565 : Nat := 4245280551895075559509

theorem tailTrace_125565 : CollatzResearch.WordTrace tailWord_125565 prefixEnd_125565 4245280551895075559509 := by
  unfold tailWord_125565
  simp only [CollatzResearch.WordTrace]
  refine ⟨4579731790106924639802149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3053154526737949759868099 4579731790106924639802149)
  ·
    refine ⟨858699710645048369962903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4579731790106924639802149 858699710645048369962903)
    ·
      refine ⟨1288049565967572554944355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 858699710645048369962903 1288049565967572554944355)
      ·
        refine ⟨1932074348951358832416533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288049565967572554944355 1932074348951358832416533)
        ·
          refine ⟨90565985107094945269525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1932074348951358832416533 90565985107094945269525)
          ·
            refine ⟨4245280551895075559509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90565985107094945269525 4245280551895075559509)
            ·
              rfl

theorem cell19_125565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 6].length) (baseStart_125565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125565 prefixEnd_125565 := by exact prefixLift 125565
  have htrace : WordTrace (prefixWord ++ tailWord_125565) baseStart_125565 baseEnd_125565 := by
    simpa [prefixWord, tailWord_125565, baseEnd_125565] using wordTrace_append hprefix tailTrace_125565
  have hstable : (prefixWord ++ tailWord_125565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125565).length < 2 ^ (prefixWord ++ tailWord_125565).sum := by decide
  have hdescent : baseEnd_125565 < baseStart_125565 := by decide
  rcases family_descends (prefixWord ++ tailWord_125565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125601 : List Nat := [1, 2, 3, 3, 3, 1, 3, 3]
def baseStart_125601 : Nat := 118140960795 + 125601 * 2 ^ 59
def prefixEnd_125601 : Nat := 4983230072969 + 3 ^ 40 * 125601 * 2
def baseEnd_125601 : Nat := 38218479221018263235483

theorem tailTrace_125601 : CollatzResearch.WordTrace tailWord_125601 prefixEnd_125601 38218479221018263235483 := by
  unfold tailWord_125601
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581044817976502788112657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3054029878651001858741771 4581044817976502788112657)
  ·
    refine ⟨3435783613482377091084493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4581044817976502788112657 3435783613482377091084493)
    ·
      refine ⟨1288418855055891409156685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3435783613482377091084493 1288418855055891409156685)
      ·
        refine ⟨483157070645959278433757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1288418855055891409156685 483157070645959278433757)
        ·
          refine ⟨181183901492234729412659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483157070645959278433757 181183901492234729412659)
          ·
            refine ⟨271775852238352094118989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181183901492234729412659 271775852238352094118989)
            ·
              refine ⟨101915944589382035294621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271775852238352094118989 101915944589382035294621)
              ·
                refine ⟨38218479221018263235483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101915944589382035294621 38218479221018263235483)
                ·
                  rfl

theorem cell19_125601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3].length) (baseStart_125601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125601 prefixEnd_125601 := by exact prefixLift 125601
  have htrace : WordTrace (prefixWord ++ tailWord_125601) baseStart_125601 baseEnd_125601 := by
    simpa [prefixWord, tailWord_125601, baseEnd_125601] using wordTrace_append hprefix tailTrace_125601
  have hstable : (prefixWord ++ tailWord_125601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125601).length < 2 ^ (prefixWord ++ tailWord_125601).sum := by decide
  have hdescent : baseEnd_125601 < baseStart_125601 := by decide
  rcases family_descends (prefixWord ++ tailWord_125601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125698 : List Nat := [3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_125698 : Nat := 118140960795 + 125698 * 2 ^ 59
def prefixEnd_125698 : Nat := 4983230072969 + 3 ^ 40 * 125698 * 2
def baseEnd_125698 : Nat := 38247994849750779079663

theorem tailTrace_125698 : CollatzResearch.WordTrace tailWord_125698 prefixEnd_125698 38247994849750779079663 := by
  unfold tailWord_125698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146145674656272088598437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3056388465750058902929165 1146145674656272088598437)
  ·
    refine ⟨214902313998051016612207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1146145674656272088598437 214902313998051016612207)
    ·
      refine ⟨322353470997076524918311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214902313998051016612207 322353470997076524918311)
      ·
        refine ⟨483530206495614787377467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322353470997076524918311 483530206495614787377467)
        ·
          refine ⟨725295309743422181066201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483530206495614787377467 725295309743422181066201)
          ·
            refine ⟨543971482307566635799651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725295309743422181066201 543971482307566635799651)
            ·
              refine ⟨815957223461349953699477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543971482307566635799651 815957223461349953699477)
              ·
                refine ⟨38247994849750779079663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 815957223461349953699477 38247994849750779079663)
                ·
                  rfl

theorem cell19_125698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_125698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125698 prefixEnd_125698 := by exact prefixLift 125698
  have htrace : WordTrace (prefixWord ++ tailWord_125698) baseStart_125698 baseEnd_125698 := by
    simpa [prefixWord, tailWord_125698, baseEnd_125698] using wordTrace_append hprefix tailTrace_125698
  have hstable : (prefixWord ++ tailWord_125698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125698).length < 2 ^ (prefixWord ++ tailWord_125698).sum := by decide
  have hdescent : baseEnd_125698 < baseStart_125698 := by decide
  rcases family_descends (prefixWord ++ tailWord_125698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125795 : List Nat := [1, 1, 1, 5, 3, 2, 6]
def baseStart_125795 : Nat := 118140960795 + 125795 * 2 ^ 59
def prefixEnd_125795 : Nat := 4983230072969 + 3 ^ 40 * 125795 * 2
def baseEnd_125795 : Nat := 12759170159494431641281

theorem tailTrace_125795 : CollatzResearch.WordTrace tailWord_125795 prefixEnd_125795 12759170159494431641281 := by
  unfold tailWord_125795
  simp only [CollatzResearch.WordTrace]
  refine ⟨4588120579273673920674839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3058747052849115947116559 4588120579273673920674839)
  ·
    refine ⟨6882180868910510881012259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4588120579273673920674839 6882180868910510881012259)
    ·
      refine ⟨10323271303365766321518389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6882180868910510881012259 10323271303365766321518389)
      ·
        refine ⟨967806684690540592642349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10323271303365766321518389 967806684690540592642349)
        ·
          refine ⟨362927506758952722240881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 967806684690540592642349 362927506758952722240881)
          ·
            refine ⟨272195630069214541680661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362927506758952722240881 272195630069214541680661)
            ·
              refine ⟨12759170159494431641281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 272195630069214541680661 12759170159494431641281)
              ·
                rfl

theorem cell19_125795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_125795 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125795 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125795 prefixEnd_125795 := by exact prefixLift 125795
  have htrace : WordTrace (prefixWord ++ tailWord_125795) baseStart_125795 baseEnd_125795 := by
    simpa [prefixWord, tailWord_125795, baseEnd_125795] using wordTrace_append hprefix tailTrace_125795
  have hstable : (prefixWord ++ tailWord_125795).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125795).length < 2 ^ (prefixWord ++ tailWord_125795).sum := by decide
  have hdescent : baseEnd_125795 < baseStart_125795 := by decide
  rcases family_descends (prefixWord ++ tailWord_125795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125831 : List Nat := [1, 1, 4, 2, 3, 1, 4, 3]
def baseStart_125831 : Nat := 118140960795 + 125831 * 2 ^ 59
def prefixEnd_125831 : Nat := 4983230072969 + 3 ^ 40 * 125831 * 2
def baseEnd_125831 : Nat := 38288464732445878123745

theorem tailTrace_125831 : CollatzResearch.WordTrace tailWord_125831 prefixEnd_125831 38288464732445878123745 := by
  unfold tailWord_125831
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589433607143252068985347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3059622404762168045990231 4589433607143252068985347)
  ·
    refine ⟨6884150410714878103478021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4589433607143252068985347 6884150410714878103478021)
    ·
      refine ⟨1290778202009039644402129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6884150410714878103478021 1290778202009039644402129)
      ·
        refine ⟨968083651506779733301597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1290778202009039644402129 968083651506779733301597)
        ·
          refine ⟨363031369315042399988099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 968083651506779733301597 363031369315042399988099)
          ·
            refine ⟨544547053972563599982149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363031369315042399988099 544547053972563599982149)
            ·
              refine ⟨102102572619855674996653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 544547053972563599982149 102102572619855674996653)
              ·
                refine ⟨38288464732445878123745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102102572619855674996653 38288464732445878123745)
                ·
                  rfl

theorem cell19_125831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 3].length) (baseStart_125831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125831 prefixEnd_125831 := by exact prefixLift 125831
  have htrace : WordTrace (prefixWord ++ tailWord_125831) baseStart_125831 baseEnd_125831 := by
    simpa [prefixWord, tailWord_125831, baseEnd_125831] using wordTrace_append hprefix tailTrace_125831
  have hstable : (prefixWord ++ tailWord_125831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125831).length < 2 ^ (prefixWord ++ tailWord_125831).sum := by decide
  have hdescent : baseEnd_125831 < baseStart_125831 := by decide
  rcases family_descends (prefixWord ++ tailWord_125831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125833 : List Nat := [1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_125833 : Nat := 118140960795 + 125833 * 2 ^ 59
def prefixEnd_125833 : Nat := 4983230072969 + 3 ^ 40 * 125833 * 2
def baseEnd_125833 : Nat := 38289073302110466079295

theorem tailTrace_125833 : CollatzResearch.WordTrace tailWord_125833 prefixEnd_125833 38289073302110466079295 := by
  unfold tailWord_125833
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589506553136006410558153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3059671035424004273705435 4589506553136006410558153)
  ·
    refine ⟨3442129914852004807918615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4589506553136006410558153 3442129914852004807918615)
    ·
      refine ⟨5163194872278007211877923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442129914852004807918615 5163194872278007211877923)
      ·
        refine ⟨7744792308417010817816885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5163194872278007211877923 7744792308417010817816885)
        ·
          refine ⟨726074278914094764170333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7744792308417010817816885 726074278914094764170333)
          ·
            refine ⟨272277854592785536563875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 726074278914094764170333 272277854592785536563875)
            ·
              refine ⟨408416781889178304845813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272277854592785536563875 408416781889178304845813)
              ·
                refine ⟨38289073302110466079295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 408416781889178304845813 38289073302110466079295)
                ·
                  rfl

theorem cell19_125833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_125833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125833 prefixEnd_125833 := by exact prefixLift 125833
  have htrace : WordTrace (prefixWord ++ tailWord_125833) baseStart_125833 baseEnd_125833 := by
    simpa [prefixWord, tailWord_125833, baseEnd_125833] using wordTrace_append hprefix tailTrace_125833
  have hstable : (prefixWord ++ tailWord_125833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125833).length < 2 ^ (prefixWord ++ tailWord_125833).sum := by decide
  have hdescent : baseEnd_125833 < baseStart_125833 := by decide
  rcases family_descends (prefixWord ++ tailWord_125833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125846 : List Nat := [5, 3, 1, 1, 1, 3, 5]
def baseStart_125846 : Nat := 118140960795 + 125846 * 2 ^ 59
def prefixEnd_125846 : Nat := 4983230072969 + 3 ^ 40 * 125846 * 2
def baseEnd_125846 : Nat := 12764343001643429263457

theorem tailTrace_125846 : CollatzResearch.WordTrace tailWord_125846 prefixEnd_125846 12764343001643429263457 := by
  unfold tailWord_125846
  simp only [CollatzResearch.WordTrace]
  refine ⟨286873793880556851923837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3059987134725939753854261 286873793880556851923837)
  ·
    refine ⟨107577672705208819471439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286873793880556851923837 107577672705208819471439)
    ·
      refine ⟨161366509057813229207159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107577672705208819471439 161366509057813229207159)
      ·
        refine ⟨242049763586719843810739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161366509057813229207159 242049763586719843810739)
        ·
          refine ⟨363074645380079765716109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242049763586719843810739 363074645380079765716109)
          ·
            refine ⟨136152992017529912143541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363074645380079765716109 136152992017529912143541)
            ·
              refine ⟨12764343001643429263457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136152992017529912143541 12764343001643429263457)
              ·
                rfl

theorem cell19_125846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 5].length) (baseStart_125846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125846 prefixEnd_125846 := by exact prefixLift 125846
  have htrace : WordTrace (prefixWord ++ tailWord_125846) baseStart_125846 baseEnd_125846 := by
    simpa [prefixWord, tailWord_125846, baseEnd_125846] using wordTrace_append hprefix tailTrace_125846
  have hstable : (prefixWord ++ tailWord_125846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125846).length < 2 ^ (prefixWord ++ tailWord_125846).sum := by decide
  have hdescent : baseEnd_125846 < baseStart_125846 := by decide
  rcases family_descends (prefixWord ++ tailWord_125846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125850 : List Nat := [3, 1, 1, 4, 3, 2, 5]
def baseStart_125850 : Nat := 118140960795 + 125850 * 2 ^ 59
def prefixEnd_125850 : Nat := 4983230072969 + 3 ^ 40 * 125850 * 2
def baseEnd_125850 : Nat := 12764748714753154567157

theorem tailTrace_125850 : CollatzResearch.WordTrace tailWord_125850 prefixEnd_125850 12764748714753154567157 := by
  unfold tailWord_125850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1147531648518604578481751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3060084396049612209284669 1147531648518604578481751)
  ·
    refine ⟨1721297472777906867722627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1147531648518604578481751 1721297472777906867722627)
    ·
      refine ⟨2581946209166860301583941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1721297472777906867722627 2581946209166860301583941)
      ·
        refine ⟨484114914218786306546989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2581946209166860301583941 484114914218786306546989)
        ·
          refine ⟨181543092832044864955121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484114914218786306546989 181543092832044864955121)
          ·
            refine ⟨136157319624033648716341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181543092832044864955121 136157319624033648716341)
            ·
              refine ⟨12764748714753154567157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136157319624033648716341 12764748714753154567157)
              ·
                rfl

theorem cell19_125850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_125850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125850 prefixEnd_125850 := by exact prefixLift 125850
  have htrace : WordTrace (prefixWord ++ tailWord_125850) baseStart_125850 baseEnd_125850 := by
    simpa [prefixWord, tailWord_125850, baseEnd_125850] using wordTrace_append hprefix tailTrace_125850
  have hstable : (prefixWord ++ tailWord_125850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125850).length < 2 ^ (prefixWord ++ tailWord_125850).sum := by decide
  have hdescent : baseEnd_125850 < baseStart_125850 := by decide
  rcases family_descends (prefixWord ++ tailWord_125850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125909 : List Nat := [1, 3, 2, 3, 3, 7]
def baseStart_125909 : Nat := 118140960795 + 125909 * 2 ^ 59
def prefixEnd_125909 : Nat := 4983230072969 + 3 ^ 40 * 125909 * 2
def baseEnd_125909 : Nat := 4256910994373867598911

theorem tailTrace_125909 : CollatzResearch.WordTrace tailWord_125909 prefixEnd_125909 4256910994373867598911 := by
  unfold tailWord_125909
  simp only [CollatzResearch.WordTrace]
  refine ⟨4592278500860671390324781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3061519000573780926883187 4592278500860671390324781)
  ·
    refine ⟨1722104437822751771371793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4592278500860671390324781 1722104437822751771371793)
    ·
      refine ⟨1291578328367063828528845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1722104437822751771371793 1291578328367063828528845)
      ·
        refine ⟨484341873137648935698317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1291578328367063828528845 484341873137648935698317)
        ·
          refine ⟨181628202426618350886869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 484341873137648935698317 181628202426618350886869)
          ·
            refine ⟨4256910994373867598911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 181628202426618350886869 4256910994373867598911)
            ·
              rfl

theorem cell19_125909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 7].length) (baseStart_125909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125909 prefixEnd_125909 := by exact prefixLift 125909
  have htrace : WordTrace (prefixWord ++ tailWord_125909) baseStart_125909 baseEnd_125909 := by
    simpa [prefixWord, tailWord_125909, baseEnd_125909] using wordTrace_append hprefix tailTrace_125909
  have hstable : (prefixWord ++ tailWord_125909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125909).length < 2 ^ (prefixWord ++ tailWord_125909).sum := by decide
  have hdescent : baseEnd_125909 < baseStart_125909 := by decide
  rcases family_descends (prefixWord ++ tailWord_125909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125928 : List Nat := [2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_125928 : Nat := 118140960795 + 125928 * 2 ^ 59
def prefixEnd_125928 : Nat := 4983230072969 + 3 ^ 40 * 125928 * 2
def baseEnd_125928 : Nat := 38317980361178393967925

theorem tailTrace_125928 : CollatzResearch.WordTrace tailWord_125928 prefixEnd_125928 38317980361178393967925 := by
  unfold tailWord_125928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2296485743895918817633219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3061980991861225090177625 2296485743895918817633219)
  ·
    refine ⟨3444728615843878226449829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2296485743895918817633219 3444728615843878226449829)
    ·
      refine ⟨645886615470727167459343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3444728615843878226449829 645886615470727167459343)
      ·
        refine ⟨968829923206090751189015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645886615470727167459343 968829923206090751189015)
        ·
          refine ⟨1453244884809136126783523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968829923206090751189015 1453244884809136126783523)
          ·
            refine ⟨2179867327213704190175285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453244884809136126783523 2179867327213704190175285)
            ·
              refine ⟨204362561926284767828933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2179867327213704190175285 204362561926284767828933)
              ·
                refine ⟨38317980361178393967925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204362561926284767828933 38317980361178393967925)
                ·
                  rfl

theorem cell19_125928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_125928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125928 prefixEnd_125928 := by exact prefixLift 125928
  have htrace : WordTrace (prefixWord ++ tailWord_125928) baseStart_125928 baseEnd_125928 := by
    simpa [prefixWord, tailWord_125928, baseEnd_125928] using wordTrace_append hprefix tailTrace_125928
  have hstable : (prefixWord ++ tailWord_125928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125928).length < 2 ^ (prefixWord ++ tailWord_125928).sum := by decide
  have hdescent : baseEnd_125928 < baseStart_125928 := by decide
  rcases family_descends (prefixWord ++ tailWord_125928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125941 : List Nat := [1, 3, 5, 2, 1, 1, 3, 3]
def baseStart_125941 : Nat := 118140960795 + 125941 * 2 ^ 59
def prefixEnd_125941 : Nat := 4983230072969 + 3 ^ 40 * 125941 * 2
def baseEnd_125941 : Nat := 38321936063998215679001

theorem tailTrace_125941 : CollatzResearch.WordTrace tailWord_125941 prefixEnd_125941 38321936063998215679001 := by
  unfold tailWord_125941
  simp only [CollatzResearch.WordTrace]
  refine ⟨4593445636744740855489677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3062297091163160570326451 4593445636744740855489677)
  ·
    refine ⟨1722542113779277820808629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4593445636744740855489677 1722542113779277820808629)
    ·
      refine ⟨161488323166807295700809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1722542113779277820808629 161488323166807295700809)
      ·
        refine ⟨121116242375105471775607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161488323166807295700809 121116242375105471775607)
        ·
          refine ⟨181674363562658207663411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121116242375105471775607 181674363562658207663411)
          ·
            refine ⟨272511545343987311495117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181674363562658207663411 272511545343987311495117)
            ·
              refine ⟨102191829503995241810669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272511545343987311495117 102191829503995241810669)
              ·
                refine ⟨38321936063998215679001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102191829503995241810669 38321936063998215679001)
                ·
                  rfl

theorem cell19_125941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 3].length) (baseStart_125941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125941 prefixEnd_125941 := by exact prefixLift 125941
  have htrace : WordTrace (prefixWord ++ tailWord_125941) baseStart_125941 baseEnd_125941 := by
    simpa [prefixWord, tailWord_125941, baseEnd_125941] using wordTrace_append hprefix tailTrace_125941
  have hstable : (prefixWord ++ tailWord_125941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125941).length < 2 ^ (prefixWord ++ tailWord_125941).sum := by decide
  have hdescent : baseEnd_125941 < baseStart_125941 := by decide
  rcases family_descends (prefixWord ++ tailWord_125941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125966 : List Nat := [4, 1, 1, 2, 2, 3, 6]
def baseStart_125966 : Nat := 118140960795 + 125966 * 2 ^ 59
def prefixEnd_125966 : Nat := 4983230072969 + 3 ^ 40 * 125966 * 2
def baseEnd_125966 : Nat := 12776514394935188374459

theorem tailTrace_125966 : CollatzResearch.WordTrace tailWord_125966 prefixEnd_125966 12776514394935188374459 := by
  unfold tailWord_125966
  simp only [CollatzResearch.WordTrace]
  refine ⟨574294682706771265643719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3062904974436113416766501 574294682706771265643719)
  ·
    refine ⟨861442024060156898465579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 574294682706771265643719 861442024060156898465579)
    ·
      refine ⟨1292163036090235347698369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861442024060156898465579 1292163036090235347698369)
      ·
        refine ⟨969122277067676510773777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1292163036090235347698369 969122277067676510773777)
        ·
          refine ⟨726841707800757383080333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969122277067676510773777 726841707800757383080333)
          ·
            refine ⟨272565640425284018655125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 726841707800757383080333 272565640425284018655125)
            ·
              refine ⟨12776514394935188374459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 272565640425284018655125 12776514394935188374459)
              ·
                rfl

theorem cell19_125966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_125966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_125966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_125966 prefixEnd_125966 := by exact prefixLift 125966
  have htrace : WordTrace (prefixWord ++ tailWord_125966) baseStart_125966 baseEnd_125966 := by
    simpa [prefixWord, tailWord_125966, baseEnd_125966] using wordTrace_append hprefix tailTrace_125966
  have hstable : (prefixWord ++ tailWord_125966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125966).length < 2 ^ (prefixWord ++ tailWord_125966).sum := by decide
  have hdescent : baseEnd_125966 < baseStart_125966 := by decide
  rcases family_descends (prefixWord ++ tailWord_125966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126023 : List Nat := [1, 1, 4, 1, 3, 4, 5]
def baseStart_126023 : Nat := 118140960795 + 126023 * 2 ^ 59
def prefixEnd_126023 : Nat := 4983230072969 + 3 ^ 40 * 126023 * 2
def baseEnd_126023 : Nat := 12782295806748773952185

theorem tailTrace_126023 : CollatzResearch.WordTrace tailWord_126023 prefixEnd_126023 12782295806748773952185 := by
  unfold tailWord_126023
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596436422447668859974723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3064290948298445906649815 4596436422447668859974723)
  ·
    refine ⟨6894654633671503289962085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4596436422447668859974723 6894654633671503289962085)
    ·
      refine ⟨1292747743813406866867891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6894654633671503289962085 1292747743813406866867891)
      ·
        refine ⟨1939121615720110300301837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292747743813406866867891 1939121615720110300301837)
        ·
          refine ⟨727170605895041362613189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1939121615720110300301837 727170605895041362613189)
          ·
            refine ⟨136344488605320255489973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 727170605895041362613189 136344488605320255489973)
            ·
              refine ⟨12782295806748773952185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136344488605320255489973 12782295806748773952185)
              ·
                rfl

theorem cell19_126023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_126023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126023 prefixEnd_126023 := by exact prefixLift 126023
  have htrace : WordTrace (prefixWord ++ tailWord_126023) baseStart_126023 baseEnd_126023 := by
    simpa [prefixWord, tailWord_126023, baseEnd_126023] using wordTrace_append hprefix tailTrace_126023
  have hstable : (prefixWord ++ tailWord_126023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126023).length < 2 ^ (prefixWord ++ tailWord_126023).sum := by decide
  have hdescent : baseEnd_126023 < baseStart_126023 := by decide
  rcases family_descends (prefixWord ++ tailWord_126023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126061 : List Nat := [1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_126061 : Nat := 118140960795 + 126061 * 2 ^ 59
def prefixEnd_126061 : Nat := 4983230072969 + 3 ^ 40 * 126061 * 2
def baseEnd_126061 : Nat := 38358450243873493012007

theorem tailTrace_126061 : CollatzResearch.WordTrace tailWord_126061 prefixEnd_126061 38358450243873493012007 := by
  unfold tailWord_126061
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597822396310001349858037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3065214930873334233238691 4597822396310001349858037)
  ·
    refine ⟨431045849654062626549191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4597822396310001349858037 431045849654062626549191)
    ·
      refine ⟨646568774481093939823787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431045849654062626549191 646568774481093939823787)
      ·
        refine ⟨969853161721640909735681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646568774481093939823787 969853161721640909735681)
        ·
          refine ⟨727389871291230682301761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969853161721640909735681 727389871291230682301761)
          ·
            refine ⟨545542403468423011726321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727389871291230682301761 545542403468423011726321)
            ·
              refine ⟨409156802601317258794741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545542403468423011726321 409156802601317258794741)
              ·
                refine ⟨38358450243873493012007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409156802601317258794741 38358450243873493012007)
                ·
                  rfl

theorem cell19_126061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_126061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126061 prefixEnd_126061 := by exact prefixLift 126061
  have htrace : WordTrace (prefixWord ++ tailWord_126061) baseStart_126061 baseEnd_126061 := by
    simpa [prefixWord, tailWord_126061, baseEnd_126061] using wordTrace_append hprefix tailTrace_126061
  have hstable : (prefixWord ++ tailWord_126061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126061).length < 2 ^ (prefixWord ++ tailWord_126061).sum := by decide
  have hdescent : baseEnd_126061 < baseStart_126061 := by decide
  rcases family_descends (prefixWord ++ tailWord_126061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126063 : List Nat := [1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_126063 : Nat := 118140960795 + 126063 * 2 ^ 59
def prefixEnd_126063 : Nat := 4983230072969 + 3 ^ 40 * 126063 * 2
def baseEnd_126063 : Nat := 38359058813538080967557

theorem tailTrace_126063 : CollatzResearch.WordTrace tailWord_126063 prefixEnd_126063 38359058813538080967557 := by
  unfold tailWord_126063
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597895342302755691430843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3065263561535170460953895 4597895342302755691430843)
  ·
    refine ⟨6896843013454133537146265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4597895342302755691430843 6896843013454133537146265)
    ·
      refine ⟨5172632260090600152859699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6896843013454133537146265 5172632260090600152859699)
      ·
        refine ⟨7758948390135900229289549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172632260090600152859699 7758948390135900229289549)
        ·
          refine ⟨2909605646300962585983581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7758948390135900229289549 2909605646300962585983581)
          ·
            refine ⟨1091102117362860969743843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2909605646300962585983581 1091102117362860969743843)
            ·
              refine ⟨1636653176044291454615765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091102117362860969743843 1636653176044291454615765)
              ·
                refine ⟨38359058813538080967557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1636653176044291454615765 38359058813538080967557)
                ·
                  rfl

theorem cell19_126063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_126063 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126063 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126063 prefixEnd_126063 := by exact prefixLift 126063
  have htrace : WordTrace (prefixWord ++ tailWord_126063) baseStart_126063 baseEnd_126063 := by
    simpa [prefixWord, tailWord_126063, baseEnd_126063] using wordTrace_append hprefix tailTrace_126063
  have hstable : (prefixWord ++ tailWord_126063).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126063).length < 2 ^ (prefixWord ++ tailWord_126063).sum := by decide
  have hdescent : baseEnd_126063 < baseStart_126063 := by decide
  rcases family_descends (prefixWord ++ tailWord_126063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126101 : List Nat := [1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_126101 : Nat := 118140960795 + 126101 * 2 ^ 59
def prefixEnd_126101 : Nat := 4983230072969 + 3 ^ 40 * 126101 * 2
def baseEnd_126101 : Nat := 38370621637165252123009

theorem tailTrace_126101 : CollatzResearch.WordTrace tailWord_126101 prefixEnd_126101 38370621637165252123009 := by
  unfold tailWord_126101
  simp only [CollatzResearch.WordTrace]
  refine ⟨4599281316165088181314157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3066187544110058787542771 4599281316165088181314157)
  ·
    refine ⟨1724730493561908067992809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4599281316165088181314157 1724730493561908067992809)
    ·
      refine ⟨1293547870171431050994607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1724730493561908067992809 1293547870171431050994607)
      ·
        refine ⟨1940321805257146576491911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293547870171431050994607 1940321805257146576491911)
        ·
          refine ⟨2910482707885719864737867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940321805257146576491911 2910482707885719864737867)
          ·
            refine ⟨4365724061828579797106801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910482707885719864737867 4365724061828579797106801)
            ·
              refine ⟨3274293046371434847830101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365724061828579797106801 3274293046371434847830101)
              ·
                refine ⟨38370621637165252123009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3274293046371434847830101 38370621637165252123009)
                ·
                  rfl

theorem cell19_126101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_126101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126101 prefixEnd_126101 := by exact prefixLift 126101
  have htrace : WordTrace (prefixWord ++ tailWord_126101) baseStart_126101 baseEnd_126101 := by
    simpa [prefixWord, tailWord_126101, baseEnd_126101] using wordTrace_append hprefix tailTrace_126101
  have hstable : (prefixWord ++ tailWord_126101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126101).length < 2 ^ (prefixWord ++ tailWord_126101).sum := by decide
  have hdescent : baseEnd_126101 < baseStart_126101 := by decide
  rcases family_descends (prefixWord ++ tailWord_126101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126114 : List Nat := [3, 3, 1, 3, 2, 1, 3, 3]
def baseStart_126114 : Nat := 118140960795 + 126114 * 2 ^ 59
def prefixEnd_126114 : Nat := 4983230072969 + 3 ^ 40 * 126114 * 2
def baseEnd_126114 : Nat := 38374577339985073834085

theorem tailTrace_126114 : CollatzResearch.WordTrace tailWord_126114 prefixEnd_126114 38374577339985073834085 := by
  unfold tailWord_126114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149938866279497850384349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3066503643411994267691597 1149938866279497850384349)
  ·
    refine ⟨431227074854811693894131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1149938866279497850384349 431227074854811693894131)
    ·
      refine ⟨646840612282217540841197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431227074854811693894131 646840612282217540841197)
      ·
        refine ⟨242565229605831577815449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 646840612282217540841197 242565229605831577815449)
        ·
          refine ⟨181923922204373683361587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242565229605831577815449 181923922204373683361587)
          ·
            refine ⟨272885883306560525042381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181923922204373683361587 272885883306560525042381)
            ·
              refine ⟨102332206239960196890893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272885883306560525042381 102332206239960196890893)
              ·
                refine ⟨38374577339985073834085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102332206239960196890893 38374577339985073834085)
                ·
                  rfl

theorem cell19_126114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_126114 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126114 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126114 prefixEnd_126114 := by exact prefixLift 126114
  have htrace : WordTrace (prefixWord ++ tailWord_126114) baseStart_126114 baseEnd_126114 := by
    simpa [prefixWord, tailWord_126114, baseEnd_126114] using wordTrace_append hprefix tailTrace_126114
  have hstable : (prefixWord ++ tailWord_126114).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126114).length < 2 ^ (prefixWord ++ tailWord_126114).sum := by decide
  have hdescent : baseEnd_126114 < baseStart_126114 := by decide
  rcases family_descends (prefixWord ++ tailWord_126114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126116 : List Nat := [2, 3, 1, 2, 3, 2, 3, 3]
def baseStart_126116 : Nat := 118140960795 + 126116 * 2 ^ 59
def prefixEnd_126116 : Nat := 4983230072969 + 3 ^ 40 * 126116 * 2
def baseEnd_126116 : Nat := 38375185909649661789635

theorem tailTrace_126116 : CollatzResearch.WordTrace tailWord_126116 prefixEnd_126116 38375185909649661789635 := by
  unfold tailWord_126116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299914205555372871555101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3066552274073830495406801 2299914205555372871555101)
  ·
    refine ⟨862467827083264826833163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2299914205555372871555101 862467827083264826833163)
    ·
      refine ⟨1293701740624897240249745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862467827083264826833163 1293701740624897240249745)
      ·
        refine ⟨970276305468672930187309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1293701740624897240249745 970276305468672930187309)
        ·
          refine ⟨363853614550752348820241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 970276305468672930187309 363853614550752348820241)
          ·
            refine ⟨272890210913064261615181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363853614550752348820241 272890210913064261615181)
            ·
              refine ⟨102333829092399098105693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272890210913064261615181 102333829092399098105693)
              ·
                refine ⟨38375185909649661789635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102333829092399098105693 38375185909649661789635)
                ·
                  rfl

theorem cell19_126116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_126116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126116 prefixEnd_126116 := by exact prefixLift 126116
  have htrace : WordTrace (prefixWord ++ tailWord_126116) baseStart_126116 baseEnd_126116 := by
    simpa [prefixWord, tailWord_126116, baseEnd_126116] using wordTrace_append hprefix tailTrace_126116
  have hstable : (prefixWord ++ tailWord_126116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126116).length < 2 ^ (prefixWord ++ tailWord_126116).sum := by decide
  have hdescent : baseEnd_126116 < baseStart_126116 := by decide
  rcases family_descends (prefixWord ++ tailWord_126116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126173 : List Nat := [1, 4, 3, 2, 2, 1, 1, 5]
def baseStart_126173 : Nat := 118140960795 + 126173 * 2 ^ 59
def prefixEnd_126173 : Nat := 4983230072969 + 3 ^ 40 * 126173 * 2
def baseEnd_126173 : Nat := 38392530145090418522813

theorem tailTrace_126173 : CollatzResearch.WordTrace tailWord_126173 prefixEnd_126173 38392530145090418522813 := by
  unfold tailWord_126173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4601907371904244477935173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3067938247936162985290115 4601907371904244477935173)
  ·
    refine ⟨862857632232045839612845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4601907371904244477935173 862857632232045839612845)
    ·
      refine ⟨323571612087017189854817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 862857632232045839612845 323571612087017189854817)
      ·
        refine ⟨242678709065262892391113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323571612087017189854817 242678709065262892391113)
        ·
          refine ⟨182009031798947169293335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242678709065262892391113 182009031798947169293335)
          ·
            refine ⟨273013547698420753940003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182009031798947169293335 273013547698420753940003)
            ·
              refine ⟨409520321547631130910005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273013547698420753940003 409520321547631130910005)
              ·
                refine ⟨38392530145090418522813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409520321547631130910005 38392530145090418522813)
                ·
                  rfl

theorem cell19_126173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_126173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126173 prefixEnd_126173 := by exact prefixLift 126173
  have htrace : WordTrace (prefixWord ++ tailWord_126173) baseStart_126173 baseEnd_126173 := by
    simpa [prefixWord, tailWord_126173, baseEnd_126173] using wordTrace_append hprefix tailTrace_126173
  have hstable : (prefixWord ++ tailWord_126173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126173).length < 2 ^ (prefixWord ++ tailWord_126173).sum := by decide
  have hdescent : baseEnd_126173 < baseStart_126173 := by decide
  rcases family_descends (prefixWord ++ tailWord_126173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126175 : List Nat := [1, 1, 2, 3, 2, 1, 6, 3]
def baseStart_126175 : Nat := 118140960795 + 126175 * 2 ^ 59
def prefixEnd_126175 : Nat := 4983230072969 + 3 ^ 40 * 126175 * 2
def baseEnd_126175 : Nat := 38393138714755006478363

theorem tailTrace_126175 : CollatzResearch.WordTrace tailWord_126175 prefixEnd_126175 38393138714755006478363 := by
  unfold tailWord_126175
  simp only [CollatzResearch.WordTrace]
  refine ⟨4601980317896998819507979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3067986878597999213005319 4601980317896998819507979)
  ·
    refine ⟨6902970476845498229261969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4601980317896998819507979 6902970476845498229261969)
    ·
      refine ⟨5177227857634123671946477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6902970476845498229261969 5177227857634123671946477)
      ·
        refine ⟨1941460446612796376979929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5177227857634123671946477 1941460446612796376979929)
        ·
          refine ⟨1456095334959597282734947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1941460446612796376979929 1456095334959597282734947)
          ·
            refine ⟨2184143002439395924102421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456095334959597282734947 2184143002439395924102421)
            ·
              refine ⟨102381703239346683942301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2184143002439395924102421 102381703239346683942301)
              ·
                refine ⟨38393138714755006478363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102381703239346683942301 38393138714755006478363)
                ·
                  rfl

theorem cell19_126175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 3].length) (baseStart_126175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126175 prefixEnd_126175 := by exact prefixLift 126175
  have htrace : WordTrace (prefixWord ++ tailWord_126175) baseStart_126175 baseEnd_126175 := by
    simpa [prefixWord, tailWord_126175, baseEnd_126175] using wordTrace_append hprefix tailTrace_126175
  have hstable : (prefixWord ++ tailWord_126175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126175).length < 2 ^ (prefixWord ++ tailWord_126175).sum := by decide
  have hdescent : baseEnd_126175 < baseStart_126175 := by decide
  rcases family_descends (prefixWord ++ tailWord_126175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126289 : List Nat := [1, 2, 2, 1, 4, 1, 5, 3]
def baseStart_126289 : Nat := 118140960795 + 126289 * 2 ^ 59
def prefixEnd_126289 : Nat := 4983230072969 + 3 ^ 40 * 126289 * 2
def baseEnd_126289 : Nat := 38427827185636519944719

theorem tailTrace_126289 : CollatzResearch.WordTrace tailWord_126289 prefixEnd_126289 38427827185636519944719 := by
  unfold tailWord_126289
  simp only [CollatzResearch.WordTrace]
  refine ⟨4606138239483996289157921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3070758826322664192771947 4606138239483996289157921)
  ·
    refine ⟨3454603679612997216868441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4606138239483996289157921 3454603679612997216868441)
    ·
      refine ⟨2590952759709747912651331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3454603679612997216868441 2590952759709747912651331)
      ·
        refine ⟨3886429139564621868976997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590952759709747912651331 3886429139564621868976997)
        ·
          refine ⟨728705463668366600433187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3886429139564621868976997 728705463668366600433187)
          ·
            refine ⟨1093058195502549900649781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728705463668366600433187 1093058195502549900649781)
            ·
              refine ⟨102474205828364053185917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1093058195502549900649781 102474205828364053185917)
              ·
                refine ⟨38427827185636519944719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102474205828364053185917 38427827185636519944719)
                ·
                  rfl

theorem cell19_126289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 3].length) (baseStart_126289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126289 prefixEnd_126289 := by exact prefixLift 126289
  have htrace : WordTrace (prefixWord ++ tailWord_126289) baseStart_126289 baseEnd_126289 := by
    simpa [prefixWord, tailWord_126289, baseEnd_126289] using wordTrace_append hprefix tailTrace_126289
  have hstable : (prefixWord ++ tailWord_126289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126289).length < 2 ^ (prefixWord ++ tailWord_126289).sum := by decide
  have hdescent : baseEnd_126289 < baseStart_126289 := by decide
  rcases family_descends (prefixWord ++ tailWord_126289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126344 : List Nat := [2, 1, 3, 3, 1, 4, 2, 3]
def baseStart_126344 : Nat := 118140960795 + 126344 * 2 ^ 59
def prefixEnd_126344 : Nat := 4983230072969 + 3 ^ 40 * 126344 * 2
def baseEnd_126344 : Nat := 38444562851412688722347

theorem tailTrace_126344 : CollatzResearch.WordTrace tailWord_126344 prefixEnd_126344 38444562851412688722347 := by
  unfold tailWord_126344
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304072127142370341205043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3072096169523160454940057 2304072127142370341205043)
  ·
    refine ⟨3456108190713555511807565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2304072127142370341205043 3456108190713555511807565)
    ·
      refine ⟨1296040571517583316927837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3456108190713555511807565 1296040571517583316927837)
      ·
        refine ⟨486015214319093743847939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1296040571517583316927837 486015214319093743847939)
        ·
          refine ⟨729022821478640615771909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486015214319093743847939 729022821478640615771909)
          ·
            refine ⟨136691779027245115457233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 729022821478640615771909 136691779027245115457233)
            ·
              refine ⟨102518834270433836592925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136691779027245115457233 102518834270433836592925)
              ·
                refine ⟨38444562851412688722347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102518834270433836592925 38444562851412688722347)
                ·
                  rfl

theorem cell19_126344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_126344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126344 prefixEnd_126344 := by exact prefixLift 126344
  have htrace : WordTrace (prefixWord ++ tailWord_126344) baseStart_126344 baseEnd_126344 := by
    simpa [prefixWord, tailWord_126344, baseEnd_126344] using wordTrace_append hprefix tailTrace_126344
  have hstable : (prefixWord ++ tailWord_126344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126344).length < 2 ^ (prefixWord ++ tailWord_126344).sum := by decide
  have hdescent : baseEnd_126344 < baseStart_126344 := by decide
  rcases family_descends (prefixWord ++ tailWord_126344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126348 : List Nat := [2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_126348 : Nat := 118140960795 + 126348 * 2 ^ 59
def prefixEnd_126348 : Nat := 4983230072969 + 3 ^ 40 * 126348 * 2
def baseEnd_126348 : Nat := 38445779990741864633447

theorem tailTrace_126348 : CollatzResearch.WordTrace tailWord_126348 prefixEnd_126348 38445779990741864633447 := by
  unfold tailWord_126348
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304145073135124682777849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3072193430846832910370465 2304145073135124682777849)
  ·
    refine ⟨1728108804851343512083387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2304145073135124682777849 1728108804851343512083387)
    ·
      refine ⟨2592163207277015268125081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1728108804851343512083387 2592163207277015268125081)
      ·
        refine ⟨1944122405457761451093811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2592163207277015268125081 1944122405457761451093811)
        ·
          refine ⟨2916183608186642176640717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944122405457761451093811 2916183608186642176640717)
          ·
            refine ⟨1093568853069990816240269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2916183608186642176640717 1093568853069990816240269)
            ·
              refine ⟨410088319901246556090101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1093568853069990816240269 410088319901246556090101)
              ·
                refine ⟨38445779990741864633447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410088319901246556090101 38445779990741864633447)
                ·
                  rfl

theorem cell19_126348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_126348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126348 prefixEnd_126348 := by exact prefixLift 126348
  have htrace : WordTrace (prefixWord ++ tailWord_126348) baseStart_126348 baseEnd_126348 := by
    simpa [prefixWord, tailWord_126348, baseEnd_126348] using wordTrace_append hprefix tailTrace_126348
  have hstable : (prefixWord ++ tailWord_126348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126348).length < 2 ^ (prefixWord ++ tailWord_126348).sum := by decide
  have hdescent : baseEnd_126348 < baseStart_126348 := by decide
  rcases family_descends (prefixWord ++ tailWord_126348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126365 : List Nat := [1, 4, 2, 1, 3, 3, 5]
def baseStart_126365 : Nat := 118140960795 + 126365 * 2 ^ 59
def prefixEnd_126365 : Nat := 4983230072969 + 3 ^ 40 * 126365 * 2
def baseEnd_126365 : Nat := 12816984277630287418541

theorem tailTrace_126365 : CollatzResearch.WordTrace tailWord_126365 prefixEnd_126365 12816984277630287418541 := by
  unfold tailWord_126365
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608910187208661268924549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3072606791472440845949699 4608910187208661268924549)
  ·
    refine ⟨864170660101623987923353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4608910187208661268924549 864170660101623987923353)
    ·
      refine ⟨648127995076217990942515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 864170660101623987923353 648127995076217990942515)
      ·
        refine ⟨972191992614326986413773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648127995076217990942515 972191992614326986413773)
        ·
          refine ⟨364571997230372619905165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 972191992614326986413773 364571997230372619905165)
          ·
            refine ⟨136714498961389732464437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364571997230372619905165 136714498961389732464437)
            ·
              refine ⟨12816984277630287418541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136714498961389732464437 12816984277630287418541)
              ·
                rfl

theorem cell19_126365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_126365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126365 prefixEnd_126365 := by exact prefixLift 126365
  have htrace : WordTrace (prefixWord ++ tailWord_126365) baseStart_126365 baseEnd_126365 := by
    simpa [prefixWord, tailWord_126365, baseEnd_126365] using wordTrace_append hprefix tailTrace_126365
  have hstable : (prefixWord ++ tailWord_126365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126365).length < 2 ^ (prefixWord ++ tailWord_126365).sum := by decide
  have hdescent : baseEnd_126365 < baseStart_126365 := by decide
  rcases family_descends (prefixWord ++ tailWord_126365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126367 : List Nat := [1, 1, 2, 5, 1, 2, 7]
def baseStart_126367 : Nat := 118140960795 + 126367 * 2 ^ 59
def prefixEnd_126367 : Nat := 4983230072969 + 3 ^ 40 * 126367 * 2
def baseEnd_126367 : Nat := 12817187134185150070391

theorem tailTrace_126367 : CollatzResearch.WordTrace tailWord_126367 prefixEnd_126367 12817187134185150070391 := by
  unfold tailWord_126367
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608983133201415610497355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3072655422134277073664903 4608983133201415610497355)
  ·
    refine ⟨6913474699802123415746033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4608983133201415610497355 6913474699802123415746033)
    ·
      refine ⟨5185106024851592561809525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6913474699802123415746033 5185106024851592561809525)
      ·
        refine ⟨486103689829836802669643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5185106024851592561809525 486103689829836802669643)
        ·
          refine ⟨729155534744755204004465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486103689829836802669643 729155534744755204004465)
          ·
            refine ⟨546866651058566403003349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729155534744755204004465 546866651058566403003349)
            ·
              refine ⟨12817187134185150070391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 546866651058566403003349 12817187134185150070391)
              ·
                rfl

theorem cell19_126367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_126367 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126367 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126367 prefixEnd_126367 := by exact prefixLift 126367
  have htrace : WordTrace (prefixWord ++ tailWord_126367) baseStart_126367 baseEnd_126367 := by
    simpa [prefixWord, tailWord_126367, baseEnd_126367] using wordTrace_append hprefix tailTrace_126367
  have hstable : (prefixWord ++ tailWord_126367).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126367).length < 2 ^ (prefixWord ++ tailWord_126367).sum := by decide
  have hdescent : baseEnd_126367 < baseStart_126367 := by decide
  rcases family_descends (prefixWord ++ tailWord_126367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126422 : List Nat := [5, 2, 1, 1, 1, 9]
def baseStart_126422 : Nat := 118140960795 + 126422 * 2 ^ 59
def prefixEnd_126422 : Nat := 4983230072969 + 3 ^ 40 * 126422 * 2
def baseEnd_126422 : Nat := 4274255229814624332089

theorem tailTrace_126422 : CollatzResearch.WordTrace tailWord_126422 prefixEnd_126422 4274255229814624332089 := by
  unfold tailWord_126422
  simp only [CollatzResearch.WordTrace]
  refine ⟨288186821750135000234345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3073992765334773335833013 288186821750135000234345)
  ·
    refine ⟨216140116312601250175759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288186821750135000234345 216140116312601250175759)
    ·
      refine ⟨324210174468901875263639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216140116312601250175759 324210174468901875263639)
      ·
        refine ⟨486315261703352812895459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324210174468901875263639 486315261703352812895459)
        ·
          refine ⟨729472892555029219343189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486315261703352812895459 729472892555029219343189)
          ·
            refine ⟨4274255229814624332089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 729472892555029219343189 4274255229814624332089)
            ·
              rfl

theorem cell19_126422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 9].length) (baseStart_126422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126422 prefixEnd_126422 := by exact prefixLift 126422
  have htrace : WordTrace (prefixWord ++ tailWord_126422) baseStart_126422 baseEnd_126422 := by
    simpa [prefixWord, tailWord_126422, baseEnd_126422] using wordTrace_append hprefix tailTrace_126422
  have hstable : (prefixWord ++ tailWord_126422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126422).length < 2 ^ (prefixWord ++ tailWord_126422).sum := by decide
  have hdescent : baseEnd_126422 < baseStart_126422 := by decide
  rcases family_descends (prefixWord ++ tailWord_126422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126517 : List Nat := [1, 3, 3, 1, 1, 3, 4, 3]
def baseStart_126517 : Nat := 118140960795 + 126517 * 2 ^ 59
def prefixEnd_126517 : Nat := 4983230072969 + 3 ^ 40 * 126517 * 2
def baseEnd_126517 : Nat := 38497204127399546877431

theorem tailTrace_126517 : CollatzResearch.WordTrace tailWord_126517 prefixEnd_126517 38497204127399546877431 := by
  unfold tailWord_126517
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614454082657991228457805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3076302721771994152305203 4614454082657991228457805)
  ·
    refine ⟨1730420280996746710671677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4614454082657991228457805 1730420280996746710671677)
    ·
      refine ⟨648907605373780016501879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1730420280996746710671677 648907605373780016501879)
      ·
        refine ⟨973361408060670024752819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648907605373780016501879 973361408060670024752819)
        ·
          refine ⟨1460042112091005037129229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973361408060670024752819 1460042112091005037129229)
          ·
            refine ⟨547515792034126888923461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1460042112091005037129229 547515792034126888923461)
            ·
              refine ⟨102659211006398791673149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 547515792034126888923461 102659211006398791673149)
              ·
                refine ⟨38497204127399546877431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102659211006398791673149 38497204127399546877431)
                ·
                  rfl

theorem cell19_126517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 3].length) (baseStart_126517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126517 prefixEnd_126517 := by exact prefixLift 126517
  have htrace : WordTrace (prefixWord ++ tailWord_126517) baseStart_126517 baseEnd_126517 := by
    simpa [prefixWord, tailWord_126517, baseEnd_126517] using wordTrace_append hprefix tailTrace_126517
  have hstable : (prefixWord ++ tailWord_126517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126517).length < 2 ^ (prefixWord ++ tailWord_126517).sum := by decide
  have hdescent : baseEnd_126517 < baseStart_126517 := by decide
  rcases family_descends (prefixWord ++ tailWord_126517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126519 : List Nat := [1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_126519 : Nat := 118140960795 + 126519 * 2 ^ 59
def prefixEnd_126519 : Nat := 4983230072969 + 3 ^ 40 * 126519 * 2
def baseEnd_126519 : Nat := 38497812697064134832981

theorem tailTrace_126519 : CollatzResearch.WordTrace tailWord_126519 prefixEnd_126519 38497812697064134832981 := by
  unfold tailWord_126519
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614527028650745570030611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3076351352433830380020407 4614527028650745570030611)
  ·
    refine ⟨6921790542976118355045917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4614527028650745570030611 6921790542976118355045917)
    ·
      refine ⟨2595671453616044383142219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6921790542976118355045917 2595671453616044383142219)
      ·
        refine ⟨3893507180424066574713329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595671453616044383142219 3893507180424066574713329)
        ·
          refine ⟨2920130385318049931034997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3893507180424066574713329 2920130385318049931034997)
          ·
            refine ⟨273762223623567181034531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2920130385318049931034997 273762223623567181034531)
            ·
              refine ⟨410643335435350771551797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273762223623567181034531 410643335435350771551797)
              ·
                refine ⟨38497812697064134832981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410643335435350771551797 38497812697064134832981)
                ·
                  rfl

theorem cell19_126519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_126519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126519 prefixEnd_126519 := by exact prefixLift 126519
  have htrace : WordTrace (prefixWord ++ tailWord_126519) baseStart_126519 baseEnd_126519 := by
    simpa [prefixWord, tailWord_126519, baseEnd_126519] using wordTrace_append hprefix tailTrace_126519
  have hstable : (prefixWord ++ tailWord_126519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126519).length < 2 ^ (prefixWord ++ tailWord_126519).sum := by decide
  have hdescent : baseEnd_126519 < baseStart_126519 := by decide
  rcases family_descends (prefixWord ++ tailWord_126519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126576 : List Nat := [2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_126576 : Nat := 118140960795 + 126576 * 2 ^ 59
def prefixEnd_126576 : Nat := 4983230072969 + 3 ^ 40 * 126576 * 2
def baseEnd_126576 : Nat := 38515156932504891566159

theorem tailTrace_126576 : CollatzResearch.WordTrace tailWord_126576 prefixEnd_126576 38515156932504891566159 := by
  unfold tailWord_126576
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308302994722122152427791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3077737326296162869903721 2308302994722122152427791)
  ·
    refine ⟨3462454492083183228641687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2308302994722122152427791 3462454492083183228641687)
    ·
      refine ⟨5193681738124774842962531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3462454492083183228641687 5193681738124774842962531)
      ·
        refine ⟨7790522607187162264443797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5193681738124774842962531 7790522607187162264443797)
        ·
          refine ⟨365180747211898231145803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7790522607187162264443797 365180747211898231145803)
          ·
            refine ⟨547771120817847346718705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365180747211898231145803 547771120817847346718705)
            ·
              refine ⟨410828340613385510039029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547771120817847346718705 410828340613385510039029)
              ·
                refine ⟨38515156932504891566159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410828340613385510039029 38515156932504891566159)
                ·
                  rfl

theorem cell19_126576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_126576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126576 prefixEnd_126576 := by exact prefixLift 126576
  have htrace : WordTrace (prefixWord ++ tailWord_126576) baseStart_126576 baseEnd_126576 := by
    simpa [prefixWord, tailWord_126576, baseEnd_126576] using wordTrace_append hprefix tailTrace_126576
  have hstable : (prefixWord ++ tailWord_126576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126576).length < 2 ^ (prefixWord ++ tailWord_126576).sum := by decide
  have hdescent : baseEnd_126576 < baseStart_126576 := by decide
  rcases family_descends (prefixWord ++ tailWord_126576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126610 : List Nat := [3, 2, 3, 1, 3, 2, 1, 4]
def baseStart_126610 : Nat := 118140960795 + 126610 * 2 ^ 59
def prefixEnd_126610 : Nat := 4983230072969 + 3 ^ 40 * 126610 * 2
def baseEnd_126610 : Nat := 38525502616802886810511

theorem tailTrace_126610 : CollatzResearch.WordTrace tailWord_126610 prefixEnd_126610 38525502616802886810511 := by
  unfold tailWord_126610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1154461517830267027898321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3078564047547378741062189 1154461517830267027898321)
  ·
    refine ⟨865846138372700270923741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1154461517830267027898321 865846138372700270923741)
    ·
      refine ⟨324692301889762601596403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 865846138372700270923741 324692301889762601596403)
      ·
        refine ⟨487038452834643902394605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324692301889762601596403 487038452834643902394605)
        ·
          refine ⟨182639419812991463397977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487038452834643902394605 182639419812991463397977)
          ·
            refine ⟨136979564859743597548483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182639419812991463397977 136979564859743597548483)
            ·
              refine ⟨205469347289615396322725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136979564859743597548483 205469347289615396322725)
              ·
                refine ⟨38525502616802886810511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205469347289615396322725 38525502616802886810511)
                ·
                  rfl

theorem cell19_126610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_126610 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126610 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126610 prefixEnd_126610 := by exact prefixLift 126610
  have htrace : WordTrace (prefixWord ++ tailWord_126610) baseStart_126610 baseEnd_126610 := by
    simpa [prefixWord, tailWord_126610, baseEnd_126610] using wordTrace_append hprefix tailTrace_126610
  have hstable : (prefixWord ++ tailWord_126610).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126610).length < 2 ^ (prefixWord ++ tailWord_126610).sum := by decide
  have hdescent : baseEnd_126610 < baseStart_126610 := by decide
  rcases family_descends (prefixWord ++ tailWord_126610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126652 : List Nat := [2, 2, 2, 3, 1, 3, 6]
def baseStart_126652 : Nat := 118140960795 + 126652 * 2 ^ 59
def prefixEnd_126652 : Nat := 4983230072969 + 3 ^ 40 * 126652 * 2
def baseEnd_126652 : Nat := 12846094193253077959021

theorem tailTrace_126652 : CollatzResearch.WordTrace tailWord_126652 prefixEnd_126652 12846094193253077959021 := by
  unfold tailWord_126652
  simp only [CollatzResearch.WordTrace]
  refine ⟨2309688968584454642311105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3079585291445939523081473 2309688968584454642311105)
  ·
    refine ⟨1732266726438340981733329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2309688968584454642311105 1732266726438340981733329)
    ·
      refine ⟨1299200044828755736299997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1732266726438340981733329 1299200044828755736299997)
      ·
        refine ⟨487200016810783401112499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1299200044828755736299997 487200016810783401112499)
        ·
          refine ⟨730800025216175101668749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487200016810783401112499 730800025216175101668749)
          ·
            refine ⟨274050009456065663125781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 730800025216175101668749 274050009456065663125781)
            ·
              refine ⟨12846094193253077959021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 274050009456065663125781 12846094193253077959021)
              ·
                rfl

theorem cell19_126652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_126652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126652 prefixEnd_126652 := by exact prefixLift 126652
  have htrace : WordTrace (prefixWord ++ tailWord_126652) baseStart_126652 baseEnd_126652 := by
    simpa [prefixWord, tailWord_126652, baseEnd_126652] using wordTrace_append hprefix tailTrace_126652
  have hstable : (prefixWord ++ tailWord_126652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126652).length < 2 ^ (prefixWord ++ tailWord_126652).sum := by decide
  have hdescent : baseEnd_126652 < baseStart_126652 := by decide
  rcases family_descends (prefixWord ++ tailWord_126652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126684 : List Nat := [2, 2, 5, 1, 2, 2, 2, 3]
def baseStart_126684 : Nat := 118140960795 + 126684 * 2 ^ 59
def prefixEnd_126684 : Nat := 4983230072969 + 3 ^ 40 * 126684 * 2
def baseEnd_126684 : Nat := 38548019694392641165865

theorem tailTrace_126684 : CollatzResearch.WordTrace tailWord_126684 prefixEnd_126684 38548019694392641165865 := by
  unfold tailWord_126684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2310272536526489374893553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3080363382035319166524737 2310272536526489374893553)
  ·
    refine ⟨1732704402394867031170165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2310272536526489374893553 1732704402394867031170165)
    ·
      refine ⟨162441037724518784172203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1732704402394867031170165 162441037724518784172203)
      ·
        refine ⟨243661556586778176258305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162441037724518784172203 243661556586778176258305)
        ·
          refine ⟨182746167440083632193729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243661556586778176258305 182746167440083632193729)
          ·
            refine ⟨137059625580062724145297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182746167440083632193729 137059625580062724145297)
            ·
              refine ⟨102794719185047043108973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137059625580062724145297 102794719185047043108973)
              ·
                refine ⟨38548019694392641165865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102794719185047043108973 38548019694392641165865)
                ·
                  rfl

theorem cell19_126684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_126684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126684 prefixEnd_126684 := by exact prefixLift 126684
  have htrace : WordTrace (prefixWord ++ tailWord_126684) baseStart_126684 baseEnd_126684 := by
    simpa [prefixWord, tailWord_126684, baseEnd_126684] using wordTrace_append hprefix tailTrace_126684
  have hstable : (prefixWord ++ tailWord_126684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126684).length < 2 ^ (prefixWord ++ tailWord_126684).sum := by decide
  have hdescent : baseEnd_126684 < baseStart_126684 := by decide
  rcases family_descends (prefixWord ++ tailWord_126684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126711 : List Nat := [1, 1, 3, 1, 1, 1, 11]
def baseStart_126711 : Nat := 118140960795 + 126711 * 2 ^ 59
def prefixEnd_126711 : Nat := 4983230072969 + 3 ^ 40 * 126711 * 2
def baseEnd_126711 : Nat := 12852078461621526188597

theorem tailTrace_126711 : CollatzResearch.WordTrace tailWord_126711 prefixEnd_126711 12852078461621526188597 := by
  unfold tailWord_126711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621529843955162361019987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3081019895970108240679991 4621529843955162361019987)
  ·
    refine ⟨6932294765932743541529981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4621529843955162361019987 6932294765932743541529981)
    ·
      refine ⟨2599610537224778828073743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6932294765932743541529981 2599610537224778828073743)
      ·
        refine ⟨3899415805837168242110615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599610537224778828073743 3899415805837168242110615)
        ·
          refine ⟨5849123708755752363165923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3899415805837168242110615 5849123708755752363165923)
          ·
            refine ⟨8773685563133628544748885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849123708755752363165923 8773685563133628544748885)
            ·
              refine ⟨12852078461621526188597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8773685563133628544748885 12852078461621526188597)
              ·
                rfl

theorem cell19_126711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_126711 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126711 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126711 prefixEnd_126711 := by exact prefixLift 126711
  have htrace : WordTrace (prefixWord ++ tailWord_126711) baseStart_126711 baseEnd_126711 := by
    simpa [prefixWord, tailWord_126711, baseEnd_126711] using wordTrace_append hprefix tailTrace_126711
  have hstable : (prefixWord ++ tailWord_126711).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126711).length < 2 ^ (prefixWord ++ tailWord_126711).sum := by decide
  have hdescent : baseEnd_126711 < baseStart_126711 := by decide
  rcases family_descends (prefixWord ++ tailWord_126711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126728 : List Nat := [2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_126728 : Nat := 118140960795 + 126728 * 2 ^ 59
def prefixEnd_126728 : Nat := 4983230072969 + 3 ^ 40 * 126728 * 2
def baseEnd_126728 : Nat := 38561408227013576187967

theorem tailTrace_126728 : CollatzResearch.WordTrace tailWord_126728 prefixEnd_126728 38561408227013576187967 := by
  unfold tailWord_126728
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311074942446787132194419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3081433256595716176259225 2311074942446787132194419)
  ·
    refine ⟨3466612413670180698291629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2311074942446787132194419 3466612413670180698291629)
    ·
      refine ⟨1299979655126317761859361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3466612413670180698291629 1299979655126317761859361)
      ·
        refine ⟨974984741344738321394521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1299979655126317761859361 974984741344738321394521)
        ·
          refine ⟨731238556008553741045891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974984741344738321394521 731238556008553741045891)
          ·
            refine ⟨1096857834012830611568837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731238556008553741045891 1096857834012830611568837)
            ·
              refine ⟨205660843877405739669157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1096857834012830611568837 205660843877405739669157)
              ·
                refine ⟨38561408227013576187967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205660843877405739669157 38561408227013576187967)
                ·
                  rfl

theorem cell19_126728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_126728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126728 prefixEnd_126728 := by exact prefixLift 126728
  have htrace : WordTrace (prefixWord ++ tailWord_126728) baseStart_126728 baseEnd_126728 := by
    simpa [prefixWord, tailWord_126728, baseEnd_126728] using wordTrace_append hprefix tailTrace_126728
  have hstable : (prefixWord ++ tailWord_126728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126728).length < 2 ^ (prefixWord ++ tailWord_126728).sum := by decide
  have hdescent : baseEnd_126728 < baseStart_126728 := by decide
  rcases family_descends (prefixWord ++ tailWord_126728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126766 : List Nat := [4, 1, 3, 2, 9]
def baseStart_126766 : Nat := 118140960795 + 126766 * 2 ^ 59
def prefixEnd_126766 : Nat := 4983230072969 + 3 ^ 40 * 126766 * 2
def baseEnd_126766 : Nat := 1428628557431138790497

theorem tailTrace_126766 : CollatzResearch.WordTrace tailWord_126766 prefixEnd_126766 1428628557431138790497 := by
  unfold tailWord_126766
  simp only [CollatzResearch.WordTrace]
  refine ⟨577941982344488344284019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3082357239170604502848101 577941982344488344284019)
  ·
    refine ⟨866912973516732516426029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 577941982344488344284019 866912973516732516426029)
    ·
      refine ⟨325092365068774693659761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 866912973516732516426029 325092365068774693659761)
      ·
        refine ⟨243819273801581020244821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325092365068774693659761 243819273801581020244821)
        ·
          refine ⟨1428628557431138790497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 243819273801581020244821 1428628557431138790497)
          ·
            rfl

theorem cell19_126766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 9].length) (baseStart_126766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126766 prefixEnd_126766 := by exact prefixLift 126766
  have htrace : WordTrace (prefixWord ++ tailWord_126766) baseStart_126766 baseEnd_126766 := by
    simpa [prefixWord, tailWord_126766, baseEnd_126766] using wordTrace_append hprefix tailTrace_126766
  have hstable : (prefixWord ++ tailWord_126766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126766).length < 2 ^ (prefixWord ++ tailWord_126766).sum := by decide
  have hdescent : baseEnd_126766 < baseStart_126766 := by decide
  rcases family_descends (prefixWord ++ tailWord_126766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126783 : List Nat := [1, 1, 2, 2, 6, 2, 1, 4]
def baseStart_126783 : Nat := 118140960795 + 126783 * 2 ^ 59
def prefixEnd_126783 : Nat := 4983230072969 + 3 ^ 40 * 126783 * 2
def baseEnd_126783 : Nat := 38578143892789744965595

theorem tailTrace_126783 : CollatzResearch.WordTrace tailWord_126783 prefixEnd_126783 38578143892789744965595 := by
  unfold tailWord_126783
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624155899694318657641003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3082770599796212438427335 4624155899694318657641003)
  ·
    refine ⟨6936233849541477986461505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4624155899694318657641003 6936233849541477986461505)
    ·
      refine ⟨5202175387156108489846129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6936233849541477986461505 5202175387156108489846129)
      ·
        refine ⟨3901631540367081367384597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5202175387156108489846129 3901631540367081367384597)
        ·
          refine ⟨182888978454706939096153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3901631540367081367384597 182888978454706939096153)
          ·
            refine ⟨137166733841030204322115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182888978454706939096153 137166733841030204322115)
            ·
              refine ⟨205750100761545306483173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137166733841030204322115 205750100761545306483173)
              ·
                refine ⟨38578143892789744965595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205750100761545306483173 38578143892789744965595)
                ·
                  rfl

theorem cell19_126783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_126783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126783 prefixEnd_126783 := by exact prefixLift 126783
  have htrace : WordTrace (prefixWord ++ tailWord_126783) baseStart_126783 baseEnd_126783 := by
    simpa [prefixWord, tailWord_126783, baseEnd_126783] using wordTrace_append hprefix tailTrace_126783
  have hstable : (prefixWord ++ tailWord_126783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126783).length < 2 ^ (prefixWord ++ tailWord_126783).sum := by decide
  have hdescent : baseEnd_126783 < baseStart_126783 := by decide
  rcases family_descends (prefixWord ++ tailWord_126783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126802 : List Nat := [3, 2, 2, 1, 1, 4, 3, 3]
def baseStart_126802 : Nat := 118140960795 + 126802 * 2 ^ 59
def prefixEnd_126802 : Nat := 4983230072969 + 3 ^ 40 * 126802 * 2
def baseEnd_126802 : Nat := 38583925304603330543321

theorem tailTrace_126802 : CollatzResearch.WordTrace tailWord_126802 prefixEnd_126802 38583925304603330543321 := by
  unfold tailWord_126802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156212221656371225645665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3083232591083656601721773 1156212221656371225645665)
  ·
    refine ⟨867159166242278419234249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1156212221656371225645665 867159166242278419234249)
    ·
      refine ⟨650369374681708814425687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 867159166242278419234249 650369374681708814425687)
      ·
        refine ⟨975554062022563221638531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650369374681708814425687 975554062022563221638531)
        ·
          refine ⟨1463331093033844832457797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975554062022563221638531 1463331093033844832457797)
          ·
            refine ⟨274374579943845906085837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1463331093033844832457797 274374579943845906085837)
            ·
              refine ⟨102890467478942214782189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274374579943845906085837 102890467478942214782189)
              ·
                refine ⟨38583925304603330543321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102890467478942214782189 38583925304603330543321)
                ·
                  rfl

theorem cell19_126802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_126802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126802 prefixEnd_126802 := by exact prefixLift 126802
  have htrace : WordTrace (prefixWord ++ tailWord_126802) baseStart_126802 baseEnd_126802 := by
    simpa [prefixWord, tailWord_126802, baseEnd_126802] using wordTrace_append hprefix tailTrace_126802
  have hstable : (prefixWord ++ tailWord_126802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126802).length < 2 ^ (prefixWord ++ tailWord_126802).sum := by decide
  have hdescent : baseEnd_126802 < baseStart_126802 := by decide
  rcases family_descends (prefixWord ++ tailWord_126802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126937 : List Nat := [1, 2, 1, 2, 7, 6]
def baseStart_126937 : Nat := 118140960795 + 126937 * 2 ^ 59
def prefixEnd_126937 : Nat := 4983230072969 + 3 ^ 40 * 126937 * 2
def baseEnd_126937 : Nat := 4291667084107001949217

theorem tailTrace_126937 : CollatzResearch.WordTrace tailWord_126937 prefixEnd_126937 4291667084107001949217 := by
  unfold tailWord_126937
  simp only [CollatzResearch.WordTrace]
  refine ⟨4629772741136402958747065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3086515160757601972498043 4629772741136402958747065)
  ·
    refine ⟨3472329555852302219060299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4629772741136402958747065 3472329555852302219060299)
    ·
      refine ⟨5208494333778453328590449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3472329555852302219060299 5208494333778453328590449)
      ·
        refine ⟨3906370750333839996442837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5208494333778453328590449 3906370750333839996442837)
        ·
          refine ⟨91555564460949374916629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3906370750333839996442837 91555564460949374916629)
          ·
            refine ⟨4291667084107001949217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91555564460949374916629 4291667084107001949217)
            ·
              rfl

theorem cell19_126937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 6].length) (baseStart_126937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_126937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_126937 prefixEnd_126937 := by exact prefixLift 126937
  have htrace : WordTrace (prefixWord ++ tailWord_126937) baseStart_126937 baseEnd_126937 := by
    simpa [prefixWord, tailWord_126937, baseEnd_126937] using wordTrace_append hprefix tailTrace_126937
  have hstable : (prefixWord ++ tailWord_126937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126937).length < 2 ^ (prefixWord ++ tailWord_126937).sum := by decide
  have hdescent : baseEnd_126937 < baseStart_126937 := by decide
  rcases family_descends (prefixWord ++ tailWord_126937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127032 : List Nat := [2, 1, 2, 1, 6, 1, 1, 5]
def baseStart_127032 : Nat := 118140960795 + 127032 * 2 ^ 59
def prefixEnd_127032 : Nat := 4983230072969 + 3 ^ 40 * 127032 * 2
def baseEnd_127032 : Nat := 38653910816030945431583

theorem tailTrace_127032 : CollatzResearch.WordTrace tailWord_127032 prefixEnd_127032 38653910816030945431583 := by
  unfold tailWord_127032
  simp only [CollatzResearch.WordTrace]
  refine ⟨2316618837896117091727675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3088825117194822788970233 2316618837896117091727675)
  ·
    refine ⟨3474928256844175637591513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2316618837896117091727675 3474928256844175637591513)
    ·
      refine ⟨2606196192633131728193635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3474928256844175637591513 2606196192633131728193635)
      ·
        refine ⟨3909294288949697592290453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606196192633131728193635 3909294288949697592290453)
        ·
          refine ⟨183248169794517074638615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3909294288949697592290453 183248169794517074638615)
          ·
            refine ⟨274872254691775611957923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183248169794517074638615 274872254691775611957923)
            ·
              refine ⟨412308382037663417936885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274872254691775611957923 412308382037663417936885)
              ·
                refine ⟨38653910816030945431583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 412308382037663417936885 38653910816030945431583)
                ·
                  rfl

theorem cell19_127032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_127032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127032 prefixEnd_127032 := by exact prefixLift 127032
  have htrace : WordTrace (prefixWord ++ tailWord_127032) baseStart_127032 baseEnd_127032 := by
    simpa [prefixWord, tailWord_127032, baseEnd_127032] using wordTrace_append hprefix tailTrace_127032
  have hstable : (prefixWord ++ tailWord_127032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127032).length < 2 ^ (prefixWord ++ tailWord_127032).sum := by decide
  have hdescent : baseEnd_127032 < baseStart_127032 := by decide
  rcases family_descends (prefixWord ++ tailWord_127032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127072 : List Nat := [2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_127072 : Nat := 118140960795 + 127072 * 2 ^ 59
def prefixEnd_127072 : Nat := 4983230072969 + 3 ^ 40 * 127072 * 2
def baseEnd_127072 : Nat := 38666082209322704542585

theorem tailTrace_127072 : CollatzResearch.WordTrace tailWord_127072 prefixEnd_127072 38666082209322704542585 := by
  unfold tailWord_127072
  simp only [CollatzResearch.WordTrace]
  refine ⟨2317348297823660507455735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3089797730431547343274313 2317348297823660507455735)
  ·
    refine ⟨3476022446735490761183603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2317348297823660507455735 3476022446735490761183603)
    ·
      refine ⟨5214033670103236141775405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3476022446735490761183603 5214033670103236141775405)
      ·
        refine ⟨1955262626288713553165777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5214033670103236141775405 1955262626288713553165777)
        ·
          refine ⟨1466446969716535164874333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1955262626288713553165777 1466446969716535164874333)
          ·
            refine ⟨549917613643700686827875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1466446969716535164874333 549917613643700686827875)
            ·
              refine ⟨824876420465551030241813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549917613643700686827875 824876420465551030241813)
              ·
                refine ⟨38666082209322704542585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 824876420465551030241813 38666082209322704542585)
                ·
                  rfl

theorem cell19_127072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_127072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127072 prefixEnd_127072 := by exact prefixLift 127072
  have htrace : WordTrace (prefixWord ++ tailWord_127072) baseStart_127072 baseEnd_127072 := by
    simpa [prefixWord, tailWord_127072, baseEnd_127072] using wordTrace_append hprefix tailTrace_127072
  have hstable : (prefixWord ++ tailWord_127072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127072).length < 2 ^ (prefixWord ++ tailWord_127072).sum := by decide
  have hdescent : baseEnd_127072 < baseStart_127072 := by decide
  rcases family_descends (prefixWord ++ tailWord_127072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127239 : List Nat := [1, 1, 4, 5, 1, 1, 2, 4]
def baseStart_127239 : Nat := 118140960795 + 127239 * 2 ^ 59
def prefixEnd_127239 : Nat := 4983230072969 + 3 ^ 40 * 127239 * 2
def baseEnd_127239 : Nat := 38716897776315798831019

theorem tailTrace_127239 : CollatzResearch.WordTrace tailWord_127239 prefixEnd_127239 38716897776315798831019 := by
  unfold tailWord_127239
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640787586042308536240771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3093858390694872357493847 4640787586042308536240771)
  ·
    refine ⟨6961181379063462804361157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4640787586042308536240771 6961181379063462804361157)
    ·
      refine ⟨1305221508574399275817717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6961181379063462804361157 1305221508574399275817717)
      ·
        refine ⟨122364516428849932107911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1305221508574399275817717 122364516428849932107911)
        ·
          refine ⟨183546774643274898161867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122364516428849932107911 183546774643274898161867)
          ·
            refine ⟨275320161964912347242801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183546774643274898161867 275320161964912347242801)
            ·
              refine ⟨206490121473684260432101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275320161964912347242801 206490121473684260432101)
              ·
                refine ⟨38716897776315798831019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206490121473684260432101 38716897776315798831019)
                ·
                  rfl

theorem cell19_127239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 4].length) (baseStart_127239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127239 prefixEnd_127239 := by exact prefixLift 127239
  have htrace : WordTrace (prefixWord ++ tailWord_127239) baseStart_127239 baseEnd_127239 := by
    simpa [prefixWord, tailWord_127239, baseEnd_127239] using wordTrace_append hprefix tailTrace_127239
  have hstable : (prefixWord ++ tailWord_127239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127239).length < 2 ^ (prefixWord ++ tailWord_127239).sum := by decide
  have hdescent : baseEnd_127239 < baseStart_127239 := by decide
  rcases family_descends (prefixWord ++ tailWord_127239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127243 : List Nat := [1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_127243 : Nat := 118140960795 + 127243 * 2 ^ 59
def prefixEnd_127243 : Nat := 4983230072969 + 3 ^ 40 * 127243 * 2
def baseEnd_127243 : Nat := 38718114915644974742119

theorem tailTrace_127243 : CollatzResearch.WordTrace tailWord_127243 prefixEnd_127243 38718114915644974742119 := by
  unfold tailWord_127243
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640933478027817219386383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3093955652018544812924255 4640933478027817219386383)
  ·
    refine ⟨6961400217041725829079575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4640933478027817219386383 6961400217041725829079575)
    ·
      refine ⟨10442100325562588743619363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6961400217041725829079575 10442100325562588743619363)
      ·
        refine ⟨15663150488343883115429045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10442100325562588743619363 15663150488343883115429045)
        ·
          refine ⟨1468420358282239042071473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15663150488343883115429045 1468420358282239042071473)
          ·
            refine ⟨1101315268711679281553605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1468420358282239042071473 1101315268711679281553605)
            ·
              refine ⟨206496612883439865291301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1101315268711679281553605 206496612883439865291301)
              ·
                refine ⟨38718114915644974742119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206496612883439865291301 38718114915644974742119)
                ·
                  rfl

theorem cell19_127243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_127243 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127243 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127243 prefixEnd_127243 := by exact prefixLift 127243
  have htrace : WordTrace (prefixWord ++ tailWord_127243) baseStart_127243 baseEnd_127243 := by
    simpa [prefixWord, tailWord_127243, baseEnd_127243] using wordTrace_append hprefix tailTrace_127243
  have hstable : (prefixWord ++ tailWord_127243).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127243).length < 2 ^ (prefixWord ++ tailWord_127243).sum := by decide
  have hdescent : baseEnd_127243 < baseStart_127243 := by decide
  rcases family_descends (prefixWord ++ tailWord_127243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127277 : List Nat := [1, 5, 3, 1, 3, 6]
def baseStart_127277 : Nat := 118140960795 + 127277 * 2 ^ 59
def prefixEnd_127277 : Nat := 4983230072969 + 3 ^ 40 * 127277 * 2
def baseEnd_127277 : Nat := 4303162288882552220719

theorem tailTrace_127277 : CollatzResearch.WordTrace tailWord_127277 prefixEnd_127277 4303162288882552220719 := by
  unfold tailWord_127277
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642173559904641026124085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3094782373269760684082723 4642173559904641026124085)
  ·
    refine ⟨435203771241060096199133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4642173559904641026124085 435203771241060096199133)
    ·
      refine ⟨163201414215397536074675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435203771241060096199133 163201414215397536074675)
      ·
        refine ⟨244802121323096304112013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163201414215397536074675 244802121323096304112013)
        ·
          refine ⟨91800795496161114042005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244802121323096304112013 91800795496161114042005)
          ·
            refine ⟨4303162288882552220719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91800795496161114042005 4303162288882552220719)
            ·
              rfl

theorem cell19_127277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 6].length) (baseStart_127277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127277 prefixEnd_127277 := by exact prefixLift 127277
  have htrace : WordTrace (prefixWord ++ tailWord_127277) baseStart_127277 baseEnd_127277 := by
    simpa [prefixWord, tailWord_127277, baseEnd_127277] using wordTrace_append hprefix tailTrace_127277
  have hstable : (prefixWord ++ tailWord_127277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127277).length < 2 ^ (prefixWord ++ tailWord_127277).sum := by decide
  have hdescent : baseEnd_127277 < baseStart_127277 := by decide
  rcases family_descends (prefixWord ++ tailWord_127277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127281 : List Nat := [1, 2, 2, 3, 4, 7]
def baseStart_127281 : Nat := 118140960795 + 127281 * 2 ^ 59
def prefixEnd_127281 : Nat := 4983230072969 + 3 ^ 40 * 127281 * 2
def baseEnd_127281 : Nat := 4303297526585793988619

theorem tailTrace_127281 : CollatzResearch.WordTrace tailWord_127281 prefixEnd_127281 4303297526585793988619 := by
  unfold tailWord_127281
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642319451890149709269697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3094879634593433139513131 4642319451890149709269697)
  ·
    refine ⟨3481739588917612281952273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4642319451890149709269697 3481739588917612281952273)
    ·
      refine ⟨2611304691688209211464205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3481739588917612281952273 2611304691688209211464205)
      ·
        refine ⟨979239259383078454299077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2611304691688209211464205 979239259383078454299077)
        ·
          refine ⟨183607361134327210181077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 979239259383078454299077 183607361134327210181077)
          ·
            refine ⟨4303297526585793988619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 183607361134327210181077 4303297526585793988619)
            ·
              rfl

theorem cell19_127281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 7].length) (baseStart_127281 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127281 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127281 prefixEnd_127281 := by exact prefixLift 127281
  have htrace : WordTrace (prefixWord ++ tailWord_127281) baseStart_127281 baseEnd_127281 := by
    simpa [prefixWord, tailWord_127281, baseEnd_127281] using wordTrace_append hprefix tailTrace_127281
  have hstable : (prefixWord ++ tailWord_127281).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127281).length < 2 ^ (prefixWord ++ tailWord_127281).sum := by decide
  have hdescent : baseEnd_127281 < baseStart_127281 := by decide
  rcases family_descends (prefixWord ++ tailWord_127281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127370 : List Nat := [3, 1, 2, 5, 1, 2, 2, 3]
def baseStart_127370 : Nat := 118140960795 + 127370 * 2 ^ 59
def prefixEnd_127370 : Nat := 4983230072969 + 3 ^ 40 * 127370 * 2
def baseEnd_127370 : Nat := 38756759089346309919551

theorem tailTrace_127370 : CollatzResearch.WordTrace tailWord_127370 prefixEnd_127370 38756759089346309919551 := by
  unfold tailWord_127370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161391387141929477314891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3097043699045145272839709 1161391387141929477314891)
  ·
    refine ⟨1742087080712894215972337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1161391387141929477314891 1742087080712894215972337)
    ·
      refine ⟨1306565310534670661979253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1742087080712894215972337 1306565310534670661979253)
      ·
        refine ⟨122490497862625374560555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1306565310534670661979253 122490497862625374560555)
        ·
          refine ⟨183735746793938061840833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122490497862625374560555 183735746793938061840833)
          ·
            refine ⟨137801810095453546380625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183735746793938061840833 137801810095453546380625)
            ·
              refine ⟨103351357571590159785469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137801810095453546380625 103351357571590159785469)
              ·
                refine ⟨38756759089346309919551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103351357571590159785469 38756759089346309919551)
                ·
                  rfl

theorem cell19_127370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_127370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127370 prefixEnd_127370 := by exact prefixLift 127370
  have htrace : WordTrace (prefixWord ++ tailWord_127370) baseStart_127370 baseEnd_127370 := by
    simpa [prefixWord, tailWord_127370, baseEnd_127370] using wordTrace_append hprefix tailTrace_127370
  have hstable : (prefixWord ++ tailWord_127370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127370).length < 2 ^ (prefixWord ++ tailWord_127370).sum := by decide
  have hdescent : baseEnd_127370 < baseStart_127370 := by decide
  rcases family_descends (prefixWord ++ tailWord_127370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127374 : List Nat := [4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_127374 : Nat := 118140960795 + 127374 * 2 ^ 59
def prefixEnd_127374 : Nat := 4983230072969 + 3 ^ 40 * 127374 * 2
def baseEnd_127374 : Nat := 38757976228675485830651

theorem tailTrace_127374 : CollatzResearch.WordTrace tailWord_127374 prefixEnd_127374 38757976228675485830651 := by
  unfold tailWord_127374
  simp only [CollatzResearch.WordTrace]
  refine ⟨580713930069153324050647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3097140960368817728270117 580713930069153324050647)
  ·
    refine ⟨871070895103729986075971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580713930069153324050647 871070895103729986075971)
    ·
      refine ⟨1306606342655594979113957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871070895103729986075971 1306606342655594979113957)
      ·
        refine ⟨244988689247924058583867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1306606342655594979113957 244988689247924058583867)
        ·
          refine ⟨367483033871886087875801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244988689247924058583867 367483033871886087875801)
          ·
            refine ⟨275612275403914565906851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367483033871886087875801 275612275403914565906851)
            ·
              refine ⟨413418413105871848860277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275612275403914565906851 413418413105871848860277)
              ·
                refine ⟨38757976228675485830651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 413418413105871848860277 38757976228675485830651)
                ·
                  rfl

theorem cell19_127374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_127374 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127374 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127374 prefixEnd_127374 := by exact prefixLift 127374
  have htrace : WordTrace (prefixWord ++ tailWord_127374) baseStart_127374 baseEnd_127374 := by
    simpa [prefixWord, tailWord_127374, baseEnd_127374] using wordTrace_append hprefix tailTrace_127374
  have hstable : (prefixWord ++ tailWord_127374).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127374).length < 2 ^ (prefixWord ++ tailWord_127374).sum := by decide
  have hdescent : baseEnd_127374 < baseStart_127374 := by decide
  rcases family_descends (prefixWord ++ tailWord_127374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127395 : List Nat := [1, 1, 1, 4, 1, 6, 5]
def baseStart_127395 : Nat := 118140960795 + 127395 * 2 ^ 59
def prefixEnd_127395 : Nat := 4983230072969 + 3 ^ 40 * 127395 * 2
def baseEnd_127395 : Nat := 12921455403384553121309

theorem tailTrace_127395 : CollatzResearch.WordTrace tailWord_127395 prefixEnd_127395 12921455403384553121309 := by
  unfold tailWord_127395
  simp only [CollatzResearch.WordTrace]
  refine ⟨4646477373477147178919639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3097651582318098119279759 4646477373477147178919639)
  ·
    refine ⟨6969716060215720768379459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4646477373477147178919639 6969716060215720768379459)
    ·
      refine ⟨10454574090323581152569189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6969716060215720768379459 10454574090323581152569189)
      ·
        refine ⟨1960232641935671466106723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10454574090323581152569189 1960232641935671466106723)
        ·
          refine ⟨2940348962903507199160085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1960232641935671466106723 2940348962903507199160085)
          ·
            refine ⟨137828857636101899960629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2940348962903507199160085 137828857636101899960629)
            ·
              refine ⟨12921455403384553121309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137828857636101899960629 12921455403384553121309)
              ·
                rfl

theorem cell19_127395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_127395 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127395 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127395 prefixEnd_127395 := by exact prefixLift 127395
  have htrace : WordTrace (prefixWord ++ tailWord_127395) baseStart_127395 baseEnd_127395 := by
    simpa [prefixWord, tailWord_127395, baseEnd_127395] using wordTrace_append hprefix tailTrace_127395
  have hstable : (prefixWord ++ tailWord_127395).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127395).length < 2 ^ (prefixWord ++ tailWord_127395).sum := by decide
  have hdescent : baseEnd_127395 < baseStart_127395 := by decide
  rcases family_descends (prefixWord ++ tailWord_127395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127469 : List Nat := [1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_127469 : Nat := 118140960795 + 127469 * 2 ^ 59
def prefixEnd_127469 : Nat := 4983230072969 + 3 ^ 40 * 127469 * 2
def baseEnd_127469 : Nat := 38786883287743413719281

theorem tailTrace_127469 : CollatzResearch.WordTrace tailWord_127469 prefixEnd_127469 38786883287743413719281 := by
  unfold tailWord_127469
  simp only [CollatzResearch.WordTrace]
  refine ⟨4649176375209057817113461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3099450916806038544742307 4649176375209057817113461)
  ·
    refine ⟨435860285175849170354387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4649176375209057817113461 435860285175849170354387)
    ·
      refine ⟨653790427763773755531581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435860285175849170354387 653790427763773755531581)
      ·
        refine ⟨245171410411415158324343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653790427763773755531581 245171410411415158324343)
        ·
          refine ⟨367757115617122737486515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245171410411415158324343 367757115617122737486515)
          ·
            refine ⟨551635673425684106229773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367757115617122737486515 551635673425684106229773)
            ·
              refine ⟨206863377534631539836165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 551635673425684106229773 206863377534631539836165)
              ·
                refine ⟨38786883287743413719281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206863377534631539836165 38786883287743413719281)
                ·
                  rfl

theorem cell19_127469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_127469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127469 prefixEnd_127469 := by exact prefixLift 127469
  have htrace : WordTrace (prefixWord ++ tailWord_127469) baseStart_127469 baseEnd_127469 := by
    simpa [prefixWord, tailWord_127469, baseEnd_127469] using wordTrace_append hprefix tailTrace_127469
  have hstable : (prefixWord ++ tailWord_127469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127469).length < 2 ^ (prefixWord ++ tailWord_127469).sum := by decide
  have hdescent : baseEnd_127469 < baseStart_127469 := by decide
  rcases family_descends (prefixWord ++ tailWord_127469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127585 : List Nat := [1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_127585 : Nat := 118140960795 + 127585 * 2 ^ 59
def prefixEnd_127585 : Nat := 4983230072969 + 3 ^ 40 * 127585 * 2
def baseEnd_127585 : Nat := 38822180328289515141187

theorem tailTrace_127585 : CollatzResearch.WordTrace tailWord_127585 prefixEnd_127585 38822180328289515141187 := by
  unfold tailWord_127585
  simp only [CollatzResearch.WordTrace]
  refine ⟨4653407242788809628336209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3102271495192539752224139 4653407242788809628336209)
  ·
    refine ⟨3490055432091607221252157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4653407242788809628336209 3490055432091607221252157)
    ·
      refine ⟨1308770787034352707969559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3490055432091607221252157 1308770787034352707969559)
      ·
        refine ⟨1963156180551529061954339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1308770787034352707969559 1963156180551529061954339)
        ·
          refine ⟨2944734270827293592931509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963156180551529061954339 2944734270827293592931509)
          ·
            refine ⟨276068837890058774337329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2944734270827293592931509 276068837890058774337329)
            ·
              refine ⟨207051628417544080752997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276068837890058774337329 207051628417544080752997)
              ·
                refine ⟨38822180328289515141187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207051628417544080752997 38822180328289515141187)
                ·
                  rfl

theorem cell19_127585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_127585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127585 prefixEnd_127585 := by exact prefixLift 127585
  have htrace : WordTrace (prefixWord ++ tailWord_127585) baseStart_127585 baseEnd_127585 := by
    simpa [prefixWord, tailWord_127585, baseEnd_127585] using wordTrace_append hprefix tailTrace_127585
  have hstable : (prefixWord ++ tailWord_127585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127585).length < 2 ^ (prefixWord ++ tailWord_127585).sum := by decide
  have hdescent : baseEnd_127585 < baseStart_127585 := by decide
  rcases family_descends (prefixWord ++ tailWord_127585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127716 : List Nat := [2, 3, 1, 1, 1, 6, 2, 3]
def baseStart_127716 : Nat := 118140960795 + 127716 * 2 ^ 59
def prefixEnd_127716 : Nat := 4983230072969 + 3 ^ 40 * 127716 * 2
def baseEnd_127716 : Nat := 38862041641320026229719

theorem tailTrace_127716 : CollatzResearch.WordTrace tailWord_127716 prefixEnd_127716 38862041641320026229719 := by
  unfold tailWord_127716
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329092602657109500677501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3105456803542812667570001 2329092602657109500677501)
  ·
    refine ⟨873409725996416062754063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2329092602657109500677501 873409725996416062754063)
    ·
      refine ⟨1310114588994624094131095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 873409725996416062754063 1310114588994624094131095)
      ·
        refine ⟨1965171883491936141196643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310114588994624094131095 1965171883491936141196643)
        ·
          refine ⟨2947757825237904211794965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1965171883491936141196643 2947757825237904211794965)
          ·
            refine ⟨138176148058026759927889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2947757825237904211794965 138176148058026759927889)
            ·
              refine ⟨103632111043520069945917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138176148058026759927889 103632111043520069945917)
              ·
                refine ⟨38862041641320026229719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103632111043520069945917 38862041641320026229719)
                ·
                  rfl

theorem cell19_127716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_127716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127716 prefixEnd_127716 := by exact prefixLift 127716
  have htrace : WordTrace (prefixWord ++ tailWord_127716) baseStart_127716 baseEnd_127716 := by
    simpa [prefixWord, tailWord_127716, baseEnd_127716] using wordTrace_append hprefix tailTrace_127716
  have hstable : (prefixWord ++ tailWord_127716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127716).length < 2 ^ (prefixWord ++ tailWord_127716).sum := by decide
  have hdescent : baseEnd_127716 < baseStart_127716 := by decide
  rcases family_descends (prefixWord ++ tailWord_127716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127777 : List Nat := [1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_127777 : Nat := 118140960795 + 127777 * 2 ^ 59
def prefixEnd_127777 : Nat := 4983230072969 + 3 ^ 40 * 127777 * 2
def baseEnd_127777 : Nat := 38880603016089958873997

theorem tailTrace_127777 : CollatzResearch.WordTrace tailWord_127777 prefixEnd_127777 38880603016089958873997 := by
  unfold tailWord_127777
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660410058093226419325585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3106940038728817612883723 4660410058093226419325585)
  ·
    refine ⟨3495307543569919814494189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4660410058093226419325585 3495307543569919814494189)
    ·
      refine ⟨1310740328838719930435321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3495307543569919814494189 1310740328838719930435321)
      ·
        refine ⟨983055246629039947826491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1310740328838719930435321 983055246629039947826491)
        ·
          refine ⟨1474582869943559921739737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983055246629039947826491 1474582869943559921739737)
          ·
            refine ⟨1105937152457669941304803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474582869943559921739737 1105937152457669941304803)
            ·
              refine ⟨1658905728686504911957205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105937152457669941304803 1658905728686504911957205)
              ·
                refine ⟨38880603016089958873997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1658905728686504911957205 38880603016089958873997)
                ·
                  rfl

theorem cell19_127777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_127777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127777 prefixEnd_127777 := by exact prefixLift 127777
  have htrace : WordTrace (prefixWord ++ tailWord_127777) baseStart_127777 baseEnd_127777 := by
    simpa [prefixWord, tailWord_127777, baseEnd_127777] using wordTrace_append hprefix tailTrace_127777
  have hstable : (prefixWord ++ tailWord_127777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127777).length < 2 ^ (prefixWord ++ tailWord_127777).sum := by decide
  have hdescent : baseEnd_127777 < baseStart_127777 := by decide
  rcases family_descends (prefixWord ++ tailWord_127777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127809 : List Nat := [1, 2, 5, 3, 1, 2, 1, 4]
def baseStart_127809 : Nat := 118140960795 + 127809 * 2 ^ 59
def prefixEnd_127809 : Nat := 4983230072969 + 3 ^ 40 * 127809 * 2
def baseEnd_127809 : Nat := 38890340130723366162799

theorem tailTrace_127809 : CollatzResearch.WordTrace tailWord_127809 prefixEnd_127809 38890340130723366162799 := by
  unfold tailWord_127809
  simp only [CollatzResearch.WordTrace]
  refine ⟨4661577193977295884490481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3107718129318197256326987 4661577193977295884490481)
  ·
    refine ⟨3496182895482971913367861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4661577193977295884490481 3496182895482971913367861)
    ·
      refine ⟨327767146451528616878237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3496182895482971913367861 327767146451528616878237)
      ·
        refine ⟨122912679919323231329339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327767146451528616878237 122912679919323231329339)
        ·
          refine ⟨184369019878984846994009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122912679919323231329339 184369019878984846994009)
          ·
            refine ⟨138276764909238635245507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184369019878984846994009 138276764909238635245507)
            ·
              refine ⟨207415147363857952868261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138276764909238635245507 207415147363857952868261)
              ·
                refine ⟨38890340130723366162799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207415147363857952868261 38890340130723366162799)
                ·
                  rfl

theorem cell19_127809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 4].length) (baseStart_127809 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127809 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127809 prefixEnd_127809 := by exact prefixLift 127809
  have htrace : WordTrace (prefixWord ++ tailWord_127809) baseStart_127809 baseEnd_127809 := by
    simpa [prefixWord, tailWord_127809, baseEnd_127809] using wordTrace_append hprefix tailTrace_127809
  have hstable : (prefixWord ++ tailWord_127809).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127809).length < 2 ^ (prefixWord ++ tailWord_127809).sum := by decide
  have hdescent : baseEnd_127809 < baseStart_127809 := by decide
  rcases family_descends (prefixWord ++ tailWord_127809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127929 : List Nat := [1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_127929 : Nat := 118140960795 + 127929 * 2 ^ 59
def prefixEnd_127929 : Nat := 4983230072969 + 3 ^ 40 * 127929 * 2
def baseEnd_127929 : Nat := 38926854310598643495805

theorem tailTrace_127929 : CollatzResearch.WordTrace tailWord_127929 prefixEnd_127929 38926854310598643495805 := by
  unfold tailWord_127929
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665953953542556378858841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3110635969028370919239227 4665953953542556378858841)
  ·
    refine ⟨3499465465156917284144131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4665953953542556378858841 3499465465156917284144131)
    ·
      refine ⟨5249198197735375926216197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3499465465156917284144131 5249198197735375926216197)
      ·
        refine ⟨984224662075382986165537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5249198197735375926216197 984224662075382986165537)
        ·
          refine ⟨738168496556537239624153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984224662075382986165537 738168496556537239624153)
          ·
            refine ⟨553626372417402929718115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738168496556537239624153 553626372417402929718115)
            ·
              refine ⟨830439558626104394577173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553626372417402929718115 830439558626104394577173)
              ·
                refine ⟨38926854310598643495805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 830439558626104394577173 38926854310598643495805)
                ·
                  rfl

theorem cell19_127929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_127929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127929 prefixEnd_127929 := by exact prefixLift 127929
  have htrace : WordTrace (prefixWord ++ tailWord_127929) baseStart_127929 baseEnd_127929 := by
    simpa [prefixWord, tailWord_127929, baseEnd_127929] using wordTrace_append hprefix tailTrace_127929
  have hstable : (prefixWord ++ tailWord_127929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127929).length < 2 ^ (prefixWord ++ tailWord_127929).sum := by decide
  have hdescent : baseEnd_127929 < baseStart_127929 := by decide
  rcases family_descends (prefixWord ++ tailWord_127929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127948 : List Nat := [2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_127948 : Nat := 118140960795 + 127948 * 2 ^ 59
def prefixEnd_127948 : Nat := 4983230072969 + 3 ^ 40 * 127948 * 2
def baseEnd_127948 : Nat := 38932635722412229073531

theorem tailTrace_127948 : CollatzResearch.WordTrace tailWord_127948 prefixEnd_127948 38932635722412229073531 := by
  unfold tailWord_127948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333323470236861311900249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3111097960315815082533665 2333323470236861311900249)
  ·
    refine ⟨1749992602677645983925187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2333323470236861311900249 1749992602677645983925187)
    ·
      refine ⟨2624988904016468975887781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1749992602677645983925187 2624988904016468975887781)
      ·
        refine ⟨492185419503087932978959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2624988904016468975887781 492185419503087932978959)
        ·
          refine ⟨738278129254631899468439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492185419503087932978959 738278129254631899468439)
          ·
            refine ⟨1107417193881947849202659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738278129254631899468439 1107417193881947849202659)
            ·
              refine ⟨1661125790822921773803989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107417193881947849202659 1661125790822921773803989)
              ·
                refine ⟨38932635722412229073531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1661125790822921773803989 38932635722412229073531)
                ·
                  rfl

theorem cell19_127948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_127948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127948 prefixEnd_127948 := by exact prefixLift 127948
  have htrace : WordTrace (prefixWord ++ tailWord_127948) baseStart_127948 baseEnd_127948 := by
    simpa [prefixWord, tailWord_127948, baseEnd_127948] using wordTrace_append hprefix tailTrace_127948
  have hstable : (prefixWord ++ tailWord_127948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127948).length < 2 ^ (prefixWord ++ tailWord_127948).sum := by decide
  have hdescent : baseEnd_127948 < baseStart_127948 := by decide
  rcases family_descends (prefixWord ++ tailWord_127948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127967 : List Nat := [1, 1, 2, 3, 5, 7]
def baseStart_127967 : Nat := 118140960795 + 127967 * 2 ^ 59
def prefixEnd_127967 : Nat := 4983230072969 + 3 ^ 40 * 127967 * 2
def baseEnd_127967 : Nat := 4326490792691757183473

theorem tailTrace_127967 : CollatzResearch.WordTrace tailWord_127967 prefixEnd_127967 4326490792691757183473 := by
  unfold tailWord_127967
  simp only [CollatzResearch.WordTrace]
  refine ⟨4667339927404888868742155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3111559951603259245828103 4667339927404888868742155)
  ·
    refine ⟨7001009891107333303113233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4667339927404888868742155 7001009891107333303113233)
    ·
      refine ⟨5250757418330499977334925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7001009891107333303113233 5250757418330499977334925)
      ·
        refine ⟨1969034031873937491500597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5250757418330499977334925 1969034031873937491500597)
        ·
          refine ⟨184596940488181639828181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1969034031873937491500597 184596940488181639828181)
          ·
            refine ⟨4326490792691757183473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 184596940488181639828181 4326490792691757183473)
            ·
              rfl

theorem cell19_127967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 7].length) (baseStart_127967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127967 prefixEnd_127967 := by exact prefixLift 127967
  have htrace : WordTrace (prefixWord ++ tailWord_127967) baseStart_127967 baseEnd_127967 := by
    simpa [prefixWord, tailWord_127967, baseEnd_127967] using wordTrace_append hprefix tailTrace_127967
  have hstable : (prefixWord ++ tailWord_127967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127967).length < 2 ^ (prefixWord ++ tailWord_127967).sum := by decide
  have hdescent : baseEnd_127967 < baseStart_127967 := by decide
  rcases family_descends (prefixWord ++ tailWord_127967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127982 : List Nat := [4, 1, 2, 1, 4, 2, 1, 4]
def baseStart_127982 : Nat := 118140960795 + 127982 * 2 ^ 59
def prefixEnd_127982 : Nat := 4983230072969 + 3 ^ 40 * 127982 * 2
def baseEnd_127982 : Nat := 38942981406710224317883

theorem tailTrace_127982 : CollatzResearch.WordTrace tailWord_127982 prefixEnd_127982 38942981406710224317883 := by
  unfold tailWord_127982
  simp only [CollatzResearch.WordTrace]
  refine ⟨583485877793818303817275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3111924681567030953692133 583485877793818303817275)
  ·
    refine ⟨875228816690727455725913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 583485877793818303817275 875228816690727455725913)
    ·
      refine ⟨656421612518045591794435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 875228816690727455725913 656421612518045591794435)
      ·
        refine ⟨984632418777068387691653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656421612518045591794435 984632418777068387691653)
        ·
          refine ⟨184618578520700322692185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 984632418777068387691653 184618578520700322692185)
          ·
            refine ⟨138463933890525242019139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184618578520700322692185 138463933890525242019139)
            ·
              refine ⟨207695900835787863028709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138463933890525242019139 207695900835787863028709)
              ·
                refine ⟨38942981406710224317883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207695900835787863028709 38942981406710224317883)
                ·
                  rfl

theorem cell19_127982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_127982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_127982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_127982 prefixEnd_127982 := by exact prefixLift 127982
  have htrace : WordTrace (prefixWord ++ tailWord_127982) baseStart_127982 baseEnd_127982 := by
    simpa [prefixWord, tailWord_127982, baseEnd_127982] using wordTrace_append hprefix tailTrace_127982
  have hstable : (prefixWord ++ tailWord_127982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127982).length < 2 ^ (prefixWord ++ tailWord_127982).sum := by decide
  have hdescent : baseEnd_127982 < baseStart_127982 := by decide
  rcases family_descends (prefixWord ++ tailWord_127982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128018 : List Nat := [3, 2, 5, 1, 1, 1, 6]
def baseStart_128018 : Nat := 118140960795 + 128018 * 2 ^ 59
def prefixEnd_128018 : Nat := 4983230072969 + 3 ^ 40 * 128018 * 2
def baseEnd_128018 : Nat := 12984645220224269172595

theorem tailTrace_128018 : CollatzResearch.WordTrace tailWord_128018 prefixEnd_128018 12984645220224269172595 := by
  unfold tailWord_128018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167300012555031144712177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3112800033480083052565805 1167300012555031144712177)
  ·
    refine ⟨875475009416273358534133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1167300012555031144712177 875475009416273358534133)
    ·
      refine ⟨82075782132775627362575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 875475009416273358534133 82075782132775627362575)
      ·
        refine ⟨123113673199163441043863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82075782132775627362575 123113673199163441043863)
        ·
          refine ⟨184670509798745161565795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123113673199163441043863 184670509798745161565795)
          ·
            refine ⟨277005764698117742348693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184670509798745161565795 277005764698117742348693)
            ·
              refine ⟨12984645220224269172595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277005764698117742348693 12984645220224269172595)
              ·
                rfl

theorem cell19_128018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 6].length) (baseStart_128018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128018 prefixEnd_128018 := by exact prefixLift 128018
  have htrace : WordTrace (prefixWord ++ tailWord_128018) baseStart_128018 baseEnd_128018 := by
    simpa [prefixWord, tailWord_128018, baseEnd_128018] using wordTrace_append hprefix tailTrace_128018
  have hstable : (prefixWord ++ tailWord_128018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128018).length < 2 ^ (prefixWord ++ tailWord_128018).sum := by decide
  have hdescent : baseEnd_128018 < baseStart_128018 := by decide
  rcases family_descends (prefixWord ++ tailWord_128018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128024 : List Nat := [2, 1, 2, 3, 2, 3, 6]
def baseStart_128024 : Nat := 118140960795 + 128024 * 2 ^ 59
def prefixEnd_128024 : Nat := 4983230072969 + 3 ^ 40 * 128024 * 2
def baseEnd_128024 : Nat := 12985253789888857128145

theorem tailTrace_128024 : CollatzResearch.WordTrace tailWord_128024 prefixEnd_128024 12985253789888857128145 := by
  unfold tailWord_128024
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334709444099193801783563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3112945925465591735711417 2334709444099193801783563)
  ·
    refine ⟨3502064166148790702675345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2334709444099193801783563 3502064166148790702675345)
    ·
      refine ⟨2626548124611593027006509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3502064166148790702675345 2626548124611593027006509)
      ·
        refine ⟨984955546729347385127441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2626548124611593027006509 984955546729347385127441)
        ·
          refine ⟨738716660047010538845581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984955546729347385127441 738716660047010538845581)
          ·
            refine ⟨277018747517628952067093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 738716660047010538845581 277018747517628952067093)
            ·
              refine ⟨12985253789888857128145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277018747517628952067093 12985253789888857128145)
              ·
                rfl

theorem cell19_128024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_128024 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128024 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128024 prefixEnd_128024 := by exact prefixLift 128024
  have htrace : WordTrace (prefixWord ++ tailWord_128024) baseStart_128024 baseEnd_128024 := by
    simpa [prefixWord, tailWord_128024, baseEnd_128024] using wordTrace_append hprefix tailTrace_128024
  have hstable : (prefixWord ++ tailWord_128024).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128024).length < 2 ^ (prefixWord ++ tailWord_128024).sum := by decide
  have hdescent : baseEnd_128024 < baseStart_128024 := by decide
  rcases family_descends (prefixWord ++ tailWord_128024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128060 : List Nat := [2, 2, 2, 2, 2, 2, 4, 3]
def baseStart_128060 : Nat := 118140960795 + 128060 * 2 ^ 59
def prefixEnd_128060 : Nat := 4983230072969 + 3 ^ 40 * 128060 * 2
def baseEnd_128060 : Nat := 38966715623629154584337

theorem tailTrace_128060 : CollatzResearch.WordTrace tailWord_128060 prefixEnd_128060 38966715623629154584337 := by
  unfold tailWord_128060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335365958033982875938817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3113821277378643834585089 2335365958033982875938817)
  ·
    refine ⟨1751524468525487156954113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2335365958033982875938817 1751524468525487156954113)
    ·
      refine ⟨1313643351394115367715585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1751524468525487156954113 1313643351394115367715585)
      ·
        refine ⟨985232513545586525786689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1313643351394115367715585 985232513545586525786689)
        ·
          refine ⟨738924385159189894340017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 985232513545586525786689 738924385159189894340017)
          ·
            refine ⟨554193288869392420755013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738924385159189894340017 554193288869392420755013)
            ·
              refine ⟨103911241663011078891565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 554193288869392420755013 103911241663011078891565)
              ·
                refine ⟨38966715623629154584337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103911241663011078891565 38966715623629154584337)
                ·
                  rfl

theorem cell19_128060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_128060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128060 prefixEnd_128060 := by exact prefixLift 128060
  have htrace : WordTrace (prefixWord ++ tailWord_128060) baseStart_128060 baseEnd_128060 := by
    simpa [prefixWord, tailWord_128060, baseEnd_128060] using wordTrace_append hprefix tailTrace_128060
  have hstable : (prefixWord ++ tailWord_128060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128060).length < 2 ^ (prefixWord ++ tailWord_128060).sum := by decide
  have hdescent : baseEnd_128060 < baseStart_128060 := by decide
  rcases family_descends (prefixWord ++ tailWord_128060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128094 : List Nat := [4, 4, 1, 1, 1, 2, 2, 4]
def baseStart_128094 : Nat := 118140960795 + 128094 * 2 ^ 59
def prefixEnd_128094 : Nat := 4983230072969 + 3 ^ 40 * 128094 * 2
def baseEnd_128094 : Nat := 38977061307927149828689

theorem tailTrace_128094 : CollatzResearch.WordTrace tailWord_128094 prefixEnd_128094 38977061307927149828689 := by
  unfold tailWord_128094
  simp only [CollatzResearch.WordTrace]
  refine ⟨583996499743098694826917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3114647998629859705743557 583996499743098694826917)
  ·
    refine ⟨109499343701831005280047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 583996499743098694826917 109499343701831005280047)
    ·
      refine ⟨164249015552746507920071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109499343701831005280047 164249015552746507920071)
      ·
        refine ⟨246373523329119761880107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164249015552746507920071 246373523329119761880107)
        ·
          refine ⟨369560284993679642820161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246373523329119761880107 369560284993679642820161)
          ·
            refine ⟨277170213745259732115121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369560284993679642820161 277170213745259732115121)
            ·
              refine ⟨207877660308944799086341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277170213745259732115121 207877660308944799086341)
              ·
                refine ⟨38977061307927149828689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207877660308944799086341 38977061307927149828689)
                ·
                  rfl

theorem cell19_128094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_128094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128094 prefixEnd_128094 := by exact prefixLift 128094
  have htrace : WordTrace (prefixWord ++ tailWord_128094) baseStart_128094 baseEnd_128094 := by
    simpa [prefixWord, tailWord_128094, baseEnd_128094] using wordTrace_append hprefix tailTrace_128094
  have hstable : (prefixWord ++ tailWord_128094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128094).length < 2 ^ (prefixWord ++ tailWord_128094).sum := by decide
  have hdescent : baseEnd_128094 < baseStart_128094 := by decide
  rcases family_descends (prefixWord ++ tailWord_128094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128098 : List Nat := [3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_128098 : Nat := 118140960795 + 128098 * 2 ^ 59
def prefixEnd_128098 : Nat := 4983230072969 + 3 ^ 40 * 128098 * 2
def baseEnd_128098 : Nat := 38978278447256325739789

theorem tailTrace_128098 : CollatzResearch.WordTrace tailWord_128098 prefixEnd_128098 38978278447256325739789 := by
  unfold tailWord_128098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168029472482574560440237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3114745259953532161173965 1168029472482574560440237)
  ·
    refine ⟨438011052180965460165089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1168029472482574560440237 438011052180965460165089)
    ·
      refine ⟨328508289135724095123817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438011052180965460165089 328508289135724095123817)
      ·
        refine ⟨246381216851793071342863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328508289135724095123817 246381216851793071342863)
        ·
          refine ⟨369571825277689607014295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246381216851793071342863 369571825277689607014295)
          ·
            refine ⟨554357737916534410521443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369571825277689607014295 554357737916534410521443)
            ·
              refine ⟨831536606874801615782165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554357737916534410521443 831536606874801615782165)
              ·
                refine ⟨38978278447256325739789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 831536606874801615782165 38978278447256325739789)
                ·
                  rfl

theorem cell19_128098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_128098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128098 prefixEnd_128098 := by exact prefixLift 128098
  have htrace : WordTrace (prefixWord ++ tailWord_128098) baseStart_128098 baseEnd_128098 := by
    simpa [prefixWord, tailWord_128098, baseEnd_128098] using wordTrace_append hprefix tailTrace_128098
  have hstable : (prefixWord ++ tailWord_128098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128098).length < 2 ^ (prefixWord ++ tailWord_128098).sum := by decide
  have hdescent : baseEnd_128098 < baseStart_128098 := by decide
  rcases family_descends (prefixWord ++ tailWord_128098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128136 : List Nat := [2, 1, 3, 4, 3, 6]
def baseStart_128136 : Nat := 118140960795 + 128136 * 2 ^ 59
def prefixEnd_128136 : Nat := 4983230072969 + 3 ^ 40 * 128136 * 2
def baseEnd_128136 : Nat := 4332204585653721877249

theorem tailTrace_128136 : CollatzResearch.WordTrace tailWord_128136 prefixEnd_128136 4332204585653721877249 := by
  unfold tailWord_128136
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336751931896315365822131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3115669242528420487762841 2336751931896315365822131)
  ·
    refine ⟨3505127897844473048733197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2336751931896315365822131 3505127897844473048733197)
    ·
      refine ⟨1314422961691677393274949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3505127897844473048733197 1314422961691677393274949)
      ·
        refine ⟨246454305317189511239053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1314422961691677393274949 246454305317189511239053)
        ·
          refine ⟨92420364493946066714645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246454305317189511239053 92420364493946066714645)
          ·
            refine ⟨4332204585653721877249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92420364493946066714645 4332204585653721877249)
            ·
              rfl

theorem cell19_128136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 6].length) (baseStart_128136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128136 prefixEnd_128136 := by exact prefixLift 128136
  have htrace : WordTrace (prefixWord ++ tailWord_128136) baseStart_128136 baseEnd_128136 := by
    simpa [prefixWord, tailWord_128136, baseEnd_128136] using wordTrace_append hprefix tailTrace_128136
  have hstable : (prefixWord ++ tailWord_128136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128136).length < 2 ^ (prefixWord ++ tailWord_128136).sum := by decide
  have hdescent : baseEnd_128136 < baseStart_128136 := by decide
  rcases family_descends (prefixWord ++ tailWord_128136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128193 : List Nat := [1, 2, 6, 1, 1, 2, 6]
def baseStart_128193 : Nat := 118140960795 + 128193 * 2 ^ 59
def prefixEnd_128193 : Nat := 4983230072969 + 3 ^ 40 * 128193 * 2
def baseEnd_128193 : Nat := 13002395168774751209473

theorem tailTrace_128193 : CollatzResearch.WordTrace tailWord_128193 prefixEnd_128193 13002395168774751209473 := by
  unfold tailWord_128193
  simp only [CollatzResearch.WordTrace]
  refine ⟨4675582824586129466469233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3117055216390752977646155 4675582824586129466469233)
  ·
    refine ⟨3506687118439597099851925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4675582824586129466469233 3506687118439597099851925)
    ·
      refine ⟨164375958676856114055559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3506687118439597099851925 164375958676856114055559)
      ·
        refine ⟨246563938015284171083339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164375958676856114055559 246563938015284171083339)
        ·
          refine ⟨369845907022926256625009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246563938015284171083339 369845907022926256625009)
          ·
            refine ⟨277384430267194692468757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369845907022926256625009 277384430267194692468757)
            ·
              refine ⟨13002395168774751209473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277384430267194692468757 13002395168774751209473)
              ·
                rfl

theorem cell19_128193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_128193 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128193 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128193 prefixEnd_128193 := by exact prefixLift 128193
  have htrace : WordTrace (prefixWord ++ tailWord_128193) baseStart_128193 baseEnd_128193 := by
    simpa [prefixWord, tailWord_128193, baseEnd_128193] using wordTrace_append hprefix tailTrace_128193
  have hstable : (prefixWord ++ tailWord_128193).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128193).length < 2 ^ (prefixWord ++ tailWord_128193).sum := by decide
  have hdescent : baseEnd_128193 < baseStart_128193 := by decide
  rcases family_descends (prefixWord ++ tailWord_128193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128229 : List Nat := [1, 3, 1, 4, 3, 2, 2, 3]
def baseStart_128229 : Nat := 118140960795 + 128229 * 2 ^ 59
def prefixEnd_128229 : Nat := 4983230072969 + 3 ^ 40 * 128229 * 2
def baseEnd_128229 : Nat := 39018139760286836828321

theorem tailTrace_128229 : CollatzResearch.WordTrace tailWord_128229 prefixEnd_128229 39018139760286836828321 := by
  unfold tailWord_128229
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676895852455707614779741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3117930568303805076519827 4676895852455707614779741)
  ·
    refine ⟨1753835944670890355542403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4676895852455707614779741 1753835944670890355542403)
    ·
      refine ⟨2630753917006335533313605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753835944670890355542403 2630753917006335533313605)
      ·
        refine ⟨493266359438687912496301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2630753917006335533313605 493266359438687912496301)
        ·
          refine ⟨184974884789507967186113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493266359438687912496301 184974884789507967186113)
          ·
            refine ⟨138731163592130975389585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184974884789507967186113 138731163592130975389585)
            ·
              refine ⟨104048372694098231542189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138731163592130975389585 104048372694098231542189)
              ·
                refine ⟨39018139760286836828321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104048372694098231542189 39018139760286836828321)
                ·
                  rfl

theorem cell19_128229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 3].length) (baseStart_128229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128229 prefixEnd_128229 := by exact prefixLift 128229
  have htrace : WordTrace (prefixWord ++ tailWord_128229) baseStart_128229 baseEnd_128229 := by
    simpa [prefixWord, tailWord_128229, baseEnd_128229] using wordTrace_append hprefix tailTrace_128229
  have hstable : (prefixWord ++ tailWord_128229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128229).length < 2 ^ (prefixWord ++ tailWord_128229).sum := by decide
  have hdescent : baseEnd_128229 < baseStart_128229 := by decide
  rcases family_descends (prefixWord ++ tailWord_128229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128231 : List Nat := [1, 1, 5, 3, 2, 1, 1, 5]
def baseStart_128231 : Nat := 118140960795 + 128231 * 2 ^ 59
def prefixEnd_128231 : Nat := 4983230072969 + 3 ^ 40 * 128231 * 2
def baseEnd_128231 : Nat := 39018748329951424783871

theorem tailTrace_128231 : CollatzResearch.WordTrace tailWord_128231 prefixEnd_128231 39018748329951424783871 := by
  unfold tailWord_128231
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676968798448461956352547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3117979198965641304235031 4676968798448461956352547)
  ·
    refine ⟨7015453197672692934528821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4676968798448461956352547 7015453197672692934528821)
    ·
      refine ⟨657698737281814962612077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7015453197672692934528821 657698737281814962612077)
      ·
        refine ⟨246637026480680610979529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 657698737281814962612077 246637026480680610979529)
        ·
          refine ⟨184977769860510458234647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246637026480680610979529 184977769860510458234647)
          ·
            refine ⟨277466654790765687351971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184977769860510458234647 277466654790765687351971)
            ·
              refine ⟨416199982186148531027957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277466654790765687351971 416199982186148531027957)
              ·
                refine ⟨39018748329951424783871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 416199982186148531027957 39018748329951424783871)
                ·
                  rfl

theorem cell19_128231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_128231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128231 prefixEnd_128231 := by exact prefixLift 128231
  have htrace : WordTrace (prefixWord ++ tailWord_128231) baseStart_128231 baseEnd_128231 := by
    simpa [prefixWord, tailWord_128231, baseEnd_128231] using wordTrace_append hprefix tailTrace_128231
  have hstable : (prefixWord ++ tailWord_128231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128231).length < 2 ^ (prefixWord ++ tailWord_128231).sum := by decide
  have hdescent : baseEnd_128231 < baseStart_128231 := by decide
  rcases family_descends (prefixWord ++ tailWord_128231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128244 : List Nat := [2, 6, 1, 2, 2, 1, 5]
def baseStart_128244 : Nat := 118140960795 + 128244 * 2 ^ 59
def prefixEnd_128244 : Nat := 4983230072969 + 3 ^ 40 * 128244 * 2
def baseEnd_128244 : Nat := 13007568010923748831649

theorem tailTrace_128244 : CollatzResearch.WordTrace tailWord_128244 prefixEnd_128244 13007568010923748831649 := by
  unfold tailWord_128244
  simp only [CollatzResearch.WordTrace]
  refine ⟨2338721473700682588287893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3118295298267576784383857 2338721473700682588287893)
  ·
    refine ⟨109627569079719496325995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2338721473700682588287893 109627569079719496325995)
    ·
      refine ⟨164441353619579244488993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109627569079719496325995 164441353619579244488993)
      ·
        refine ⟨123331015214684433366745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164441353619579244488993 123331015214684433366745)
        ·
          refine ⟨92498261411013325025059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123331015214684433366745 92498261411013325025059)
          ·
            refine ⟨138747392116519987537589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92498261411013325025059 138747392116519987537589)
            ·
              refine ⟨13007568010923748831649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138747392116519987537589 13007568010923748831649)
              ·
                rfl

theorem cell19_128244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 5].length) (baseStart_128244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128244 prefixEnd_128244 := by exact prefixLift 128244
  have htrace : WordTrace (prefixWord ++ tailWord_128244) baseStart_128244 baseEnd_128244 := by
    simpa [prefixWord, tailWord_128244, baseEnd_128244] using wordTrace_append hprefix tailTrace_128244
  have hstable : (prefixWord ++ tailWord_128244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128244).length < 2 ^ (prefixWord ++ tailWord_128244).sum := by decide
  have hdescent : baseEnd_128244 < baseStart_128244 := by decide
  rcases family_descends (prefixWord ++ tailWord_128244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128324 : List Nat := [2, 3, 4, 1, 1, 3, 1, 4]
def baseStart_128324 : Nat := 118140960795 + 128324 * 2 ^ 59
def prefixEnd_128324 : Nat := 4983230072969 + 3 ^ 40 * 128324 * 2
def baseEnd_128324 : Nat := 39047046819354764716951

theorem tailTrace_128324 : CollatzResearch.WordTrace tailWord_128324 prefixEnd_128324 39047046819354764716951 := by
  unfold tailWord_128324
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340180393555769419744013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3120240524741025892992017 2340180393555769419744013)
  ·
    refine ⟨877567647583413532404005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2340180393555769419744013 877567647583413532404005)
    ·
      refine ⟨164543933921890037325751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 877567647583413532404005 164543933921890037325751)
      ·
        refine ⟨246815900882835055988627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164543933921890037325751 246815900882835055988627)
        ·
          refine ⟨370223851324252583982941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246815900882835055988627 370223851324252583982941)
          ·
            refine ⟨138833944246594718993603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370223851324252583982941 138833944246594718993603)
            ·
              refine ⟨208250916369892078490405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138833944246594718993603 208250916369892078490405)
              ·
                refine ⟨39047046819354764716951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208250916369892078490405 39047046819354764716951)
                ·
                  rfl

theorem cell19_128324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_128324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128324 prefixEnd_128324 := by exact prefixLift 128324
  have htrace : WordTrace (prefixWord ++ tailWord_128324) baseStart_128324 baseEnd_128324 := by
    simpa [prefixWord, tailWord_128324, baseEnd_128324] using wordTrace_append hprefix tailTrace_128324
  have hstable : (prefixWord ++ tailWord_128324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128324).length < 2 ^ (prefixWord ++ tailWord_128324).sum := by decide
  have hdescent : baseEnd_128324 < baseStart_128324 := by decide
  rcases family_descends (prefixWord ++ tailWord_128324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128368 : List Nat := [2, 1, 1, 1, 4, 2, 8]
def baseStart_128368 : Nat := 118140960795 + 128368 * 2 ^ 59
def prefixEnd_128368 : Nat := 4983230072969 + 3 ^ 40 * 128368 * 2
def baseEnd_128368 : Nat := 13020145117325233246351

theorem tailTrace_128368 : CollatzResearch.WordTrace tailWord_128368 prefixEnd_128368 13020145117325233246351 := by
  unfold tailWord_128368
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340982799476067177044879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3121310399301422902726505 2340982799476067177044879)
  ·
    refine ⟨3511474199214100765567319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2340982799476067177044879 3511474199214100765567319)
    ·
      refine ⟨5267211298821151148350979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511474199214100765567319 5267211298821151148350979)
      ·
        refine ⟨7900816948231726722526469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5267211298821151148350979 7900816948231726722526469)
        ·
          refine ⟨1481403177793448760473713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7900816948231726722526469 1481403177793448760473713)
          ·
            refine ⟨1111052383345086570355285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1481403177793448760473713 1111052383345086570355285)
            ·
              refine ⟨13020145117325233246351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1111052383345086570355285 13020145117325233246351)
              ·
                rfl

theorem cell19_128368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_128368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128368 prefixEnd_128368 := by exact prefixLift 128368
  have htrace : WordTrace (prefixWord ++ tailWord_128368) baseStart_128368 baseEnd_128368 := by
    simpa [prefixWord, tailWord_128368, baseEnd_128368] using wordTrace_append hprefix tailTrace_128368
  have hstable : (prefixWord ++ tailWord_128368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128368).length < 2 ^ (prefixWord ++ tailWord_128368).sum := by decide
  have hdescent : baseEnd_128368 < baseStart_128368 := by decide
  rcases family_descends (prefixWord ++ tailWord_128368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128398 : List Nat := [4, 1, 1, 4, 3, 1, 2, 3]
def baseStart_128398 : Nat := 118140960795 + 128398 * 2 ^ 59
def prefixEnd_128398 : Nat := 4983230072969 + 3 ^ 40 * 128398 * 2
def baseEnd_128398 : Nat := 39069563896944519072305

theorem tailTrace_128398 : CollatzResearch.WordTrace tailWord_128398 prefixEnd_128398 39069563896944519072305 := by
  unfold tailWord_128398
  simp only [CollatzResearch.WordTrace]
  refine ⟨585382473605431184710231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3122039859228966318454565 585382473605431184710231)
  ·
    refine ⟨878073710408146777065347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585382473605431184710231 878073710408146777065347)
    ·
      refine ⟨1317110565612220165598021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878073710408146777065347 1317110565612220165598021)
      ·
        refine ⟨246958231052291281049629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1317110565612220165598021 246958231052291281049629)
        ·
          refine ⟨92609336644609230393611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246958231052291281049629 92609336644609230393611)
          ·
            refine ⟨138914004966913845590417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92609336644609230393611 138914004966913845590417)
            ·
              refine ⟨104185503725185384192813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138914004966913845590417 104185503725185384192813)
              ·
                refine ⟨39069563896944519072305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104185503725185384192813 39069563896944519072305)
                ·
                  rfl

theorem cell19_128398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_128398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128398 prefixEnd_128398 := by exact prefixLift 128398
  have htrace : WordTrace (prefixWord ++ tailWord_128398) baseStart_128398 baseEnd_128398 := by
    simpa [prefixWord, tailWord_128398, baseEnd_128398] using wordTrace_append hprefix tailTrace_128398
  have hstable : (prefixWord ++ tailWord_128398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128398).length < 2 ^ (prefixWord ++ tailWord_128398).sum := by decide
  have hdescent : baseEnd_128398 < baseStart_128398 := by decide
  rcases family_descends (prefixWord ++ tailWord_128398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128463 : List Nat := [1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_128463 : Nat := 118140960795 + 128463 * 2 ^ 59
def prefixEnd_128463 : Nat := 4983230072969 + 3 ^ 40 * 128463 * 2
def baseEnd_128463 : Nat := 39089342411043627627683

theorem tailTrace_128463 : CollatzResearch.WordTrace tailWord_128463 prefixEnd_128463 39089342411043627627683 := by
  unfold tailWord_128463
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685430533607965578798043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3123620355738643719198695 4685430533607965578798043)
  ·
    refine ⟨7028145800411948368197065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685430533607965578798043 7028145800411948368197065)
    ·
      refine ⟨5271109350308961276147799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7028145800411948368197065 5271109350308961276147799)
      ·
        refine ⟨7906664025463441914221699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271109350308961276147799 7906664025463441914221699)
        ·
          refine ⟨11859996038195162871332549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906664025463441914221699 11859996038195162871332549)
          ·
            refine ⟨2223749257161593038374853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11859996038195162871332549 2223749257161593038374853)
            ·
              refine ⟨416952985717798694695285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2223749257161593038374853 416952985717798694695285)
              ·
                refine ⟨39089342411043627627683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 416952985717798694695285 39089342411043627627683)
                ·
                  rfl

theorem cell19_128463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_128463 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128463 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128463 prefixEnd_128463 := by exact prefixLift 128463
  have htrace : WordTrace (prefixWord ++ tailWord_128463) baseStart_128463 baseEnd_128463 := by
    simpa [prefixWord, tailWord_128463, baseEnd_128463] using wordTrace_append hprefix tailTrace_128463
  have hstable : (prefixWord ++ tailWord_128463).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128463).length < 2 ^ (prefixWord ++ tailWord_128463).sum := by decide
  have hdescent : baseEnd_128463 < baseStart_128463 := by decide
  rcases family_descends (prefixWord ++ tailWord_128463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128514 : List Nat := [3, 4, 1, 2, 1, 2, 3, 3]
def baseStart_128514 : Nat := 118140960795 + 128514 * 2 ^ 59
def prefixEnd_128514 : Nat := 4983230072969 + 3 ^ 40 * 128514 * 2
def baseEnd_128514 : Nat := 39104860937490620494211

theorem tailTrace_128514 : CollatzResearch.WordTrace tailWord_128514 prefixEnd_128514 39104860937490620494211 := by
  unfold tailWord_128514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171822664105800322226149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3124860437615467525936397 1171822664105800322226149)
  ·
    refine ⟨219716749519837560417403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1171822664105800322226149 219716749519837560417403)
    ·
      refine ⟨329575124279756340626105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219716749519837560417403 329575124279756340626105)
      ·
        refine ⟨247181343209817255469579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329575124279756340626105 247181343209817255469579)
        ·
          refine ⟨370772014814725883204369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247181343209817255469579 370772014814725883204369)
          ·
            refine ⟨278079011111044412403277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370772014814725883204369 278079011111044412403277)
            ·
              refine ⟨104279629166641654651229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278079011111044412403277 104279629166641654651229)
              ·
                refine ⟨39104860937490620494211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104279629166641654651229 39104860937490620494211)
                ·
                  rfl

theorem cell19_128514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_128514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128514 prefixEnd_128514 := by exact prefixLift 128514
  have htrace : WordTrace (prefixWord ++ tailWord_128514) baseStart_128514 baseEnd_128514 := by
    simpa [prefixWord, tailWord_128514, baseEnd_128514] using wordTrace_append hprefix tailTrace_128514
  have hstable : (prefixWord ++ tailWord_128514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128514).length < 2 ^ (prefixWord ++ tailWord_128514).sum := by decide
  have hdescent : baseEnd_128514 < baseStart_128514 := by decide
  rcases family_descends (prefixWord ++ tailWord_128514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128520 : List Nat := [2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_128520 : Nat := 118140960795 + 128520 * 2 ^ 59
def prefixEnd_128520 : Nat := 4983230072969 + 3 ^ 40 * 128520 * 2
def baseEnd_128520 : Nat := 39106686646484384360861

theorem tailTrace_128520 : CollatzResearch.WordTrace tailWord_128520 prefixEnd_128520 39106686646484384360861 := by
  unfold tailWord_128520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343754747200732156811507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3125006329600976209082009 2343754747200732156811507)
  ·
    refine ⟨3515632120801098235217261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2343754747200732156811507 3515632120801098235217261)
    ·
      refine ⟨1318362045300411838206473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3515632120801098235217261 1318362045300411838206473)
      ·
        refine ⟨988771533975308878654855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1318362045300411838206473 988771533975308878654855)
        ·
          refine ⟨1483157300962963317982283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988771533975308878654855 1483157300962963317982283)
          ·
            refine ⟨2224735951444444976973425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483157300962963317982283 2224735951444444976973425)
            ·
              refine ⟨1668551963583333732730069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224735951444444976973425 1668551963583333732730069)
              ·
                refine ⟨39106686646484384360861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1668551963583333732730069 39106686646484384360861)
                ·
                  rfl

theorem cell19_128520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_128520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128520 prefixEnd_128520 := by exact prefixLift 128520
  have htrace : WordTrace (prefixWord ++ tailWord_128520) baseStart_128520 baseEnd_128520 := by
    simpa [prefixWord, tailWord_128520, baseEnd_128520] using wordTrace_append hprefix tailTrace_128520
  have hstable : (prefixWord ++ tailWord_128520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128520).length < 2 ^ (prefixWord ++ tailWord_128520).sum := by decide
  have hdescent : baseEnd_128520 < baseStart_128520 := by decide
  rcases family_descends (prefixWord ++ tailWord_128520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128575 : List Nat := [1, 1, 2, 2, 3, 3, 4, 3]
def baseStart_128575 : Nat := 118140960795 + 128575 * 2 ^ 59
def prefixEnd_128575 : Nat := 4983230072969 + 3 ^ 40 * 128575 * 2
def baseEnd_128575 : Nat := 39123422312260553138489

theorem tailTrace_128575 : CollatzResearch.WordTrace tailWord_128575 prefixEnd_128575 39123422312260553138489 := by
  unfold tailWord_128575
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689515509202208706875179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3126343672801472471250119 4689515509202208706875179)
  ·
    refine ⟨7034273263803313060312769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4689515509202208706875179 7034273263803313060312769)
    ·
      refine ⟨5275704947852484795234577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7034273263803313060312769 5275704947852484795234577)
      ·
        refine ⟨3956778710889363596425933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5275704947852484795234577 3956778710889363596425933)
        ·
          refine ⟨1483792016583511348659725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3956778710889363596425933 1483792016583511348659725)
          ·
            refine ⟨556422006218816755747397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1483792016583511348659725 556422006218816755747397)
            ·
              refine ⟨104329126166028141702637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 556422006218816755747397 104329126166028141702637)
              ·
                refine ⟨39123422312260553138489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104329126166028141702637 39123422312260553138489)
                ·
                  rfl

theorem cell19_128575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 3].length) (baseStart_128575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128575 prefixEnd_128575 := by exact prefixLift 128575
  have htrace : WordTrace (prefixWord ++ tailWord_128575) baseStart_128575 baseEnd_128575 := by
    simpa [prefixWord, tailWord_128575, baseEnd_128575] using wordTrace_append hprefix tailTrace_128575
  have hstable : (prefixWord ++ tailWord_128575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128575).length < 2 ^ (prefixWord ++ tailWord_128575).sum := by decide
  have hdescent : baseEnd_128575 < baseStart_128575 := by decide
  rcases family_descends (prefixWord ++ tailWord_128575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128594 : List Nat := [3, 2, 2, 1, 2, 4, 5]
def baseStart_128594 : Nat := 118140960795 + 128594 * 2 ^ 59
def prefixEnd_128594 : Nat := 4983230072969 + 3 ^ 40 * 128594 * 2
def baseEnd_128594 : Nat := 13043067908024712905405

theorem tailTrace_128594 : CollatzResearch.WordTrace tailWord_128594 prefixEnd_128594 13043067908024712905405 := by
  unfold tailWord_128594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172552124033343737954209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3126805664088916634544557 1172552124033343737954209)
  ·
    refine ⟨879414093025007803465657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1172552124033343737954209 879414093025007803465657)
    ·
      refine ⟨659560569768755852599243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 879414093025007803465657 659560569768755852599243)
      ·
        refine ⟨989340854653133778898865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659560569768755852599243 989340854653133778898865)
        ·
          refine ⟨742005640989850334174149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989340854653133778898865 742005640989850334174149)
          ·
            refine ⟨139126057685596937657653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 742005640989850334174149 139126057685596937657653)
            ·
              refine ⟨13043067908024712905405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139126057685596937657653 13043067908024712905405)
              ·
                rfl

theorem cell19_128594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_128594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128594 prefixEnd_128594 := by exact prefixLift 128594
  have htrace : WordTrace (prefixWord ++ tailWord_128594) baseStart_128594 baseEnd_128594 := by
    simpa [prefixWord, tailWord_128594, baseEnd_128594] using wordTrace_append hprefix tailTrace_128594
  have hstable : (prefixWord ++ tailWord_128594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128594).length < 2 ^ (prefixWord ++ tailWord_128594).sum := by decide
  have hdescent : baseEnd_128594 < baseStart_128594 := by decide
  rcases family_descends (prefixWord ++ tailWord_128594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128613 : List Nat := [1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_128613 : Nat := 118140960795 + 128613 * 2 ^ 59
def prefixEnd_128613 : Nat := 4983230072969 + 3 ^ 40 * 128613 * 2
def baseEnd_128613 : Nat := 39134985135887724293941

theorem tailTrace_128613 : CollatzResearch.WordTrace tailWord_128613 prefixEnd_128613 39134985135887724293941 := by
  unfold tailWord_128613
  simp only [CollatzResearch.WordTrace]
  refine ⟨4690901483064541196758493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3127267655376360797838995 4690901483064541196758493)
  ·
    refine ⟨1759088056149202948784435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4690901483064541196758493 1759088056149202948784435)
    ·
      refine ⟨2638632084223804423176653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1759088056149202948784435 2638632084223804423176653)
      ·
        refine ⟨989487031583926658691245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2638632084223804423176653 989487031583926658691245)
        ·
          refine ⟨371057636843972497009217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 989487031583926658691245 371057636843972497009217)
          ·
            refine ⟨278293227632979372756913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371057636843972497009217 278293227632979372756913)
            ·
              refine ⟨208719920724734529567685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278293227632979372756913 208719920724734529567685)
              ·
                refine ⟨39134985135887724293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208719920724734529567685 39134985135887724293941)
                ·
                  rfl

theorem cell19_128613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_128613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128613 prefixEnd_128613 := by exact prefixLift 128613
  have htrace : WordTrace (prefixWord ++ tailWord_128613) baseStart_128613 baseEnd_128613 := by
    simpa [prefixWord, tailWord_128613, baseEnd_128613] using wordTrace_append hprefix tailTrace_128613
  have hstable : (prefixWord ++ tailWord_128613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128613).length < 2 ^ (prefixWord ++ tailWord_128613).sum := by decide
  have hdescent : baseEnd_128613 < baseStart_128613 := by decide
  rcases family_descends (prefixWord ++ tailWord_128613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128615 : List Nat := [1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_128615 : Nat := 118140960795 + 128615 * 2 ^ 59
def prefixEnd_128615 : Nat := 4983230072969 + 3 ^ 40 * 128615 * 2
def baseEnd_128615 : Nat := 39135593705552312249491

theorem tailTrace_128615 : CollatzResearch.WordTrace tailWord_128615 prefixEnd_128615 39135593705552312249491 := by
  unfold tailWord_128615
  simp only [CollatzResearch.WordTrace]
  refine ⟨4690974429057295538331299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3127316286038197025554199 4690974429057295538331299)
  ·
    refine ⟨7036461643585943307496949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4690974429057295538331299 7036461643585943307496949)
    ·
      refine ⟨659668279086182185077839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7036461643585943307496949 659668279086182185077839)
      ·
        refine ⟨989502418629273277616759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659668279086182185077839 989502418629273277616759)
        ·
          refine ⟨1484253627943909916425139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989502418629273277616759 1484253627943909916425139)
          ·
            refine ⟨2226380441915864874637709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484253627943909916425139 2226380441915864874637709)
            ·
              refine ⟨834892665718449327989141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2226380441915864874637709 834892665718449327989141)
              ·
                refine ⟨39135593705552312249491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 834892665718449327989141 39135593705552312249491)
                ·
                  rfl

theorem cell19_128615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_128615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128615 prefixEnd_128615 := by exact prefixLift 128615
  have htrace : WordTrace (prefixWord ++ tailWord_128615) baseStart_128615 baseEnd_128615 := by
    simpa [prefixWord, tailWord_128615, baseEnd_128615] using wordTrace_append hprefix tailTrace_128615
  have hstable : (prefixWord ++ tailWord_128615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128615).length < 2 ^ (prefixWord ++ tailWord_128615).sum := by decide
  have hdescent : baseEnd_128615 < baseStart_128615 := by decide
  rcases family_descends (prefixWord ++ tailWord_128615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128668 : List Nat := [2, 2, 3, 2, 3, 2, 1, 4]
def baseStart_128668 : Nat := 118140960795 + 128668 * 2 ^ 59
def prefixEnd_128668 : Nat := 4983230072969 + 3 ^ 40 * 128668 * 2
def baseEnd_128668 : Nat := 39151720801663893071569

theorem tailTrace_128668 : CollatzResearch.WordTrace tailWord_128668 prefixEnd_128668 39151720801663893071569 := by
  unfold tailWord_128668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2346453748932642795005329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3128604998576857060007105 2346453748932642795005329)
  ·
    refine ⟨1759840311699482096253997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2346453748932642795005329 1759840311699482096253997)
    ·
      refine ⟨659940116887305786095249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1759840311699482096253997 659940116887305786095249)
      ·
        refine ⟨494955087665479339571437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659940116887305786095249 494955087665479339571437)
        ·
          refine ⟨185608157874554752339289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494955087665479339571437 185608157874554752339289)
          ·
            refine ⟨139206118405916064254467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185608157874554752339289 139206118405916064254467)
            ·
              refine ⟨208809177608874096381701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139206118405916064254467 208809177608874096381701)
              ·
                refine ⟨39151720801663893071569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208809177608874096381701 39151720801663893071569)
                ·
                  rfl

theorem cell19_128668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_128668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128668 prefixEnd_128668 := by exact prefixLift 128668
  have htrace : WordTrace (prefixWord ++ tailWord_128668) baseStart_128668 baseEnd_128668 := by
    simpa [prefixWord, tailWord_128668, baseEnd_128668] using wordTrace_append hprefix tailTrace_128668
  have hstable : (prefixWord ++ tailWord_128668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128668).length < 2 ^ (prefixWord ++ tailWord_128668).sum := by decide
  have hdescent : baseEnd_128668 < baseStart_128668 := by decide
  rcases family_descends (prefixWord ++ tailWord_128668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128744 : List Nat := [2, 1, 4, 1, 3, 3, 2, 3]
def baseStart_128744 : Nat := 118140960795 + 128744 * 2 ^ 59
def prefixEnd_128744 : Nat := 4983230072969 + 3 ^ 40 * 128744 * 2
def baseEnd_128744 : Nat := 39174846448918235382473

theorem tailTrace_128744 : CollatzResearch.WordTrace tailWord_128744 prefixEnd_128744 39174846448918235382473 := by
  unfold tailWord_128744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347839722794975284888643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3130452963726633713184857 2347839722794975284888643)
  ·
    refine ⟨3521759584192462927332965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2347839722794975284888643 3521759584192462927332965)
    ·
      refine ⟨660329922036086798874931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3521759584192462927332965 660329922036086798874931)
      ·
        refine ⟨990494883054130198312397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660329922036086798874931 990494883054130198312397)
        ·
          refine ⟨371435581145298824367149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 990494883054130198312397 371435581145298824367149)
          ·
            refine ⟨139288342929487059137681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371435581145298824367149 139288342929487059137681)
            ·
              refine ⟨104466257197115294353261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139288342929487059137681 104466257197115294353261)
              ·
                refine ⟨39174846448918235382473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104466257197115294353261 39174846448918235382473)
                ·
                  rfl

theorem cell19_128744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_128744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128744 prefixEnd_128744 := by exact prefixLift 128744
  have htrace : WordTrace (prefixWord ++ tailWord_128744) baseStart_128744 baseEnd_128744 := by
    simpa [prefixWord, tailWord_128744, baseEnd_128744] using wordTrace_append hprefix tailTrace_128744
  have hstable : (prefixWord ++ tailWord_128744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128744).length < 2 ^ (prefixWord ++ tailWord_128744).sum := by decide
  have hdescent : baseEnd_128744 < baseStart_128744 := by decide
  rcases family_descends (prefixWord ++ tailWord_128744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128746 : List Nat := [3, 1, 3, 1, 1, 1, 6, 3]
def baseStart_128746 : Nat := 118140960795 + 128746 * 2 ^ 59
def prefixEnd_128746 : Nat := 4983230072969 + 3 ^ 40 * 128746 * 2
def baseEnd_128746 : Nat := 39175455018582823338023

theorem tailTrace_128746 : CollatzResearch.WordTrace tailWord_128746 prefixEnd_128746 39175455018582823338023 := by
  unfold tailWord_128746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173938097895676227837523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3130501594388469940900061 1173938097895676227837523)
  ·
    refine ⟨1760907146843514341756285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1173938097895676227837523 1760907146843514341756285)
    ·
      refine ⟨660340180066317878158607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1760907146843514341756285 660340180066317878158607)
      ·
        refine ⟨990510270099476817237911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660340180066317878158607 990510270099476817237911)
        ·
          refine ⟨1485765405149215225856867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990510270099476817237911 1485765405149215225856867)
          ·
            refine ⟨2228648107723822838785301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485765405149215225856867 2228648107723822838785301)
            ·
              refine ⟨104467880049554195568061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2228648107723822838785301 104467880049554195568061)
              ·
                refine ⟨39175455018582823338023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104467880049554195568061 39175455018582823338023)
                ·
                  rfl

theorem cell19_128746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_128746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128746 prefixEnd_128746 := by exact prefixLift 128746
  have htrace : WordTrace (prefixWord ++ tailWord_128746) baseStart_128746 baseEnd_128746 := by
    simpa [prefixWord, tailWord_128746, baseEnd_128746] using wordTrace_append hprefix tailTrace_128746
  have hstable : (prefixWord ++ tailWord_128746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128746).length < 2 ^ (prefixWord ++ tailWord_128746).sum := by decide
  have hdescent : baseEnd_128746 < baseStart_128746 := by decide
  rcases family_descends (prefixWord ++ tailWord_128746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128805 : List Nat := [1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_128805 : Nat := 118140960795 + 128805 * 2 ^ 59
def prefixEnd_128805 : Nat := 4983230072969 + 3 ^ 40 * 128805 * 2
def baseEnd_128805 : Nat := 39193407823688168026751

theorem tailTrace_128805 : CollatzResearch.WordTrace tailWord_128805 prefixEnd_128805 39193407823688168026751 := by
  unfold tailWord_128805
  simp only [CollatzResearch.WordTrace]
  refine ⟨4697904298368957987747869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3131936198912638658498579 4697904298368957987747869)
  ·
    refine ⟨1761714111888359245405451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4697904298368957987747869 1761714111888359245405451)
    ·
      refine ⟨2642571167832538868108177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1761714111888359245405451 2642571167832538868108177)
      ·
        refine ⟨1981928375874404151081133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2642571167832538868108177 1981928375874404151081133)
        ·
          refine ⟨743223140952901556655425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1981928375874404151081133 743223140952901556655425)
          ·
            refine ⟨557417355714676167491569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743223140952901556655425 557417355714676167491569)
            ·
              refine ⟨418063016786007125618677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557417355714676167491569 418063016786007125618677)
              ·
                refine ⟨39193407823688168026751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418063016786007125618677 39193407823688168026751)
                ·
                  rfl

theorem cell19_128805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_128805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128805 prefixEnd_128805 := by exact prefixLift 128805
  have htrace : WordTrace (prefixWord ++ tailWord_128805) baseStart_128805 baseEnd_128805 := by
    simpa [prefixWord, tailWord_128805, baseEnd_128805] using wordTrace_append hprefix tailTrace_128805
  have hstable : (prefixWord ++ tailWord_128805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128805).length < 2 ^ (prefixWord ++ tailWord_128805).sum := by decide
  have hdescent : baseEnd_128805 < baseStart_128805 := by decide
  rcases family_descends (prefixWord ++ tailWord_128805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128822 : List Nat := [5, 1, 2, 2, 1, 8]
def baseStart_128822 : Nat := 118140960795 + 128822 * 2 ^ 59
def prefixEnd_128822 : Nat := 4983230072969 + 3 ^ 40 * 128822 * 2
def baseEnd_128822 : Nat := 4355397851759685072103

theorem tailTrace_128822 : CollatzResearch.WordTrace tailWord_128822 prefixEnd_128822 4355397851759685072103 := by
  unfold tailWord_128822
  simp only [CollatzResearch.WordTrace]
  refine ⟨293657771206710618194795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3132349559538246594077813 293657771206710618194795)
  ·
    refine ⟨440486656810065927292193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293657771206710618194795 440486656810065927292193)
    ·
      refine ⟨330364992607549445469145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440486656810065927292193 330364992607549445469145)
      ·
        refine ⟨247773744455662084101859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330364992607549445469145 247773744455662084101859)
        ·
          refine ⟨371660616683493126152789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247773744455662084101859 371660616683493126152789)
          ·
            refine ⟨4355397851759685072103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 371660616683493126152789 4355397851759685072103)
            ·
              rfl

theorem cell19_128822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 8].length) (baseStart_128822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128822 prefixEnd_128822 := by exact prefixLift 128822
  have htrace : WordTrace (prefixWord ++ tailWord_128822) baseStart_128822 baseEnd_128822 := by
    simpa [prefixWord, tailWord_128822, baseEnd_128822] using wordTrace_append hprefix tailTrace_128822
  have hstable : (prefixWord ++ tailWord_128822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128822).length < 2 ^ (prefixWord ++ tailWord_128822).sum := by decide
  have hdescent : baseEnd_128822 < baseStart_128822 := by decide
  rcases family_descends (prefixWord ++ tailWord_128822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128919 : List Nat := [1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_128919 : Nat := 118140960795 + 128919 * 2 ^ 59
def prefixEnd_128919 : Nat := 4983230072969 + 3 ^ 40 * 128919 * 2
def baseEnd_128919 : Nat := 39228096294569681493107

theorem tailTrace_128919 : CollatzResearch.WordTrace tailWord_128919 prefixEnd_128919 39228096294569681493107 := by
  unfold tailWord_128919
  simp only [CollatzResearch.WordTrace]
  refine ⟨4702062219955955457397811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3134708146637303638265207 4702062219955955457397811)
  ·
    refine ⟨7053093329933933186096717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4702062219955955457397811 7053093329933933186096717)
    ·
      refine ⟨2644909998725224944786269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7053093329933933186096717 2644909998725224944786269)
      ·
        refine ⟨991841249521959354294851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2644909998725224944786269 991841249521959354294851)
        ·
          refine ⟨1487761874282939031442277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991841249521959354294851 1487761874282939031442277)
          ·
            refine ⟨278955351428051068395427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1487761874282939031442277 278955351428051068395427)
            ·
              refine ⟨418433027142076602593141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278955351428051068395427 418433027142076602593141)
              ·
                refine ⟨39228096294569681493107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418433027142076602593141 39228096294569681493107)
                ·
                  rfl

theorem cell19_128919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_128919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128919 prefixEnd_128919 := by exact prefixLift 128919
  have htrace : WordTrace (prefixWord ++ tailWord_128919) baseStart_128919 baseEnd_128919 := by
    simpa [prefixWord, tailWord_128919, baseEnd_128919] using wordTrace_append hprefix tailTrace_128919
  have hstable : (prefixWord ++ tailWord_128919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128919).length < 2 ^ (prefixWord ++ tailWord_128919).sum := by decide
  have hdescent : baseEnd_128919 < baseStart_128919 := by decide
  rcases family_descends (prefixWord ++ tailWord_128919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128957 : List Nat := [1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_128957 : Nat := 118140960795 + 128957 * 2 ^ 59
def prefixEnd_128957 : Nat := 4983230072969 + 3 ^ 40 * 128957 * 2
def baseEnd_128957 : Nat := 39239659118196852648559

theorem tailTrace_128957 : CollatzResearch.WordTrace tailWord_128957 prefixEnd_128957 39239659118196852648559 := by
  unfold tailWord_128957
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703448193818287947281125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3135632129212191964854083 4703448193818287947281125)
  ·
    refine ⟨881896536340928990115211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4703448193818287947281125 881896536340928990115211)
    ·
      refine ⟨1322844804511393485172817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 881896536340928990115211 1322844804511393485172817)
      ·
        refine ⟨992133603383545113879613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1322844804511393485172817 992133603383545113879613)
        ·
          refine ⟨372050101268829417704855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 992133603383545113879613 372050101268829417704855)
          ·
            refine ⟨558075151903244126557283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372050101268829417704855 558075151903244126557283)
            ·
              refine ⟨837112727854866189835925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558075151903244126557283 837112727854866189835925)
              ·
                refine ⟨39239659118196852648559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 837112727854866189835925 39239659118196852648559)
                ·
                  rfl

theorem cell19_128957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_128957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128957 prefixEnd_128957 := by exact prefixLift 128957
  have htrace : WordTrace (prefixWord ++ tailWord_128957) baseStart_128957 baseEnd_128957 := by
    simpa [prefixWord, tailWord_128957, baseEnd_128957] using wordTrace_append hprefix tailTrace_128957
  have hstable : (prefixWord ++ tailWord_128957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128957).length < 2 ^ (prefixWord ++ tailWord_128957).sum := by decide
  have hdescent : baseEnd_128957 < baseStart_128957 := by decide
  rcases family_descends (prefixWord ++ tailWord_128957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128997 : List Nat := [1, 3, 1, 14]
def baseStart_128997 : Nat := 118140960795 + 128997 * 2 ^ 59
def prefixEnd_128997 : Nat := 4983230072969 + 3 ^ 40 * 128997 * 2
def baseEnd_128997 : Nat := 484590500141834713081

theorem tailTrace_128997 : CollatzResearch.WordTrace tailWord_128997 prefixEnd_128997 484590500141834713081 := by
  unfold tailWord_128997
  simp only [CollatzResearch.WordTrace]
  refine ⟨4704907113673374778737245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3136604742448916519158163 4704907113673374778737245)
  ·
    refine ⟨1764340167627515542026467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4704907113673374778737245 1764340167627515542026467)
    ·
      refine ⟨2646510251441273313039701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1764340167627515542026467 2646510251441273313039701)
      ·
        refine ⟨484590500141834713081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 2646510251441273313039701 484590500141834713081)
        ·
          rfl

theorem cell19_128997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 14].length) (baseStart_128997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_128997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_128997 prefixEnd_128997 := by exact prefixLift 128997
  have htrace : WordTrace (prefixWord ++ tailWord_128997) baseStart_128997 baseEnd_128997 := by
    simpa [prefixWord, tailWord_128997, baseEnd_128997] using wordTrace_append hprefix tailTrace_128997
  have hstable : (prefixWord ++ tailWord_128997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128997).length < 2 ^ (prefixWord ++ tailWord_128997).sum := by decide
  have hdescent : baseEnd_128997 < baseStart_128997 := by decide
  rcases family_descends (prefixWord ++ tailWord_128997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129031 : List Nat := [1, 1, 4, 3, 1, 3, 3, 3]
def baseStart_129031 : Nat := 118140960795 + 129031 * 2 ^ 59
def prefixEnd_129031 : Nat := 4983230072969 + 3 ^ 40 * 129031 * 2
def baseEnd_129031 : Nat := 39262176195786607003913

theorem tailTrace_129031 : CollatzResearch.WordTrace tailWord_129031 prefixEnd_129031 39262176195786607003913 := by
  unfold tailWord_129031
  simp only [CollatzResearch.WordTrace]
  refine ⟨4706147195550198585474947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3137431463700132390316631 4706147195550198585474947)
  ·
    refine ⟨7059220793325297878212421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4706147195550198585474947 7059220793325297878212421)
    ·
      refine ⟨1323603898748493352164829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7059220793325297878212421 1323603898748493352164829)
      ·
        refine ⟨496351462030685007061811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1323603898748493352164829 496351462030685007061811)
        ·
          refine ⟨744527193046027510592717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496351462030685007061811 744527193046027510592717)
          ·
            refine ⟨279197697392260316472269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744527193046027510592717 279197697392260316472269)
            ·
              refine ⟨104699136522097618677101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279197697392260316472269 104699136522097618677101)
              ·
                refine ⟨39262176195786607003913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104699136522097618677101 39262176195786607003913)
                ·
                  rfl

theorem cell19_129031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 3].length) (baseStart_129031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129031 prefixEnd_129031 := by exact prefixLift 129031
  have htrace : WordTrace (prefixWord ++ tailWord_129031) baseStart_129031 baseEnd_129031 := by
    simpa [prefixWord, tailWord_129031, baseEnd_129031] using wordTrace_append hprefix tailTrace_129031
  have hstable : (prefixWord ++ tailWord_129031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129031).length < 2 ^ (prefixWord ++ tailWord_129031).sum := by decide
  have hdescent : baseEnd_129031 < baseStart_129031 := by decide
  rcases family_descends (prefixWord ++ tailWord_129031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129052 : List Nat := [2, 2, 3, 1, 3, 2, 6]
def baseStart_129052 : Nat := 118140960795 + 129052 * 2 ^ 59
def prefixEnd_129052 : Nat := 4983230072969 + 3 ^ 40 * 129052 * 2
def baseEnd_129052 : Nat := 13089522059088260179063

theorem tailTrace_129052 : CollatzResearch.WordTrace tailWord_129052 prefixEnd_129052 13089522059088260179063 := by
  unfold tailWord_129052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353456564237059585994705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3137942085649412781326273 2353456564237059585994705)
  ·
    refine ⟨1765092423177794689496029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2353456564237059585994705 1765092423177794689496029)
    ·
      refine ⟨661909658691673008561011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1765092423177794689496029 661909658691673008561011)
      ·
        refine ⟨992864488037509512841517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661909658691673008561011 992864488037509512841517)
        ·
          refine ⟨372324183014066067315569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 992864488037509512841517 372324183014066067315569)
          ·
            refine ⟨279243137260549550486677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372324183014066067315569 279243137260549550486677)
            ·
              refine ⟨13089522059088260179063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 279243137260549550486677 13089522059088260179063)
              ·
                rfl

theorem cell19_129052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_129052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129052 prefixEnd_129052 := by exact prefixLift 129052
  have htrace : WordTrace (prefixWord ++ tailWord_129052) baseStart_129052 baseEnd_129052 := by
    simpa [prefixWord, tailWord_129052, baseEnd_129052] using wordTrace_append hprefix tailTrace_129052
  have hstable : (prefixWord ++ tailWord_129052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129052).length < 2 ^ (prefixWord ++ tailWord_129052).sum := by decide
  have hdescent : baseEnd_129052 < baseStart_129052 := by decide
  rcases family_descends (prefixWord ++ tailWord_129052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129088 : List Nat := [2, 1, 1, 2, 2, 6, 2, 3]
def baseStart_129088 : Nat := 118140960795 + 129088 * 2 ^ 59
def prefixEnd_129088 : Nat := 4983230072969 + 3 ^ 40 * 129088 * 2
def baseEnd_129088 : Nat := 39279520431227363737091

theorem tailTrace_129088 : CollatzResearch.WordTrace tailWord_129088 prefixEnd_129088 39279520431227363737091 := by
  unfold tailWord_129088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2354113078171848660149959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3138817437562464880199945 2354113078171848660149959)
  ·
    refine ⟨3531169617257772990224939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2354113078171848660149959 3531169617257772990224939)
    ·
      refine ⟨5296754425886659485337409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531169617257772990224939 5296754425886659485337409)
      ·
        refine ⟨3972565819414994614003057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5296754425886659485337409 3972565819414994614003057)
        ·
          refine ⟨2979424364561245960502293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3972565819414994614003057 2979424364561245960502293)
          ·
            refine ⟨139660517088808404398545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2979424364561245960502293 139660517088808404398545)
            ·
              refine ⟨104745387816606303298909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139660517088808404398545 104745387816606303298909)
              ·
                refine ⟨39279520431227363737091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104745387816606303298909 39279520431227363737091)
                ·
                  rfl

theorem cell19_129088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_129088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129088 prefixEnd_129088 := by exact prefixLift 129088
  have htrace : WordTrace (prefixWord ++ tailWord_129088) baseStart_129088 baseEnd_129088 := by
    simpa [prefixWord, tailWord_129088, baseEnd_129088] using wordTrace_append hprefix tailTrace_129088
  have hstable : (prefixWord ++ tailWord_129088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129088).length < 2 ^ (prefixWord ++ tailWord_129088).sum := by decide
  have hdescent : baseEnd_129088 < baseStart_129088 := by decide
  rcases family_descends (prefixWord ++ tailWord_129088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129109 : List Nat := [1, 3, 2, 2, 1, 5, 5]
def baseStart_129109 : Nat := 118140960795 + 129109 * 2 ^ 59
def prefixEnd_129109 : Nat := 4983230072969 + 3 ^ 40 * 129109 * 2
def baseEnd_129109 : Nat := 13095303470901845756789

theorem tailTrace_129109 : CollatzResearch.WordTrace tailWord_129109 prefixEnd_129109 13095303470901845756789 := by
  unfold tailWord_129109
  simp only [CollatzResearch.WordTrace]
  refine ⟨4708992089267617906814381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3139328059511745271209587 4708992089267617906814381)
  ·
    refine ⟨1765872033475356715055393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4708992089267617906814381 1765872033475356715055393)
    ·
      refine ⟨1324404025106517536291545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1765872033475356715055393 1324404025106517536291545)
      ·
        refine ⟨993303018829888152218659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1324404025106517536291545 993303018829888152218659)
        ·
          refine ⟨1489954528244832228327989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993303018829888152218659 1489954528244832228327989)
          ·
            refine ⟨139683237022953021405749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1489954528244832228327989 139683237022953021405749)
            ·
              refine ⟨13095303470901845756789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139683237022953021405749 13095303470901845756789)
              ·
                rfl

theorem cell19_129109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_129109 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129109 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129109 prefixEnd_129109 := by exact prefixLift 129109
  have htrace : WordTrace (prefixWord ++ tailWord_129109) baseStart_129109 baseEnd_129109 := by
    simpa [prefixWord, tailWord_129109, baseEnd_129109] using wordTrace_append hprefix tailTrace_129109
  have hstable : (prefixWord ++ tailWord_129109).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129109).length < 2 ^ (prefixWord ++ tailWord_129109).sum := by decide
  have hdescent : baseEnd_129109 < baseStart_129109 := by decide
  rcases family_descends (prefixWord ++ tailWord_129109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129111 : List Nat := [1, 1, 3, 2, 2, 1, 9]
def baseStart_129111 : Nat := 118140960795 + 129111 * 2 ^ 59
def prefixEnd_129111 : Nat := 4983230072969 + 3 ^ 40 * 129111 * 2
def baseEnd_129111 : Nat := 13095506327456708408639

theorem tailTrace_129111 : CollatzResearch.WordTrace tailWord_129111 prefixEnd_129111 13095506327456708408639 := by
  unfold tailWord_129111
  simp only [CollatzResearch.WordTrace]
  refine ⟨4709065035260372248387187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3139376690173581498924791 4709065035260372248387187)
  ·
    refine ⟨7063597552890558372580781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4709065035260372248387187 7063597552890558372580781)
    ·
      refine ⟨2648849082333959389717793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7063597552890558372580781 2648849082333959389717793)
      ·
        refine ⟨1986636811750469542288345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2648849082333959389717793 1986636811750469542288345)
        ·
          refine ⟨1489977608812852156716259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1986636811750469542288345 1489977608812852156716259)
          ·
            refine ⟨2234966413219278235074389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489977608812852156716259 2234966413219278235074389)
            ·
              refine ⟨13095506327456708408639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2234966413219278235074389 13095506327456708408639)
              ·
                rfl

theorem cell19_129111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_129111 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129111 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129111 prefixEnd_129111 := by exact prefixLift 129111
  have htrace : WordTrace (prefixWord ++ tailWord_129111) baseStart_129111 baseEnd_129111 := by
    simpa [prefixWord, tailWord_129111, baseEnd_129111] using wordTrace_append hprefix tailTrace_129111
  have hstable : (prefixWord ++ tailWord_129111).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129111).length < 2 ^ (prefixWord ++ tailWord_129111).sum := by decide
  have hdescent : baseEnd_129111 < baseStart_129111 := by decide
  rcases family_descends (prefixWord ++ tailWord_129111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129166 : List Nat := [4, 1, 1, 3, 3, 7]
def baseStart_129166 : Nat := 118140960795 + 129166 * 2 ^ 59
def prefixEnd_129166 : Nat := 4983230072969 + 3 ^ 40 * 129166 * 2
def baseEnd_129166 : Nat := 4367028294238477111505

theorem tailTrace_129166 : CollatzResearch.WordTrace tailWord_129166 prefixEnd_129166 4367028294238477111505 := by
  unfold tailWord_129166
  simp only [CollatzResearch.WordTrace]
  refine ⟨588883881257639580204919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3140714033374077761092901 588883881257639580204919)
  ·
    refine ⟨883325821886459370307379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 588883881257639580204919 883325821886459370307379)
    ·
      refine ⟨1324988732829689055461069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 883325821886459370307379 1324988732829689055461069)
      ·
        refine ⟨496870774811133395797901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1324988732829689055461069 496870774811133395797901)
        ·
          refine ⟨186326540554175023424213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496870774811133395797901 186326540554175023424213)
          ·
            refine ⟨4367028294238477111505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 186326540554175023424213 4367028294238477111505)
            ·
              rfl

theorem cell19_129166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 7].length) (baseStart_129166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129166 prefixEnd_129166 := by exact prefixLift 129166
  have htrace : WordTrace (prefixWord ++ tailWord_129166) baseStart_129166 baseEnd_129166 := by
    simpa [prefixWord, tailWord_129166, baseEnd_129166] using wordTrace_append hprefix tailTrace_129166
  have hstable : (prefixWord ++ tailWord_129166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129166).length < 2 ^ (prefixWord ++ tailWord_129166).sum := by decide
  have hdescent : baseEnd_129166 < baseStart_129166 := by decide
  rcases family_descends (prefixWord ++ tailWord_129166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129183 : List Nat := [1, 1, 2, 6, 1, 3, 1, 4]
def baseStart_129183 : Nat := 118140960795 + 129183 * 2 ^ 59
def prefixEnd_129183 : Nat := 4983230072969 + 3 ^ 40 * 129183 * 2
def baseEnd_129183 : Nat := 39308427490295291625721

theorem tailTrace_129183 : CollatzResearch.WordTrace tailWord_129183 prefixEnd_129183 39308427490295291625721 := by
  unfold tailWord_129183
  simp only [CollatzResearch.WordTrace]
  refine ⟨4711691090999528545008203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3141127393999685696672135 4711691090999528545008203)
  ·
    refine ⟨7067536636499292817512305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4711691090999528545008203 7067536636499292817512305)
    ·
      refine ⟨5300652477374469613134229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7067536636499292817512305 5300652477374469613134229)
      ·
        refine ⟨248468084876928263115667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5300652477374469613134229 248468084876928263115667)
        ·
          refine ⟨372702127315392394673501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248468084876928263115667 372702127315392394673501)
          ·
            refine ⟨139763297743272148002563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372702127315392394673501 139763297743272148002563)
            ·
              refine ⟨209644946614908222003845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139763297743272148002563 209644946614908222003845)
              ·
                refine ⟨39308427490295291625721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209644946614908222003845 39308427490295291625721)
                ·
                  rfl

theorem cell19_129183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_129183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129183 prefixEnd_129183 := by exact prefixLift 129183
  have htrace : WordTrace (prefixWord ++ tailWord_129183) baseStart_129183 baseEnd_129183 := by
    simpa [prefixWord, tailWord_129183, baseEnd_129183] using wordTrace_append hprefix tailTrace_129183
  have hstable : (prefixWord ++ tailWord_129183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129183).length < 2 ^ (prefixWord ++ tailWord_129183).sum := by decide
  have hdescent : baseEnd_129183 < baseStart_129183 := by decide
  rcases family_descends (prefixWord ++ tailWord_129183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129185 : List Nat := [1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_129185 : Nat := 118140960795 + 129185 * 2 ^ 59
def prefixEnd_129185 : Nat := 4983230072969 + 3 ^ 40 * 129185 * 2
def baseEnd_129185 : Nat := 39309036059959879581271

theorem tailTrace_129185 : CollatzResearch.WordTrace tailWord_129185 prefixEnd_129185 39309036059959879581271 := by
  unfold tailWord_129185
  simp only [CollatzResearch.WordTrace]
  refine ⟨4711764036992282886581009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3141176024661521924387339 4711764036992282886581009)
  ·
    refine ⟨3533823027744212164935757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4711764036992282886581009 3533823027744212164935757)
    ·
      refine ⟨1325183635404079561850909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3533823027744212164935757 1325183635404079561850909)
      ·
        refine ⟨496943863276529835694091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1325183635404079561850909 496943863276529835694091)
        ·
          refine ⟨745415794914794753541137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496943863276529835694091 745415794914794753541137)
          ·
            refine ⟨559061846186096065155853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745415794914794753541137 559061846186096065155853)
            ·
              refine ⟨209648192319786024433445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559061846186096065155853 209648192319786024433445)
              ·
                refine ⟨39309036059959879581271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209648192319786024433445 39309036059959879581271)
                ·
                  rfl

theorem cell19_129185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_129185 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129185 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129185 prefixEnd_129185 := by exact prefixLift 129185
  have htrace : WordTrace (prefixWord ++ tailWord_129185) baseStart_129185 baseEnd_129185 := by
    simpa [prefixWord, tailWord_129185, baseEnd_129185] using wordTrace_append hprefix tailTrace_129185
  have hstable : (prefixWord ++ tailWord_129185).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129185).length < 2 ^ (prefixWord ++ tailWord_129185).sum := by decide
  have hdescent : baseEnd_129185 < baseStart_129185 := by decide
  rcases family_descends (prefixWord ++ tailWord_129185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129198 : List Nat := [4, 1, 4, 2, 1, 1, 3, 3]
def baseStart_129198 : Nat := 118140960795 + 129198 * 2 ^ 59
def prefixEnd_129198 : Nat := 4983230072969 + 3 ^ 40 * 129198 * 2
def baseEnd_129198 : Nat := 39312991762779701292347

theorem tailTrace_129198 : CollatzResearch.WordTrace tailWord_129198 prefixEnd_129198 39312991762779701292347 := by
  unfold tailWord_129198
  simp only [CollatzResearch.WordTrace]
  refine ⟨589029773243148263350531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3141492123963457404536165 589029773243148263350531)
  ·
    refine ⟨883544659864722395025797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 589029773243148263350531 883544659864722395025797)
    ·
      refine ⟨165664623724635449067337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 883544659864722395025797 165664623724635449067337)
      ·
        refine ⟨124248467793476586800503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165664623724635449067337 124248467793476586800503)
        ·
          refine ⟨186372701690214880200755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124248467793476586800503 186372701690214880200755)
          ·
            refine ⟨279559052535322320301133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186372701690214880200755 279559052535322320301133)
            ·
              refine ⟨104834644700745870112925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279559052535322320301133 104834644700745870112925)
              ·
                refine ⟨39312991762779701292347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104834644700745870112925 39312991762779701292347)
                ·
                  rfl

theorem cell19_129198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_129198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129198 prefixEnd_129198 := by exact prefixLift 129198
  have htrace : WordTrace (prefixWord ++ tailWord_129198) baseStart_129198 baseEnd_129198 := by
    simpa [prefixWord, tailWord_129198, baseEnd_129198] using wordTrace_append hprefix tailTrace_129198
  have hstable : (prefixWord ++ tailWord_129198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129198).length < 2 ^ (prefixWord ++ tailWord_129198).sum := by decide
  have hdescent : baseEnd_129198 < baseStart_129198 := by decide
  rcases family_descends (prefixWord ++ tailWord_129198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129301 : List Nat := [1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_129301 : Nat := 118140960795 + 129301 * 2 ^ 59
def prefixEnd_129301 : Nat := 4983230072969 + 3 ^ 40 * 129301 * 2
def baseEnd_129301 : Nat := 39344333100505981003177

theorem tailTrace_129301 : CollatzResearch.WordTrace tailWord_129301 prefixEnd_129301 39344333100505981003177 := by
  unfold tailWord_129301
  simp only [CollatzResearch.WordTrace]
  refine ⟨4715994904572034697803757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3143996603048023131869171 4715994904572034697803757)
  ·
    refine ⟨1768498089214513011676409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4715994904572034697803757 1768498089214513011676409)
    ·
      refine ⟨1326373566910884758757307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1768498089214513011676409 1326373566910884758757307)
      ·
        refine ⟨1989560350366327138135961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326373566910884758757307 1989560350366327138135961)
        ·
          refine ⟨1492170262774745353601971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1989560350366327138135961 1492170262774745353601971)
          ·
            refine ⟨2238255394162118030402957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492170262774745353601971 2238255394162118030402957)
            ·
              refine ⟨839345772810794261401109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2238255394162118030402957 839345772810794261401109)
              ·
                refine ⟨39344333100505981003177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 839345772810794261401109 39344333100505981003177)
                ·
                  rfl

theorem cell19_129301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_129301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129301 prefixEnd_129301 := by exact prefixLift 129301
  have htrace : WordTrace (prefixWord ++ tailWord_129301) baseStart_129301 baseEnd_129301 := by
    simpa [prefixWord, tailWord_129301, baseEnd_129301] using wordTrace_append hprefix tailTrace_129301
  have hstable : (prefixWord ++ tailWord_129301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129301).length < 2 ^ (prefixWord ++ tailWord_129301).sum := by decide
  have hdescent : baseEnd_129301 < baseStart_129301 := by decide
  rcases family_descends (prefixWord ++ tailWord_129301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129358 : List Nat := [4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_129358 : Nat := 118140960795 + 129358 * 2 ^ 59
def prefixEnd_129358 : Nat := 4983230072969 + 3 ^ 40 * 129358 * 2
def baseEnd_129358 : Nat := 39361677335946737736355

theorem tailTrace_129358 : CollatzResearch.WordTrace tailWord_129358 prefixEnd_129358 39361677335946737736355 := by
  unfold tailWord_129358
  simp only [CollatzResearch.WordTrace]
  refine ⟨589759233170691679078591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3145382576910355621752485 589759233170691679078591)
  ·
    refine ⟨884638849756037518617887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 589759233170691679078591 884638849756037518617887)
    ·
      refine ⟨1326958274634056277926831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 884638849756037518617887 1326958274634056277926831)
      ·
        refine ⟨1990437411951084416890247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326958274634056277926831 1990437411951084416890247)
        ·
          refine ⟨2985656117926626625335371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990437411951084416890247 2985656117926626625335371)
          ·
            refine ⟨4478484176889939938003057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985656117926626625335371 4478484176889939938003057)
            ·
              refine ⟨3358863132667454953502293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4478484176889939938003057 3358863132667454953502293)
              ·
                refine ⟨39361677335946737736355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3358863132667454953502293 39361677335946737736355)
                ·
                  rfl

theorem cell19_129358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_129358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129358 prefixEnd_129358 := by exact prefixLift 129358
  have htrace : WordTrace (prefixWord ++ tailWord_129358) baseStart_129358 baseEnd_129358 := by
    simpa [prefixWord, tailWord_129358, baseEnd_129358] using wordTrace_append hprefix tailTrace_129358
  have hstable : (prefixWord ++ tailWord_129358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129358).length < 2 ^ (prefixWord ++ tailWord_129358).sum := by decide
  have hdescent : baseEnd_129358 < baseStart_129358 := by decide
  rcases family_descends (prefixWord ++ tailWord_129358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129415 : List Nat := [1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_129415 : Nat := 118140960795 + 129415 * 2 ^ 59
def prefixEnd_129415 : Nat := 4983230072969 + 3 ^ 40 * 129415 * 2
def baseEnd_129415 : Nat := 39379021571387494469533

theorem tailTrace_129415 : CollatzResearch.WordTrace tailWord_129415 prefixEnd_129415 39379021571387494469533 := by
  unfold tailWord_129415
  simp only [CollatzResearch.WordTrace]
  refine ⟨4720152826159032167453699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3146768550772688111635799 4720152826159032167453699)
  ·
    refine ⟨7080229239238548251180549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4720152826159032167453699 7080229239238548251180549)
    ·
      refine ⟨1327542982357227797096353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7080229239238548251180549 1327542982357227797096353)
      ·
        refine ⟨995657236767920847822265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1327542982357227797096353 995657236767920847822265)
        ·
          refine ⟨746742927575940635866699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 995657236767920847822265 746742927575940635866699)
          ·
            refine ⟨1120114391363910953800049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746742927575940635866699 1120114391363910953800049)
            ·
              refine ⟨840085793522933215350037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120114391363910953800049 840085793522933215350037)
              ·
                refine ⟨39379021571387494469533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 840085793522933215350037 39379021571387494469533)
                ·
                  rfl

theorem cell19_129415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_129415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129415 prefixEnd_129415 := by exact prefixLift 129415
  have htrace : WordTrace (prefixWord ++ tailWord_129415) baseStart_129415 baseEnd_129415 := by
    simpa [prefixWord, tailWord_129415, baseEnd_129415] using wordTrace_append hprefix tailTrace_129415
  have hstable : (prefixWord ++ tailWord_129415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129415).length < 2 ^ (prefixWord ++ tailWord_129415).sum := by decide
  have hdescent : baseEnd_129415 < baseStart_129415 := by decide
  rcases family_descends (prefixWord ++ tailWord_129415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129428 : List Nat := [2, 4, 2, 1, 3, 2, 2, 3]
def baseStart_129428 : Nat := 118140960795 + 129428 * 2 ^ 59
def prefixEnd_129428 : Nat := 4983230072969 + 3 ^ 40 * 129428 * 2
def baseEnd_129428 : Nat := 39382977274207316180609

theorem tailTrace_129428 : CollatzResearch.WordTrace tailWord_129428 prefixEnd_129428 39382977274207316180609 := by
  unfold tailWord_129428
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360313487555967693838469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3147084650074623591784625 2360313487555967693838469)
  ·
    refine ⟨442558778916743942594713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2360313487555967693838469 442558778916743942594713)
    ·
      refine ⟨331919084187557956946035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442558778916743942594713 331919084187557956946035)
      ·
        refine ⟨497878626281336935419053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331919084187557956946035 497878626281336935419053)
        ·
          refine ⟨186704484855501350782145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497878626281336935419053 186704484855501350782145)
          ·
            refine ⟨140028363641626013086609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186704484855501350782145 140028363641626013086609)
            ·
              refine ⟨105021272731219509814957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140028363641626013086609 105021272731219509814957)
              ·
                refine ⟨39382977274207316180609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105021272731219509814957 39382977274207316180609)
                ·
                  rfl

theorem cell19_129428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_129428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129428 prefixEnd_129428 := by exact prefixLift 129428
  have htrace : WordTrace (prefixWord ++ tailWord_129428) baseStart_129428 baseEnd_129428 := by
    simpa [prefixWord, tailWord_129428, baseEnd_129428] using wordTrace_append hprefix tailTrace_129428
  have hstable : (prefixWord ++ tailWord_129428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129428).length < 2 ^ (prefixWord ++ tailWord_129428).sum := by decide
  have hdescent : baseEnd_129428 < baseStart_129428 := by decide
  rcases family_descends (prefixWord ++ tailWord_129428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129432 : List Nat := [2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_129432 : Nat := 118140960795 + 129432 * 2 ^ 59
def prefixEnd_129432 : Nat := 4983230072969 + 3 ^ 40 * 129432 * 2
def baseEnd_129432 : Nat := 39384194413536492091709

theorem tailTrace_129432 : CollatzResearch.WordTrace tailWord_129432 prefixEnd_129432 39384194413536492091709 := by
  unfold tailWord_129432
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360386433548722035411275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3147181911398296047215033 2360386433548722035411275)
  ·
    refine ⟨3540579650323083053116913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2360386433548722035411275 3540579650323083053116913)
    ·
      refine ⟨2655434737742312289837685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3540579650323083053116913 2655434737742312289837685)
      ·
        refine ⟨248947006663341777172283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2655434737742312289837685 248947006663341777172283)
        ·
          refine ⟨373420509995012665758425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248947006663341777172283 373420509995012665758425)
          ·
            refine ⟨280065382496259499318819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373420509995012665758425 280065382496259499318819)
            ·
              refine ⟨420098073744389248978229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280065382496259499318819 420098073744389248978229)
              ·
                refine ⟨39384194413536492091709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 420098073744389248978229 39384194413536492091709)
                ·
                  rfl

theorem cell19_129432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_129432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129432 prefixEnd_129432 := by exact prefixLift 129432
  have htrace : WordTrace (prefixWord ++ tailWord_129432) baseStart_129432 baseEnd_129432 := by
    simpa [prefixWord, tailWord_129432, baseEnd_129432] using wordTrace_append hprefix tailTrace_129432
  have hstable : (prefixWord ++ tailWord_129432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129432).length < 2 ^ (prefixWord ++ tailWord_129432).sum := by decide
  have hdescent : baseEnd_129432 < baseStart_129432 := by decide
  rcases family_descends (prefixWord ++ tailWord_129432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129506 : List Nat := [3, 3, 3, 2, 1, 7]
def baseStart_129506 : Nat := 118140960795 + 129506 * 2 ^ 59
def prefixEnd_129506 : Nat := 4983230072969 + 3 ^ 40 * 129506 * 2
def baseEnd_129506 : Nat := 4378523499014027383007

theorem tailTrace_129506 : CollatzResearch.WordTrace tailWord_129506 prefixEnd_129506 4378523499014027383007 := by
  unfold tailWord_129506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1180867967207338677254093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3148981245886236472677581 1180867967207338677254093)
  ·
    refine ⟨442825487702752003970285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1180867967207338677254093 442825487702752003970285)
    ·
      refine ⟨166059557888532001488857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442825487702752003970285 166059557888532001488857)
      ·
        refine ⟨124544668416399001116643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166059557888532001488857 124544668416399001116643)
        ·
          refine ⟨186817002624598501674965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124544668416399001116643 186817002624598501674965)
          ·
            refine ⟨4378523499014027383007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 186817002624598501674965 4378523499014027383007)
            ·
              rfl

theorem cell19_129506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 7].length) (baseStart_129506 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129506 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129506 prefixEnd_129506 := by exact prefixLift 129506
  have htrace : WordTrace (prefixWord ++ tailWord_129506) baseStart_129506 baseEnd_129506 := by
    simpa [prefixWord, tailWord_129506, baseEnd_129506] using wordTrace_append hprefix tailTrace_129506
  have hstable : (prefixWord ++ tailWord_129506).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129506).length < 2 ^ (prefixWord ++ tailWord_129506).sum := by decide
  have hdescent : baseEnd_129506 < baseStart_129506 := by decide
  rcases family_descends (prefixWord ++ tailWord_129506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129529 : List Nat := [1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_129529 : Nat := 118140960795 + 129529 * 2 ^ 59
def prefixEnd_129529 : Nat := 4983230072969 + 3 ^ 40 * 129529 * 2
def baseEnd_129529 : Nat := 39413710042269007935889

theorem tailTrace_129529 : CollatzResearch.WordTrace tailWord_129529 prefixEnd_129529 39413710042269007935889 := by
  unfold tailWord_129529
  simp only [CollatzResearch.WordTrace]
  refine ⟨4724310747746029637103641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3149540498497353091402427 4724310747746029637103641)
  ·
    refine ⟨3543233060809522227827731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4724310747746029637103641 3543233060809522227827731)
    ·
      refine ⟨5314849591214283341741597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3543233060809522227827731 5314849591214283341741597)
      ·
        refine ⟨1993068596705356253153099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5314849591214283341741597 1993068596705356253153099)
        ·
          refine ⟨2989602895058034379729649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993068596705356253153099 2989602895058034379729649)
          ·
            refine ⟨2242202171293525784797237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2989602895058034379729649 2242202171293525784797237)
            ·
              refine ⟨210206453558768042324741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2242202171293525784797237 210206453558768042324741)
              ·
                refine ⟨39413710042269007935889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210206453558768042324741 39413710042269007935889)
                ·
                  rfl

theorem cell19_129529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_129529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129529 prefixEnd_129529 := by exact prefixLift 129529
  have htrace : WordTrace (prefixWord ++ tailWord_129529) baseStart_129529 baseEnd_129529 := by
    simpa [prefixWord, tailWord_129529, baseEnd_129529] using wordTrace_append hprefix tailTrace_129529
  have hstable : (prefixWord ++ tailWord_129529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129529).length < 2 ^ (prefixWord ++ tailWord_129529).sum := by decide
  have hdescent : baseEnd_129529 < baseStart_129529 := by decide
  rcases family_descends (prefixWord ++ tailWord_129529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129546 : List Nat := [3, 1, 2, 2, 2, 1, 5, 3]
def baseStart_129546 : Nat := 118140960795 + 129546 * 2 ^ 59
def prefixEnd_129546 : Nat := 4983230072969 + 3 ^ 40 * 129546 * 2
def baseEnd_129546 : Nat := 39418882884418005558065

theorem tailTrace_129546 : CollatzResearch.WordTrace tailWord_129546 prefixEnd_129546 39418882884418005558065 := by
  unfold tailWord_129546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181232697171110385118123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3149953859122961026981661 1181232697171110385118123)
  ·
    refine ⟨1771849045756665577677185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1181232697171110385118123 1771849045756665577677185)
    ·
      refine ⟨1328886784317499183257889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1771849045756665577677185 1328886784317499183257889)
      ·
        refine ⟨996665088238124387443417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1328886784317499183257889 996665088238124387443417)
        ·
          refine ⟨747498816178593290582563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996665088238124387443417 747498816178593290582563)
          ·
            refine ⟨1121248224267889935873845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747498816178593290582563 1121248224267889935873845)
            ·
              refine ⟨105117021025114681488173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1121248224267889935873845 105117021025114681488173)
              ·
                refine ⟨39418882884418005558065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105117021025114681488173 39418882884418005558065)
                ·
                  rfl

theorem cell19_129546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_129546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129546 prefixEnd_129546 := by exact prefixLift 129546
  have htrace : WordTrace (prefixWord ++ tailWord_129546) baseStart_129546 baseEnd_129546 := by
    simpa [prefixWord, tailWord_129546, baseEnd_129546] using wordTrace_append hprefix tailTrace_129546
  have hstable : (prefixWord ++ tailWord_129546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129546).length < 2 ^ (prefixWord ++ tailWord_129546).sum := by decide
  have hdescent : baseEnd_129546 < baseStart_129546 := by decide
  rcases family_descends (prefixWord ++ tailWord_129546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129601 : List Nat := [1, 2, 5, 1, 1, 4, 2, 3]
def baseStart_129601 : Nat := 118140960795 + 129601 * 2 ^ 59
def prefixEnd_129601 : Nat := 4983230072969 + 3 ^ 40 * 129601 * 2
def baseEnd_129601 : Nat := 39435618550194174335693

theorem tailTrace_129601 : CollatzResearch.WordTrace tailWord_129601 prefixEnd_129601 39435618550194174335693 := by
  unfold tailWord_129601
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726936803485185933724657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3151291202323457289149771 4726936803485185933724657)
  ·
    refine ⟨3545202602613889450293493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4726936803485185933724657 3545202602613889450293493)
    ·
      refine ⟨332362743995052135965015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3545202602613889450293493 332362743995052135965015)
      ·
        refine ⟨498544115992578203947523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332362743995052135965015 498544115992578203947523)
        ·
          refine ⟨747816173988867305921285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498544115992578203947523 747816173988867305921285)
          ·
            refine ⟨140215532622912619860241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 747816173988867305921285 140215532622912619860241)
            ·
              refine ⟨105161649467184464895181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140215532622912619860241 105161649467184464895181)
              ·
                refine ⟨39435618550194174335693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105161649467184464895181 39435618550194174335693)
                ·
                  rfl

theorem cell19_129601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 3].length) (baseStart_129601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129601 prefixEnd_129601 := by exact prefixLift 129601
  have htrace : WordTrace (prefixWord ++ tailWord_129601) baseStart_129601 baseEnd_129601 := by
    simpa [prefixWord, tailWord_129601, baseEnd_129601] using wordTrace_append hprefix tailTrace_129601
  have hstable : (prefixWord ++ tailWord_129601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129601).length < 2 ^ (prefixWord ++ tailWord_129601).sum := by decide
  have hdescent : baseEnd_129601 < baseStart_129601 := by decide
  rcases family_descends (prefixWord ++ tailWord_129601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129605 : List Nat := [1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_129605 : Nat := 118140960795 + 129605 * 2 ^ 59
def prefixEnd_129605 : Nat := 4983230072969 + 3 ^ 40 * 129605 * 2
def baseEnd_129605 : Nat := 39436835689523350246793

theorem tailTrace_129605 : CollatzResearch.WordTrace tailWord_129605 prefixEnd_129605 39436835689523350246793 := by
  unfold tailWord_129605
  simp only [CollatzResearch.WordTrace]
  refine ⟨4727082695470694616870269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3151388463647129744580179 4727082695470694616870269)
  ·
    refine ⟨1772656010801510481326351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4727082695470694616870269 1772656010801510481326351)
    ·
      refine ⟨2658984016202265721989527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1772656010801510481326351 2658984016202265721989527)
      ·
        refine ⟨3988476024303398582984291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658984016202265721989527 3988476024303398582984291)
        ·
          refine ⟨5982714036455097874476437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988476024303398582984291 5982714036455097874476437)
          ·
            refine ⟨280439720458832712866083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5982714036455097874476437 280439720458832712866083)
            ·
              refine ⟨420659580688249069299125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280439720458832712866083 420659580688249069299125)
              ·
                refine ⟨39436835689523350246793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 420659580688249069299125 39436835689523350246793)
                ·
                  rfl

theorem cell19_129605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_129605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129605 prefixEnd_129605 := by exact prefixLift 129605
  have htrace : WordTrace (prefixWord ++ tailWord_129605) baseStart_129605 baseEnd_129605 := by
    simpa [prefixWord, tailWord_129605, baseEnd_129605] using wordTrace_append hprefix tailTrace_129605
  have hstable : (prefixWord ++ tailWord_129605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129605).length < 2 ^ (prefixWord ++ tailWord_129605).sum := by decide
  have hdescent : baseEnd_129605 < baseStart_129605 := by decide
  rcases family_descends (prefixWord ++ tailWord_129605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129696 : List Nat := [2, 1, 1, 4, 5, 1, 1, 4]
def baseStart_129696 : Nat := 118140960795 + 129696 * 2 ^ 59
def prefixEnd_129696 : Nat := 4983230072969 + 3 ^ 40 * 129696 * 2
def baseEnd_129696 : Nat := 39464525609262102224323

theorem tailTrace_129696 : CollatzResearch.WordTrace tailWord_129696 prefixEnd_129696 39464525609262102224323 := by
  unfold tailWord_129696
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365200869070508579216471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3153601158760678105621961 2365200869070508579216471)
  ·
    refine ⟨3547801303605762868824707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2365200869070508579216471 3547801303605762868824707)
    ·
      refine ⟨5321701955408644303237061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3547801303605762868824707 5321701955408644303237061)
      ·
        refine ⟨997819116639120806856949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5321701955408644303237061 997819116639120806856949)
        ·
          refine ⟨93545542184917575642839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 997819116639120806856949 93545542184917575642839)
          ·
            refine ⟨140318313277376363464259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93545542184917575642839 140318313277376363464259)
            ·
              refine ⟨210477469916064545196389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140318313277376363464259 210477469916064545196389)
              ·
                refine ⟨39464525609262102224323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210477469916064545196389 39464525609262102224323)
                ·
                  rfl

theorem cell19_129696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_129696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129696 prefixEnd_129696 := by exact prefixLift 129696
  have htrace : WordTrace (prefixWord ++ tailWord_129696) baseStart_129696 baseEnd_129696 := by
    simpa [prefixWord, tailWord_129696, baseEnd_129696] using wordTrace_append hprefix tailTrace_129696
  have hstable : (prefixWord ++ tailWord_129696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129696).length < 2 ^ (prefixWord ++ tailWord_129696).sum := by decide
  have hdescent : baseEnd_129696 < baseStart_129696 := by decide
  rcases family_descends (prefixWord ++ tailWord_129696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129738 : List Nat := [3, 1, 2, 1, 4, 2, 6]
def baseStart_129738 : Nat := 118140960795 + 129738 * 2 ^ 59
def prefixEnd_129738 : Nat := 4983230072969 + 3 ^ 40 * 129738 * 2
def baseEnd_129738 : Nat := 13159101857406149763625

theorem tailTrace_129738 : CollatzResearch.WordTrace tailWord_129738 prefixEnd_129738 13159101857406149763625 := by
  unfold tailWord_129738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1182983400997214582865467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3154622402659238887641245 1182983400997214582865467)
  ·
    refine ⟨1774475101495821874298201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1182983400997214582865467 1774475101495821874298201)
    ·
      refine ⟨1330856326121866405723651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1774475101495821874298201 1330856326121866405723651)
      ·
        refine ⟨1996284489182799608585477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330856326121866405723651 1996284489182799608585477)
        ·
          refine ⟨374303341721774926609777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1996284489182799608585477 374303341721774926609777)
          ·
            refine ⟨280727506291331194957333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374303341721774926609777 280727506291331194957333)
            ·
              refine ⟨13159101857406149763625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 280727506291331194957333 13159101857406149763625)
              ·
                rfl

theorem cell19_129738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_129738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129738 prefixEnd_129738 := by exact prefixLift 129738
  have htrace : WordTrace (prefixWord ++ tailWord_129738) baseStart_129738 baseEnd_129738 := by
    simpa [prefixWord, tailWord_129738, baseEnd_129738] using wordTrace_append hprefix tailTrace_129738
  have hstable : (prefixWord ++ tailWord_129738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129738).length < 2 ^ (prefixWord ++ tailWord_129738).sum := by decide
  have hdescent : baseEnd_129738 < baseStart_129738 := by decide
  rcases family_descends (prefixWord ++ tailWord_129738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129774 : List Nat := [4, 1, 2, 1, 1, 3, 4, 3]
def baseStart_129774 : Nat := 118140960795 + 129774 * 2 ^ 59
def prefixEnd_129774 : Nat := 4983230072969 + 3 ^ 40 * 129774 * 2
def baseEnd_129774 : Nat := 39488259826181032490777

theorem tailTrace_129774 : CollatzResearch.WordTrace tailWord_129774 prefixEnd_129774 39488259826181032490777 := by
  unfold tailWord_129774
  simp only [CollatzResearch.WordTrace]
  refine ⟨591655828982304559971547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3155497754572290986514917 591655828982304559971547)
  ·
    refine ⟨887483743473456839957321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 591655828982304559971547 887483743473456839957321)
    ·
      refine ⟨665612807605092629967991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 887483743473456839957321 665612807605092629967991)
      ·
        refine ⟨998419211407638944951987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665612807605092629967991 998419211407638944951987)
        ·
          refine ⟨1497628817111458417427981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998419211407638944951987 1497628817111458417427981)
          ·
            refine ⟨561610806416796906535493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1497628817111458417427981 561610806416796906535493)
            ·
              refine ⟨105302026203149419975405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 561610806416796906535493 105302026203149419975405)
              ·
                refine ⟨39488259826181032490777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105302026203149419975405 39488259826181032490777)
                ·
                  rfl

theorem cell19_129774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_129774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129774 prefixEnd_129774 := by exact prefixLift 129774
  have htrace : WordTrace (prefixWord ++ tailWord_129774) baseStart_129774 baseEnd_129774 := by
    simpa [prefixWord, tailWord_129774, baseEnd_129774] using wordTrace_append hprefix tailTrace_129774
  have hstable : (prefixWord ++ tailWord_129774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129774).length < 2 ^ (prefixWord ++ tailWord_129774).sum := by decide
  have hdescent : baseEnd_129774 < baseStart_129774 := by decide
  rcases family_descends (prefixWord ++ tailWord_129774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129810 : List Nat := [3, 2, 4, 1, 2, 1, 2, 4]
def baseStart_129810 : Nat := 118140960795 + 129810 * 2 ^ 59
def prefixEnd_129810 : Nat := 4983230072969 + 3 ^ 40 * 129810 * 2
def baseEnd_129810 : Nat := 39499214080143615690679

theorem tailTrace_129810 : CollatzResearch.WordTrace tailWord_129810 prefixEnd_129810 39499214080143615690679 := by
  unfold tailWord_129810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183639914932003657020721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3156373106485343085388589 1183639914932003657020721)
  ·
    refine ⟨887729936199002742765541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1183639914932003657020721 887729936199002742765541)
    ·
      refine ⟨166449363037313014268539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 887729936199002742765541 166449363037313014268539)
      ·
        refine ⟨249674044555969521402809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166449363037313014268539 249674044555969521402809)
        ·
          refine ⟨187255533416977141052107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249674044555969521402809 187255533416977141052107)
          ·
            refine ⟨280883300125465711578161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187255533416977141052107 280883300125465711578161)
            ·
              refine ⟨210662475094099283683621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280883300125465711578161 210662475094099283683621)
              ·
                refine ⟨39499214080143615690679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210662475094099283683621 39499214080143615690679)
                ·
                  rfl

theorem cell19_129810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_129810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129810 prefixEnd_129810 := by exact prefixLift 129810
  have htrace : WordTrace (prefixWord ++ tailWord_129810) baseStart_129810 baseEnd_129810 := by
    simpa [prefixWord, tailWord_129810, baseEnd_129810] using wordTrace_append hprefix tailTrace_129810
  have hstable : (prefixWord ++ tailWord_129810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129810).length < 2 ^ (prefixWord ++ tailWord_129810).sum := by decide
  have hdescent : baseEnd_129810 < baseStart_129810 := by decide
  rcases family_descends (prefixWord ++ tailWord_129810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129909 : List Nat := [1, 3, 4, 1, 1, 3, 6]
def baseStart_129909 : Nat := 118140960795 + 129909 * 2 ^ 59
def prefixEnd_129909 : Nat := 4983230072969 + 3 ^ 40 * 129909 * 2
def baseEnd_129909 : Nat := 13176446092846906496803

theorem tailTrace_129909 : CollatzResearch.WordTrace tailWord_129909 prefixEnd_129909 13176446092846906496803 := by
  unfold tailWord_129909
  simp only [CollatzResearch.WordTrace]
  refine ⟨4738170486369354535936781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3158780324246236357291187 4738170486369354535936781)
  ·
    refine ⟨1776813932388507950976293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4738170486369354535936781 1776813932388507950976293)
    ·
      refine ⟨333152612322845240808055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1776813932388507950976293 333152612322845240808055)
      ·
        refine ⟨499728918484267861212083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333152612322845240808055 499728918484267861212083)
        ·
          refine ⟨749593377726401791818125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499728918484267861212083 749593377726401791818125)
          ·
            refine ⟨281097516647400671931797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 749593377726401791818125 281097516647400671931797)
            ·
              refine ⟨13176446092846906496803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 281097516647400671931797 13176446092846906496803)
              ·
                rfl

theorem cell19_129909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_129909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_129909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_129909 prefixEnd_129909 := by exact prefixLift 129909
  have htrace : WordTrace (prefixWord ++ tailWord_129909) baseStart_129909 baseEnd_129909 := by
    simpa [prefixWord, tailWord_129909, baseEnd_129909] using wordTrace_append hprefix tailTrace_129909
  have hstable : (prefixWord ++ tailWord_129909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129909).length < 2 ^ (prefixWord ++ tailWord_129909).sum := by decide
  have hdescent : baseEnd_129909 < baseStart_129909 := by decide
  rcases family_descends (prefixWord ++ tailWord_129909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130004 : List Nat := [2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_130004 : Nat := 118140960795 + 130004 * 2 ^ 59
def prefixEnd_130004 : Nat := 4983230072969 + 3 ^ 40 * 130004 * 2
def baseEnd_130004 : Nat := 39558245337608647379039

theorem tailTrace_130004 : CollatzResearch.WordTrace tailWord_130004 prefixEnd_130004 39558245337608647379039 := by
  unfold tailWord_130004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370817710512592880322533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3161090280683457173763377 2370817710512592880322533)
  ·
    refine ⟨444528320721111165060475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2370817710512592880322533 444528320721111165060475)
    ·
      refine ⟨666792481081666747590713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444528320721111165060475 666792481081666747590713)
      ·
        refine ⟨500094360811250060693035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666792481081666747590713 500094360811250060693035)
        ·
          refine ⟨750141541216875091039553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500094360811250060693035 750141541216875091039553)
          ·
            refine ⟨562606155912656318279665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750141541216875091039553 562606155912656318279665)
            ·
              refine ⟨421954616934492238709749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562606155912656318279665 421954616934492238709749)
              ·
                refine ⟨39558245337608647379039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 421954616934492238709749 39558245337608647379039)
                ·
                  rfl

theorem cell19_130004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_130004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130004 prefixEnd_130004 := by exact prefixLift 130004
  have htrace : WordTrace (prefixWord ++ tailWord_130004) baseStart_130004 baseEnd_130004 := by
    simpa [prefixWord, tailWord_130004, baseEnd_130004] using wordTrace_append hprefix tailTrace_130004
  have hstable : (prefixWord ++ tailWord_130004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130004).length < 2 ^ (prefixWord ++ tailWord_130004).sum := by decide
  have hdescent : baseEnd_130004 < baseStart_130004 := by decide
  rcases family_descends (prefixWord ++ tailWord_130004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130021 : List Nat := [1, 3, 1, 6, 2, 6]
def baseStart_130021 : Nat := 118140960795 + 130021 * 2 ^ 59
def prefixEnd_130021 : Nat := 4983230072969 + 3 ^ 40 * 130021 * 2
def baseEnd_130021 : Nat := 4395935353306405000135

theorem tailTrace_130021 : CollatzResearch.WordTrace tailWord_130021 prefixEnd_130021 4395935353306405000135 := by
  unfold tailWord_130021
  simp only [CollatzResearch.WordTrace]
  refine ⟨4742255461963597664013917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3161503641309065109342611 4742255461963597664013917)
  ·
    refine ⟨1778345798236349124005219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4742255461963597664013917 1778345798236349124005219)
    ·
      refine ⟨2667518697354523686007829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1778345798236349124005219 2667518697354523686007829)
      ·
        refine ⟨125039938938493297781617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2667518697354523686007829 125039938938493297781617)
        ·
          refine ⟨93779954203869973336213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125039938938493297781617 93779954203869973336213)
          ·
            refine ⟨4395935353306405000135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93779954203869973336213 4395935353306405000135)
            ·
              rfl

theorem cell19_130021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 6].length) (baseStart_130021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130021 prefixEnd_130021 := by exact prefixLift 130021
  have htrace : WordTrace (prefixWord ++ tailWord_130021) baseStart_130021 baseEnd_130021 := by
    simpa [prefixWord, tailWord_130021, baseEnd_130021] using wordTrace_append hprefix tailTrace_130021
  have hstable : (prefixWord ++ tailWord_130021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130021).length < 2 ^ (prefixWord ++ tailWord_130021).sum := by decide
  have hdescent : baseEnd_130021 < baseStart_130021 := by decide
  rcases family_descends (prefixWord ++ tailWord_130021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130101 : List Nat := [1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_130101 : Nat := 118140960795 + 130101 * 2 ^ 59
def prefixEnd_130101 : Nat := 4983230072969 + 3 ^ 40 * 130101 * 2
def baseEnd_130101 : Nat := 39587760966341163223219

theorem tailTrace_130101 : CollatzResearch.WordTrace tailWord_130101 prefixEnd_130101 39587760966341163223219 := by
  unfold tailWord_130101
  simp only [CollatzResearch.WordTrace]
  refine ⟨4745173301673771326926157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3163448867782514217950771 4745173301673771326926157)
  ·
    refine ⟨1779439988127664247597309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4745173301673771326926157 1779439988127664247597309)
    ·
      refine ⟨667289995547874092848991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1779439988127664247597309 667289995547874092848991)
      ·
        refine ⟨1000934993321811139273487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667289995547874092848991 1000934993321811139273487)
        ·
          refine ⟨1501402489982716708910231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000934993321811139273487 1501402489982716708910231)
          ·
            refine ⟨2252103734974075063365347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501402489982716708910231 2252103734974075063365347)
            ·
              refine ⟨3378155602461112595048021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252103734974075063365347 3378155602461112595048021)
              ·
                refine ⟨39587760966341163223219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3378155602461112595048021 39587760966341163223219)
                ·
                  rfl

theorem cell19_130101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_130101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130101 prefixEnd_130101 := by exact prefixLift 130101
  have htrace : WordTrace (prefixWord ++ tailWord_130101) baseStart_130101 baseEnd_130101 := by
    simpa [prefixWord, tailWord_130101, baseEnd_130101] using wordTrace_append hprefix tailTrace_130101
  have hstable : (prefixWord ++ tailWord_130101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130101).length < 2 ^ (prefixWord ++ tailWord_130101).sum := by decide
  have hdescent : baseEnd_130101 < baseStart_130101 := by decide
  rcases family_descends (prefixWord ++ tailWord_130101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130120 : List Nat := [2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_130120 : Nat := 118140960795 + 130120 * 2 ^ 59
def prefixEnd_130120 : Nat := 4983230072969 + 3 ^ 40 * 130120 * 2
def baseEnd_130120 : Nat := 39593542378154748800945

theorem tailTrace_130120 : CollatzResearch.WordTrace tailWord_130120 prefixEnd_130120 39593542378154748800945 := by
  unfold tailWord_130120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372933144302468785933907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3163910859069958381245209 2372933144302468785933907)
  ·
    refine ⟨3559399716453703178900861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2372933144302468785933907 3559399716453703178900861)
    ·
      refine ⟨1334774893670138692087823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3559399716453703178900861 1334774893670138692087823)
      ·
        refine ⟨2002162340505208038131735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334774893670138692087823 2002162340505208038131735)
        ·
          refine ⟨3003243510757812057197603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002162340505208038131735 3003243510757812057197603)
          ·
            refine ⟨4504865266136718085796405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003243510757812057197603 4504865266136718085796405)
            ·
              refine ⟨422331118700317320543413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4504865266136718085796405 422331118700317320543413)
              ·
                refine ⟨39593542378154748800945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422331118700317320543413 39593542378154748800945)
                ·
                  rfl

theorem cell19_130120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_130120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130120 prefixEnd_130120 := by exact prefixLift 130120
  have htrace : WordTrace (prefixWord ++ tailWord_130120) baseStart_130120 baseEnd_130120 := by
    simpa [prefixWord, tailWord_130120, baseEnd_130120] using wordTrace_append hprefix tailTrace_130120
  have hstable : (prefixWord ++ tailWord_130120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130120).length < 2 ^ (prefixWord ++ tailWord_130120).sum := by decide
  have hdescent : baseEnd_130120 < baseStart_130120 := by decide
  rcases family_descends (prefixWord ++ tailWord_130120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130196 : List Nat := [2, 4, 2, 11]
def baseStart_130196 : Nat := 118140960795 + 130196 * 2 ^ 59
def prefixEnd_130196 : Nat := 4983230072969 + 3 ^ 40 * 130196 * 2
def baseEnd_130196 : Nat := 489094666980359149529

theorem tailTrace_130196 : CollatzResearch.WordTrace tailWord_130196 prefixEnd_130196 489094666980359149529 := by
  unfold tailWord_130196
  simp only [CollatzResearch.WordTrace]
  refine ⟨2374319118164801275817221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3165758824219735034422961 2374319118164801275817221)
  ·
    refine ⟨445184834655900239215729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2374319118164801275817221 445184834655900239215729)
    ·
      refine ⟨333888625991925179411797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445184834655900239215729 333888625991925179411797)
      ·
        refine ⟨489094666980359149529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 333888625991925179411797 489094666980359149529)
        ·
          rfl

theorem cell19_130196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 11].length) (baseStart_130196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130196 prefixEnd_130196 := by exact prefixLift 130196
  have htrace : WordTrace (prefixWord ++ tailWord_130196) baseStart_130196 baseEnd_130196 := by
    simpa [prefixWord, tailWord_130196, baseEnd_130196] using wordTrace_append hprefix tailTrace_130196
  have hstable : (prefixWord ++ tailWord_130196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130196).length < 2 ^ (prefixWord ++ tailWord_130196).sum := by decide
  have hdescent : baseEnd_130196 < baseStart_130196 := by decide
  rcases family_descends (prefixWord ++ tailWord_130196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130213 : List Nat := [1, 3, 1, 2, 1, 6, 1, 4]
def baseStart_130213 : Nat := 118140960795 + 130213 * 2 ^ 59
def prefixEnd_130213 : Nat := 4983230072969 + 3 ^ 40 * 130213 * 2
def baseEnd_130213 : Nat := 39621840867558088734025

theorem tailTrace_130213 : CollatzResearch.WordTrace tailWord_130213 prefixEnd_130213 39621840867558088734025 := by
  unfold tailWord_130213
  simp only [CollatzResearch.WordTrace]
  refine ⟨4749258277268014455003293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3166172184845342970002195 4749258277268014455003293)
  ·
    refine ⟨1780971853975505420626235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4749258277268014455003293 1780971853975505420626235)
    ·
      refine ⟨2671457780963258130939353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1780971853975505420626235 2671457780963258130939353)
      ·
        refine ⟨2003593335722443598204515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2671457780963258130939353 2003593335722443598204515)
        ·
          refine ⟨3005390003583665397306773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003593335722443598204515 3005390003583665397306773)
          ·
            refine ⟨140877656417984315498755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3005390003583665397306773 140877656417984315498755)
            ·
              refine ⟨211316484626976473248133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140877656417984315498755 211316484626976473248133)
              ·
                refine ⟨39621840867558088734025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211316484626976473248133 39621840867558088734025)
                ·
                  rfl

theorem cell19_130213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_130213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130213 prefixEnd_130213 := by exact prefixLift 130213
  have htrace : WordTrace (prefixWord ++ tailWord_130213) baseStart_130213 baseEnd_130213 := by
    simpa [prefixWord, tailWord_130213, baseEnd_130213] using wordTrace_append hprefix tailTrace_130213
  have hstable : (prefixWord ++ tailWord_130213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130213).length < 2 ^ (prefixWord ++ tailWord_130213).sum := by decide
  have hdescent : baseEnd_130213 < baseStart_130213 := by decide
  rcases family_descends (prefixWord ++ tailWord_130213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130287 : List Nat := [1, 1, 2, 1, 7, 2, 2, 3]
def baseStart_130287 : Nat := 118140960795 + 130287 * 2 ^ 59
def prefixEnd_130287 : Nat := 4983230072969 + 3 ^ 40 * 130287 * 2
def baseEnd_130287 : Nat := 39644357945147843089379

theorem tailTrace_130287 : CollatzResearch.WordTrace tailWord_130287 prefixEnd_130287 39644357945147843089379 := by
  unfold tailWord_130287
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751957278999925093197115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3167971519333283395464743 4751957278999925093197115)
  ·
    refine ⟨7127935918499887639795673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4751957278999925093197115 7127935918499887639795673)
    ·
      refine ⟨5345951938874915729846755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7127935918499887639795673 5345951938874915729846755)
      ·
        refine ⟨8018927908312373594770133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5345951938874915729846755 8018927908312373594770133)
        ·
          refine ⟨187943622851071256127425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8018927908312373594770133 187943622851071256127425)
          ·
            refine ⟨140957717138303442095569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187943622851071256127425 140957717138303442095569)
            ·
              refine ⟨105718287853727581571677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140957717138303442095569 105718287853727581571677)
              ·
                refine ⟨39644357945147843089379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105718287853727581571677 39644357945147843089379)
                ·
                  rfl

theorem cell19_130287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 3].length) (baseStart_130287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130287 prefixEnd_130287 := by exact prefixLift 130287
  have htrace : WordTrace (prefixWord ++ tailWord_130287) baseStart_130287 baseEnd_130287 := by
    simpa [prefixWord, tailWord_130287, baseEnd_130287] using wordTrace_append hprefix tailTrace_130287
  have hstable : (prefixWord ++ tailWord_130287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130287).length < 2 ^ (prefixWord ++ tailWord_130287).sum := by decide
  have hdescent : baseEnd_130287 < baseStart_130287 := by decide
  rcases family_descends (prefixWord ++ tailWord_130287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130291 : List Nat := [1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_130291 : Nat := 118140960795 + 130291 * 2 ^ 59
def prefixEnd_130291 : Nat := 4983230072969 + 3 ^ 40 * 130291 * 2
def baseEnd_130291 : Nat := 39645575084477019000479

theorem tailTrace_130291 : CollatzResearch.WordTrace tailWord_130291 prefixEnd_130291 39645575084477019000479 := by
  unfold tailWord_130291
  simp only [CollatzResearch.WordTrace]
  refine ⟨4752103170985433776342727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3168068780656955850895151 4752103170985433776342727)
  ·
    refine ⟨7128154756478150664514091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4752103170985433776342727 7128154756478150664514091)
    ·
      refine ⟨10692232134717225996771137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7128154756478150664514091 10692232134717225996771137)
      ·
        refine ⟨8019174101037919497578353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10692232134717225996771137 8019174101037919497578353)
        ·
          refine ⟨6014380575778439623183765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8019174101037919497578353 6014380575778439623183765)
          ·
            refine ⟨281924089489614357336739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6014380575778439623183765 281924089489614357336739)
            ·
              refine ⟨422886134234421536005109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281924089489614357336739 422886134234421536005109)
              ·
                refine ⟨39645575084477019000479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422886134234421536005109 39645575084477019000479)
                ·
                  rfl

theorem cell19_130291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_130291 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130291 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130291 prefixEnd_130291 := by exact prefixLift 130291
  have htrace : WordTrace (prefixWord ++ tailWord_130291) baseStart_130291 baseEnd_130291 := by
    simpa [prefixWord, tailWord_130291, baseEnd_130291] using wordTrace_append hprefix tailTrace_130291
  have hstable : (prefixWord ++ tailWord_130291).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130291).length < 2 ^ (prefixWord ++ tailWord_130291).sum := by decide
  have hdescent : baseEnd_130291 < baseStart_130291 := by decide
  rcases family_descends (prefixWord ++ tailWord_130291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130306 : List Nat := [3, 4, 1, 1, 3, 2, 5]
def baseStart_130306 : Nat := 118140960795 + 130306 * 2 ^ 59
def prefixEnd_130306 : Nat := 4983230072969 + 3 ^ 40 * 130306 * 2
def baseEnd_130306 : Nat := 13216713118987142889035

theorem tailTrace_130306 : CollatzResearch.WordTrace tailWord_130306 prefixEnd_130306 13216713118987142889035 := by
  unfold tailWord_130306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188162566482772834534693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3168433510620727558759181 1188162566482772834534693)
  ·
    refine ⟨222780481215519906475255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1188162566482772834534693 222780481215519906475255)
    ·
      refine ⟨334170721823279859712883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222780481215519906475255 334170721823279859712883)
      ·
        refine ⟨501256082734919789569325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334170721823279859712883 501256082734919789569325)
        ·
          refine ⟨187971031025594921088497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501256082734919789569325 187971031025594921088497)
          ·
            refine ⟨140978273269196190816373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187971031025594921088497 140978273269196190816373)
            ·
              refine ⟨13216713118987142889035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140978273269196190816373 13216713118987142889035)
              ·
                rfl

theorem cell19_130306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_130306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130306 prefixEnd_130306 := by exact prefixLift 130306
  have htrace : WordTrace (prefixWord ++ tailWord_130306) baseStart_130306 baseEnd_130306 := by
    simpa [prefixWord, tailWord_130306, baseEnd_130306] using wordTrace_append hprefix tailTrace_130306
  have hstable : (prefixWord ++ tailWord_130306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130306).length < 2 ^ (prefixWord ++ tailWord_130306).sum := by decide
  have hdescent : baseEnd_130306 < baseStart_130306 := by decide
  rcases family_descends (prefixWord ++ tailWord_130306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130308 : List Nat := [2, 3, 2, 2, 2, 3, 5]
def baseStart_130308 : Nat := 118140960795 + 130308 * 2 ^ 59
def prefixEnd_130308 : Nat := 4983230072969 + 3 ^ 40 * 130308 * 2
def baseEnd_130308 : Nat := 13216915975542005540885

theorem tailTrace_130308 : CollatzResearch.WordTrace tailWord_130308 prefixEnd_130308 13216915975542005540885 := by
  unfold tailWord_130308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376361605961922839855789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3168482141282563786474385 2376361605961922839855789)
  ·
    refine ⟨891135602235721064945921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2376361605961922839855789 891135602235721064945921)
    ·
      refine ⟨668351701676790798709441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 891135602235721064945921 668351701676790798709441)
      ·
        refine ⟨501263776257593099032081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668351701676790798709441 501263776257593099032081)
        ·
          refine ⟨375947832193194824274061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501263776257593099032081 375947832193194824274061)
          ·
            refine ⟨140980437072448059102773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375947832193194824274061 140980437072448059102773)
            ·
              refine ⟨13216915975542005540885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140980437072448059102773 13216915975542005540885)
              ·
                rfl

theorem cell19_130308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_130308 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130308 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130308 prefixEnd_130308 := by exact prefixLift 130308
  have htrace : WordTrace (prefixWord ++ tailWord_130308) baseStart_130308 baseEnd_130308 := by
    simpa [prefixWord, tailWord_130308, baseEnd_130308] using wordTrace_append hprefix tailTrace_130308
  have hstable : (prefixWord ++ tailWord_130308).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130308).length < 2 ^ (prefixWord ++ tailWord_130308).sum := by decide
  have hdescent : baseEnd_130308 < baseStart_130308 := by decide
  rcases family_descends (prefixWord ++ tailWord_130308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130346 : List Nat := [3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_130346 : Nat := 118140960795 + 130346 * 2 ^ 59
def prefixEnd_130346 : Nat := 4983230072969 + 3 ^ 40 * 130346 * 2
def baseEnd_130346 : Nat := 39662310750253187778107

theorem tailTrace_130346 : CollatzResearch.WordTrace tailWord_130346 prefixEnd_130346 39662310750253187778107 := by
  unfold tailWord_130346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188527296446544542398723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3169406123857452113063261 1188527296446544542398723)
  ·
    refine ⟨1782790944669816813598085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1188527296446544542398723 1782790944669816813598085)
    ·
      refine ⟨334273302125590652549641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1782790944669816813598085 334273302125590652549641)
      ·
        refine ⟨250704976594192989412231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334273302125590652549641 250704976594192989412231)
        ·
          refine ⟨376057464891289484118347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250704976594192989412231 376057464891289484118347)
          ·
            refine ⟨564086197336934226177521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376057464891289484118347 564086197336934226177521)
            ·
              refine ⟨423064648002700669633141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564086197336934226177521 423064648002700669633141)
              ·
                refine ⟨39662310750253187778107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 423064648002700669633141 39662310750253187778107)
                ·
                  rfl

theorem cell19_130346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_130346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130346 prefixEnd_130346 := by exact prefixLift 130346
  have htrace : WordTrace (prefixWord ++ tailWord_130346) baseStart_130346 baseEnd_130346 := by
    simpa [prefixWord, tailWord_130346, baseEnd_130346] using wordTrace_append hprefix tailTrace_130346
  have hstable : (prefixWord ++ tailWord_130346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130346).length < 2 ^ (prefixWord ++ tailWord_130346).sum := by decide
  have hdescent : baseEnd_130346 < baseStart_130346 := by decide
  rcases family_descends (prefixWord ++ tailWord_130346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130365 : List Nat := [1, 4, 1, 5, 1, 7]
def baseStart_130365 : Nat := 118140960795 + 130365 * 2 ^ 59
def prefixEnd_130365 : Nat := 4983230072969 + 3 ^ 40 * 130365 * 2
def baseEnd_130365 : Nat := 4407565795785197039537

theorem tailTrace_130365 : CollatzResearch.WordTrace tailWord_130365 prefixEnd_130365 4407565795785197039537 := by
  unfold tailWord_130365
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754802172717344414536549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3169868115144896276357699 4754802172717344414536549)
  ·
    refine ⟨891525407384502077725603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4754802172717344414536549 891525407384502077725603)
    ·
      refine ⟨1337288111076753116588405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 891525407384502077725603 1337288111076753116588405)
      ·
        refine ⟨125370760413445604680163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1337288111076753116588405 125370760413445604680163)
        ·
          refine ⟨188056140620168407020245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125370760413445604680163 188056140620168407020245)
          ·
            refine ⟨4407565795785197039537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 188056140620168407020245 4407565795785197039537)
            ·
              rfl

theorem cell19_130365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 7].length) (baseStart_130365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130365 prefixEnd_130365 := by exact prefixLift 130365
  have htrace : WordTrace (prefixWord ++ tailWord_130365) baseStart_130365 baseEnd_130365 := by
    simpa [prefixWord, tailWord_130365, baseEnd_130365] using wordTrace_append hprefix tailTrace_130365
  have hstable : (prefixWord ++ tailWord_130365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130365).length < 2 ^ (prefixWord ++ tailWord_130365).sum := by decide
  have hdescent : baseEnd_130365 < baseStart_130365 := by decide
  rcases family_descends (prefixWord ++ tailWord_130365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130397 : List Nat := [1, 4, 5, 1, 1, 1, 3, 3]
def baseStart_130397 : Nat := 118140960795 + 130397 * 2 ^ 59
def prefixEnd_130397 : Nat := 4983230072969 + 3 ^ 40 * 130397 * 2
def baseEnd_130397 : Nat := 39677829276700180644635

theorem tailTrace_130397 : CollatzResearch.WordTrace tailWord_130397 prefixEnd_130397 39677829276700180644635 := by
  unfold tailWord_130397
  simp only [CollatzResearch.WordTrace]
  refine ⟨4755969308601413879701445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3170646205734275919800963 4755969308601413879701445)
  ·
    refine ⟨891744245362765102444021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4755969308601413879701445 891744245362765102444021)
    ·
      refine ⟨83601023002759228354127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 891744245362765102444021 83601023002759228354127)
      ·
        refine ⟨125401534504138842531191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83601023002759228354127 125401534504138842531191)
        ·
          refine ⟨188102301756208263796787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125401534504138842531191 188102301756208263796787)
          ·
            refine ⟨282153452634312395695181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188102301756208263796787 282153452634312395695181)
            ·
              refine ⟨105807544737867148385693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282153452634312395695181 105807544737867148385693)
              ·
                refine ⟨39677829276700180644635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105807544737867148385693 39677829276700180644635)
                ·
                  rfl

theorem cell19_130397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 3].length) (baseStart_130397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130397 prefixEnd_130397 := by exact prefixLift 130397
  have htrace : WordTrace (prefixWord ++ tailWord_130397) baseStart_130397 baseEnd_130397 := by
    simpa [prefixWord, tailWord_130397, baseEnd_130397] using wordTrace_append hprefix tailTrace_130397
  have hstable : (prefixWord ++ tailWord_130397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130397).length < 2 ^ (prefixWord ++ tailWord_130397).sum := by decide
  have hdescent : baseEnd_130397 < baseStart_130397 := by decide
  rcases family_descends (prefixWord ++ tailWord_130397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130403 : List Nat := [1, 1, 1, 5, 2, 3, 3, 3]
def baseStart_130403 : Nat := 118140960795 + 130403 * 2 ^ 59
def prefixEnd_130403 : Nat := 4983230072969 + 3 ^ 40 * 130403 * 2
def baseEnd_130403 : Nat := 39679654985693944511285

theorem tailTrace_130403 : CollatzResearch.WordTrace tailWord_130403 prefixEnd_130403 39679654985693944511285 := by
  unfold tailWord_130403
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756188146579676904419863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3170792097719784602946575 4756188146579676904419863)
  ·
    refine ⟨7134282219869515356629795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4756188146579676904419863 7134282219869515356629795)
    ·
      refine ⟨10701423329804273034944693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7134282219869515356629795 10701423329804273034944693)
      ·
        refine ⟨1003258437169150597026065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10701423329804273034944693 1003258437169150597026065)
        ·
          refine ⟨752443827876862947769549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003258437169150597026065 752443827876862947769549)
          ·
            refine ⟨282166435453823605413581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 752443827876862947769549 282166435453823605413581)
            ·
              refine ⟨105812413295183852030093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282166435453823605413581 105812413295183852030093)
              ·
                refine ⟨39679654985693944511285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105812413295183852030093 39679654985693944511285)
                ·
                  rfl

theorem cell19_130403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 3].length) (baseStart_130403 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130403 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130403 prefixEnd_130403 := by exact prefixLift 130403
  have htrace : WordTrace (prefixWord ++ tailWord_130403) baseStart_130403 baseEnd_130403 := by
    simpa [prefixWord, tailWord_130403, baseEnd_130403] using wordTrace_append hprefix tailTrace_130403
  have hstable : (prefixWord ++ tailWord_130403).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130403).length < 2 ^ (prefixWord ++ tailWord_130403).sum := by decide
  have hdescent : baseEnd_130403 < baseStart_130403 := by decide
  rcases family_descends (prefixWord ++ tailWord_130403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130456 : List Nat := [2, 1, 2, 5, 3, 1, 2, 3]
def baseStart_130456 : Nat := 118140960795 + 130456 * 2 ^ 59
def prefixEnd_130456 : Nat := 4983230072969 + 3 ^ 40 * 130456 * 2
def baseEnd_130456 : Nat := 39695782081805525333363

theorem tailTrace_130456 : CollatzResearch.WordTrace tailWord_130456 prefixEnd_130456 39695782081805525333363 := by
  unfold tailWord_130456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379060607693833478049611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3172080810258444637399481 2379060607693833478049611)
  ·
    refine ⟨3568590911540750217074417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2379060607693833478049611 3568590911540750217074417)
    ·
      refine ⟨2676443183655562662805813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3568590911540750217074417 2676443183655562662805813)
      ·
        refine ⟨250916548467708999638045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2676443183655562662805813 250916548467708999638045)
        ·
          refine ⟨94093705675390874864267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250916548467708999638045 94093705675390874864267)
          ·
            refine ⟨141140558513086312296401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94093705675390874864267 141140558513086312296401)
            ·
              refine ⟨105855418884814734222301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141140558513086312296401 105855418884814734222301)
              ·
                refine ⟨39695782081805525333363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105855418884814734222301 39695782081805525333363)
                ·
                  rfl

theorem cell19_130456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_130456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130456 prefixEnd_130456 := by exact prefixLift 130456
  have htrace : WordTrace (prefixWord ++ tailWord_130456) baseStart_130456 baseEnd_130456 := by
    simpa [prefixWord, tailWord_130456, baseEnd_130456] using wordTrace_append hprefix tailTrace_130456
  have hstable : (prefixWord ++ tailWord_130456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130456).length < 2 ^ (prefixWord ++ tailWord_130456).sum := by decide
  have hdescent : baseEnd_130456 < baseStart_130456 := by decide
  rcases family_descends (prefixWord ++ tailWord_130456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130538 : List Nat := [3, 1, 3, 1, 4, 7]
def baseStart_130538 : Nat := 118140960795 + 130538 * 2 ^ 59
def prefixEnd_130538 : Nat := 4983230072969 + 3 ^ 40 * 130538 * 2
def baseEnd_130538 : Nat := 4413414826450403501213

theorem tailTrace_130538 : CollatzResearch.WordTrace tailWord_130538 prefixEnd_130538 4413414826450403501213 := by
  unfold tailWord_130538
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190278000272648740146067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3174074667393729973722845 1190278000272648740146067)
  ·
    refine ⟨1785417000408973110219101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1190278000272648740146067 1785417000408973110219101)
    ·
      refine ⟨669531375153364916332163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1785417000408973110219101 669531375153364916332163)
      ·
        refine ⟨1004297062730047374498245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669531375153364916332163 1004297062730047374498245)
        ·
          refine ⟨188305699261883882718421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1004297062730047374498245 188305699261883882718421)
          ·
            refine ⟨4413414826450403501213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 188305699261883882718421 4413414826450403501213)
            ·
              rfl

theorem cell19_130538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 7].length) (baseStart_130538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130538 prefixEnd_130538 := by exact prefixLift 130538
  have htrace : WordTrace (prefixWord ++ tailWord_130538) baseStart_130538 baseEnd_130538 := by
    simpa [prefixWord, tailWord_130538, baseEnd_130538] using wordTrace_append hprefix tailTrace_130538
  have hstable : (prefixWord ++ tailWord_130538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130538).length < 2 ^ (prefixWord ++ tailWord_130538).sum := by decide
  have hdescent : baseEnd_130538 < baseStart_130538 := by decide
  rcases family_descends (prefixWord ++ tailWord_130538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130557 : List Nat := [1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_130557 : Nat := 118140960795 + 130557 * 2 ^ 59
def prefixEnd_130557 : Nat := 4983230072969 + 3 ^ 40 * 130557 * 2
def baseEnd_130557 : Nat := 39726514849867217088643

theorem tailTrace_130557 : CollatzResearch.WordTrace tailWord_130557 prefixEnd_130557 39726514849867217088643 := by
  unfold tailWord_130557
  simp only [CollatzResearch.WordTrace]
  refine ⟨4761804988021761205525925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3174536658681174137017283 4761804988021761205525925)
  ·
    refine ⟨892838435254080226036111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4761804988021761205525925 892838435254080226036111)
    ·
      refine ⟨1339257652881120339054167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 892838435254080226036111 1339257652881120339054167)
      ·
        refine ⟨2008886479321680508581251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339257652881120339054167 2008886479321680508581251)
        ·
          refine ⟨3013329718982520762871877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008886479321680508581251 3013329718982520762871877)
          ·
            refine ⟨564999322309222643038477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3013329718982520762871877 564999322309222643038477)
            ·
              refine ⟨211874745865958491139429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 564999322309222643038477 211874745865958491139429)
              ·
                refine ⟨39726514849867217088643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211874745865958491139429 39726514849867217088643)
                ·
                  rfl

theorem cell19_130557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_130557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130557 prefixEnd_130557 := by exact prefixLift 130557
  have htrace : WordTrace (prefixWord ++ tailWord_130557) baseStart_130557 baseEnd_130557 := by
    simpa [prefixWord, tailWord_130557, baseEnd_130557] using wordTrace_append hprefix tailTrace_130557
  have hstable : (prefixWord ++ tailWord_130557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130557).length < 2 ^ (prefixWord ++ tailWord_130557).sum := by decide
  have hdescent : baseEnd_130557 < baseStart_130557 := by decide
  rcases family_descends (prefixWord ++ tailWord_130557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130559 : List Nat := [1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_130559 : Nat := 118140960795 + 130559 * 2 ^ 59
def prefixEnd_130559 : Nat := 4983230072969 + 3 ^ 40 * 130559 * 2
def baseEnd_130559 : Nat := 39727123419531805044193

theorem tailTrace_130559 : CollatzResearch.WordTrace tailWord_130559 prefixEnd_130559 39727123419531805044193 := by
  unfold tailWord_130559
  simp only [CollatzResearch.WordTrace]
  refine ⟨4761877934014515547098731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3174585289343010364732487 4761877934014515547098731)
  ·
    refine ⟨7142816901021773320648097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4761877934014515547098731 7142816901021773320648097)
    ·
      refine ⟨5357112675766329990486073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7142816901021773320648097 5357112675766329990486073)
      ·
        refine ⟨4017834506824747492864555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5357112675766329990486073 4017834506824747492864555)
        ·
          refine ⟨6026751760237121239296833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017834506824747492864555 6026751760237121239296833)
          ·
            refine ⟨4520063820177840929472625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6026751760237121239296833 4520063820177840929472625)
            ·
              refine ⟨3390047865133380697104469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4520063820177840929472625 3390047865133380697104469)
              ·
                refine ⟨39727123419531805044193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3390047865133380697104469 39727123419531805044193)
                ·
                  rfl

theorem cell19_130559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_130559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130559 prefixEnd_130559 := by exact prefixLift 130559
  have htrace : WordTrace (prefixWord ++ tailWord_130559) baseStart_130559 baseEnd_130559 := by
    simpa [prefixWord, tailWord_130559, baseEnd_130559] using wordTrace_append hprefix tailTrace_130559
  have hstable : (prefixWord ++ tailWord_130559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130559).length < 2 ^ (prefixWord ++ tailWord_130559).sum := by decide
  have hdescent : baseEnd_130559 < baseStart_130559 := by decide
  rcases family_descends (prefixWord ++ tailWord_130559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130595 : List Nat := [1, 1, 1, 4, 5, 1, 6]
def baseStart_130595 : Nat := 118140960795 + 130595 * 2 ^ 59
def prefixEnd_130595 : Nat := 4983230072969 + 3 ^ 40 * 130595 * 2
def baseEnd_130595 : Nat := 13246025891164796081365

theorem tailTrace_130595 : CollatzResearch.WordTrace tailWord_130595 prefixEnd_130595 13246025891164796081365 := by
  unfold tailWord_130595
  simp only [CollatzResearch.WordTrace]
  refine ⟨4763190961884093695409239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3175460641256062463606159 4763190961884093695409239)
  ·
    refine ⟨7144786442826140543113859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4763190961884093695409239 7144786442826140543113859)
    ·
      refine ⟨10717179664239210814670789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7144786442826140543113859 10717179664239210814670789)
      ·
        refine ⟨2009471187044852027750773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10717179664239210814670789 2009471187044852027750773)
        ·
          refine ⟨188387923785454877601635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2009471187044852027750773 188387923785454877601635)
          ·
            refine ⟨282581885678182316402453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188387923785454877601635 282581885678182316402453)
            ·
              refine ⟨13246025891164796081365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282581885678182316402453 13246025891164796081365)
              ·
                rfl

theorem cell19_130595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_130595 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130595 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130595 prefixEnd_130595 := by exact prefixLift 130595
  have htrace : WordTrace (prefixWord ++ tailWord_130595) baseStart_130595 baseEnd_130595 := by
    simpa [prefixWord, tailWord_130595, baseEnd_130595] using wordTrace_append hprefix tailTrace_130595
  have hstable : (prefixWord ++ tailWord_130595).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130595).length < 2 ^ (prefixWord ++ tailWord_130595).sum := by decide
  have hdescent : baseEnd_130595 < baseStart_130595 := by decide
  rcases family_descends (prefixWord ++ tailWord_130595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130646 : List Nat := [5, 2, 2, 2, 1, 2, 5]
def baseStart_130646 : Nat := 118140960795 + 130646 * 2 ^ 59
def prefixEnd_130646 : Nat := 4983230072969 + 3 ^ 40 * 130646 * 2
def baseEnd_130646 : Nat := 13251198733313793703541

theorem tailTrace_130646 : CollatzResearch.WordTrace tailWord_130646 prefixEnd_130646 13251198733313793703541 := by
  unfold tailWord_130646
  simp only [CollatzResearch.WordTrace]
  refine ⟨297815692793708087844737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3176700723132886270343861 297815692793708087844737)
  ·
    refine ⟨223361769595281065883553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297815692793708087844737 223361769595281065883553)
    ·
      refine ⟨167521327196460799412665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223361769595281065883553 167521327196460799412665)
      ·
        refine ⟨125640995397345599559499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167521327196460799412665 125640995397345599559499)
        ·
          refine ⟨188461493096018399339249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125640995397345599559499 188461493096018399339249)
          ·
            refine ⟨141346119822013799504437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188461493096018399339249 141346119822013799504437)
            ·
              refine ⟨13251198733313793703541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141346119822013799504437 13251198733313793703541)
              ·
                rfl

theorem cell19_130646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 5].length) (baseStart_130646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130646 prefixEnd_130646 := by exact prefixLift 130646
  have htrace : WordTrace (prefixWord ++ tailWord_130646) baseStart_130646 baseEnd_130646 := by
    simpa [prefixWord, tailWord_130646, baseEnd_130646] using wordTrace_append hprefix tailTrace_130646
  have hstable : (prefixWord ++ tailWord_130646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130646).length < 2 ^ (prefixWord ++ tailWord_130646).sum := by decide
  have hdescent : baseEnd_130646 < baseStart_130646 := by decide
  rcases family_descends (prefixWord ++ tailWord_130646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130652 : List Nat := [2, 2, 4, 1, 2, 1, 7]
def baseStart_130652 : Nat := 118140960795 + 130652 * 2 ^ 59
def prefixEnd_130652 : Nat := 4983230072969 + 3 ^ 40 * 130652 * 2
def baseEnd_130652 : Nat := 13251807302978381659091

theorem tailTrace_130652 : CollatzResearch.WordTrace tailWord_130652 prefixEnd_130652 13251807302978381659091 := by
  unfold tailWord_130652
  simp only [CollatzResearch.WordTrace]
  refine ⟨2382634961338796215117105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3176846615118394953489473 2382634961338796215117105)
  ·
    refine ⟨1786976221004097161337829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2382634961338796215117105 1786976221004097161337829)
    ·
      refine ⟨335058041438268217750843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1786976221004097161337829 335058041438268217750843)
      ·
        refine ⟨502587062157402326626265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335058041438268217750843 502587062157402326626265)
        ·
          refine ⟨376940296618051744969699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502587062157402326626265 376940296618051744969699)
          ·
            refine ⟨565410444927077617454549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376940296618051744969699 565410444927077617454549)
            ·
              refine ⟨13251807302978381659091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 565410444927077617454549 13251807302978381659091)
              ·
                rfl

theorem cell19_130652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_130652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130652 prefixEnd_130652 := by exact prefixLift 130652
  have htrace : WordTrace (prefixWord ++ tailWord_130652) baseStart_130652 baseEnd_130652 := by
    simpa [prefixWord, tailWord_130652, baseEnd_130652] using wordTrace_append hprefix tailTrace_130652
  have hstable : (prefixWord ++ tailWord_130652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130652).length < 2 ^ (prefixWord ++ tailWord_130652).sum := by decide
  have hdescent : baseEnd_130652 < baseStart_130652 := by decide
  rcases family_descends (prefixWord ++ tailWord_130652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130669 : List Nat := [1, 5, 1, 1, 4, 1, 2, 4]
def baseStart_130669 : Nat := 118140960795 + 130669 * 2 ^ 59
def prefixEnd_130669 : Nat := 4983230072969 + 3 ^ 40 * 130669 * 2
def baseEnd_130669 : Nat := 39760594751084142599449

theorem tailTrace_130669 : CollatzResearch.WordTrace tailWord_130669 prefixEnd_130669 39760594751084142599449 := by
  unfold tailWord_130669
  simp only [CollatzResearch.WordTrace]
  refine ⟨4765889963616004333603061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3177259975744002889068707 4765889963616004333603061)
  ·
    refine ⟨446802184089000406275287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4765889963616004333603061 446802184089000406275287)
    ·
      refine ⟨670203276133500609412931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446802184089000406275287 670203276133500609412931)
      ·
        refine ⟨1005304914200250914119397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670203276133500609412931 1005304914200250914119397)
        ·
          refine ⟨188494671412547046397387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1005304914200250914119397 188494671412547046397387)
          ·
            refine ⟨282742007118820569596081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188494671412547046397387 282742007118820569596081)
            ·
              refine ⟨212056505339115427197061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282742007118820569596081 212056505339115427197061)
              ·
                refine ⟨39760594751084142599449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212056505339115427197061 39760594751084142599449)
                ·
                  rfl

theorem cell19_130669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_130669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130669 prefixEnd_130669 := by exact prefixLift 130669
  have htrace : WordTrace (prefixWord ++ tailWord_130669) baseStart_130669 baseEnd_130669 := by
    simpa [prefixWord, tailWord_130669, baseEnd_130669] using wordTrace_append hprefix tailTrace_130669
  have hstable : (prefixWord ++ tailWord_130669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130669).length < 2 ^ (prefixWord ++ tailWord_130669).sum := by decide
  have hdescent : baseEnd_130669 < baseStart_130669 := by decide
  rcases family_descends (prefixWord ++ tailWord_130669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130711 : List Nat := [1, 1, 3, 3, 2, 9]
def baseStart_130711 : Nat := 118140960795 + 130711 * 2 ^ 59
def prefixEnd_130711 : Nat := 4983230072969 + 3 ^ 40 * 130711 * 2
def baseEnd_130711 : Nat := 4419263857115609962889

theorem tailTrace_130711 : CollatzResearch.WordTrace tailWord_130711 prefixEnd_130711 4419263857115609962889 := by
  unfold tailWord_130711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4767421829463845506631987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3178281219642563671087991 4767421829463845506631987)
  ·
    refine ⟨7151132744195768259947981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4767421829463845506631987 7151132744195768259947981)
    ·
      refine ⟨2681674779073413097480493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7151132744195768259947981 2681674779073413097480493)
      ·
        refine ⟨1005628042152529911555185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2681674779073413097480493 1005628042152529911555185)
        ·
          refine ⟨754221031614397433666389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005628042152529911555185 754221031614397433666389)
          ·
            refine ⟨4419263857115609962889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 754221031614397433666389 4419263857115609962889)
            ·
              rfl

theorem cell19_130711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 9].length) (baseStart_130711 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130711 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130711 prefixEnd_130711 := by exact prefixLift 130711
  have htrace : WordTrace (prefixWord ++ tailWord_130711) baseStart_130711 baseEnd_130711 := by
    simpa [prefixWord, tailWord_130711, baseEnd_130711] using wordTrace_append hprefix tailTrace_130711
  have hstable : (prefixWord ++ tailWord_130711).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130711).length < 2 ^ (prefixWord ++ tailWord_130711).sum := by decide
  have hdescent : baseEnd_130711 < baseStart_130711 := by decide
  rcases family_descends (prefixWord ++ tailWord_130711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130722 : List Nat := [3, 3, 1, 4, 2, 1, 1, 4]
def baseStart_130722 : Nat := 118140960795 + 130722 * 2 ^ 59
def prefixEnd_130722 : Nat := 4983230072969 + 3 ^ 40 * 130722 * 2
def baseEnd_130722 : Nat := 39776721847195723421527

theorem tailTrace_130722 : CollatzResearch.WordTrace tailWord_130722 prefixEnd_130722 39776721847195723421527 := by
  unfold tailWord_130722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191955758105998596320605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3178548688282662923521613 1191955758105998596320605)
  ·
    refine ⟨446983409289749473620227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1191955758105998596320605 446983409289749473620227)
    ·
      refine ⟨670475113934624210430341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446983409289749473620227 670475113934624210430341)
      ·
        refine ⟨125714083862742039455689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 670475113934624210430341 125714083862742039455689)
        ·
          refine ⟨94285562897056529591767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125714083862742039455689 94285562897056529591767)
          ·
            refine ⟨141428344345584794387651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94285562897056529591767 141428344345584794387651)
            ·
              refine ⟨212142516518377191581477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141428344345584794387651 212142516518377191581477)
              ·
                refine ⟨39776721847195723421527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212142516518377191581477 39776721847195723421527)
                ·
                  rfl

theorem cell19_130722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_130722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130722 prefixEnd_130722 := by exact prefixLift 130722
  have htrace : WordTrace (prefixWord ++ tailWord_130722) baseStart_130722 baseEnd_130722 := by
    simpa [prefixWord, tailWord_130722, baseEnd_130722] using wordTrace_append hprefix tailTrace_130722
  have hstable : (prefixWord ++ tailWord_130722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130722).length < 2 ^ (prefixWord ++ tailWord_130722).sum := by decide
  have hdescent : baseEnd_130722 < baseStart_130722 := by decide
  rcases family_descends (prefixWord ++ tailWord_130722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130836 : List Nat := [2, 4, 4, 1, 1, 1, 2, 4]
def baseStart_130836 : Nat := 118140960795 + 130836 * 2 ^ 59
def prefixEnd_130836 : Nat := 4983230072969 + 3 ^ 40 * 130836 * 2
def baseEnd_130836 : Nat := 39811410318077236887883

theorem tailTrace_130836 : CollatzResearch.WordTrace tailWord_130836 prefixEnd_130836 39811410318077236887883 := by
  unfold tailWord_130836
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385990477005495927466181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3181320636007327903288241 2385990477005495927466181)
  ·
    refine ⟨447373214438530486399909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2385990477005495927466181 447373214438530486399909)
    ·
      refine ⟨83882477707224466199983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447373214438530486399909 83882477707224466199983)
      ·
        refine ⟨125823716560836699299975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83882477707224466199983 125823716560836699299975)
        ·
          refine ⟨188735574841255048949963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125823716560836699299975 188735574841255048949963)
          ·
            refine ⟨283103362261882573424945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188735574841255048949963 283103362261882573424945)
            ·
              refine ⟨212327521696411930068709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283103362261882573424945 212327521696411930068709)
              ·
                refine ⟨39811410318077236887883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212327521696411930068709 39811410318077236887883)
                ·
                  rfl

theorem cell19_130836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_130836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130836 prefixEnd_130836 := by exact prefixLift 130836
  have htrace : WordTrace (prefixWord ++ tailWord_130836) baseStart_130836 baseEnd_130836 := by
    simpa [prefixWord, tailWord_130836, baseEnd_130836] using wordTrace_append hprefix tailTrace_130836
  have hstable : (prefixWord ++ tailWord_130836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130836).length < 2 ^ (prefixWord ++ tailWord_130836).sum := by decide
  have hdescent : baseEnd_130836 < baseStart_130836 := by decide
  rcases family_descends (prefixWord ++ tailWord_130836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130842 : List Nat := [3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_130842 : Nat := 118140960795 + 130842 * 2 ^ 59
def prefixEnd_130842 : Nat := 4983230072969 + 3 ^ 40 * 130842 * 2
def baseEnd_130842 : Nat := 39813236027071000754533

theorem tailTrace_130842 : CollatzResearch.WordTrace tailWord_130842 prefixEnd_130842 39813236027071000754533 := by
  unfold tailWord_130842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193049947997313719912695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3181466527992836586433853 1193049947997313719912695)
  ·
    refine ⟨1789574921995970579869043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1193049947997313719912695 1789574921995970579869043)
    ·
      refine ⟨2684362382993955869803565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1789574921995970579869043 2684362382993955869803565)
      ·
        refine ⟨1006635893622733451176337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2684362382993955869803565 1006635893622733451176337)
        ·
          refine ⟨754976920217050088382253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006635893622733451176337 754976920217050088382253)
          ·
            refine ⟨283116345081393783143345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 754976920217050088382253 283116345081393783143345)
            ·
              refine ⟨212337258811045337357509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283116345081393783143345 212337258811045337357509)
              ·
                refine ⟨39813236027071000754533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212337258811045337357509 39813236027071000754533)
                ·
                  rfl

theorem cell19_130842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_130842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130842 prefixEnd_130842 := by exact prefixLift 130842
  have htrace : WordTrace (prefixWord ++ tailWord_130842) baseStart_130842 baseEnd_130842 := by
    simpa [prefixWord, tailWord_130842, baseEnd_130842] using wordTrace_append hprefix tailTrace_130842
  have hstable : (prefixWord ++ tailWord_130842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130842).length < 2 ^ (prefixWord ++ tailWord_130842).sum := by decide
  have hdescent : baseEnd_130842 < baseStart_130842 := by decide
  rcases family_descends (prefixWord ++ tailWord_130842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130916 : List Nat := [2, 3, 1, 1, 5, 1, 3, 3]
def baseStart_130916 : Nat := 118140960795 + 130916 * 2 ^ 59
def prefixEnd_130916 : Nat := 4983230072969 + 3 ^ 40 * 130916 * 2
def baseEnd_130916 : Nat := 39835753104660755109887

theorem tailTrace_130916 : CollatzResearch.WordTrace tailWord_130916 prefixEnd_130916 39835753104660755109887 := by
  unfold tailWord_130916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2387449396860582758922301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3183265862480777011896401 2387449396860582758922301)
  ·
    refine ⟨895293523822718534595863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2387449396860582758922301 895293523822718534595863)
    ·
      refine ⟨1342940285734077801893795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 895293523822718534595863 1342940285734077801893795)
      ·
        refine ⟨2014410428601116702840693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342940285734077801893795 2014410428601116702840693)
        ·
          refine ⟨188850977681354690891315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2014410428601116702840693 188850977681354690891315)
          ·
            refine ⟨283276466522032036336973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188850977681354690891315 283276466522032036336973)
            ·
              refine ⟨106228674945762013626365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283276466522032036336973 106228674945762013626365)
              ·
                refine ⟨39835753104660755109887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106228674945762013626365 39835753104660755109887)
                ·
                  rfl

theorem cell19_130916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_130916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130916 prefixEnd_130916 := by exact prefixLift 130916
  have htrace : WordTrace (prefixWord ++ tailWord_130916) baseStart_130916 baseEnd_130916 := by
    simpa [prefixWord, tailWord_130916, baseEnd_130916] using wordTrace_append hprefix tailTrace_130916
  have hstable : (prefixWord ++ tailWord_130916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130916).length < 2 ^ (prefixWord ++ tailWord_130916).sum := by decide
  have hdescent : baseEnd_130916 < baseStart_130916 := by decide
  rcases family_descends (prefixWord ++ tailWord_130916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130973 : List Nat := [1, 4, 2, 1, 2, 4, 2, 3]
def baseStart_130973 : Nat := 118140960795 + 130973 * 2 ^ 59
def prefixEnd_130973 : Nat := 4983230072969 + 3 ^ 40 * 130973 * 2
def baseEnd_130973 : Nat := 39853097340101511843065

theorem tailTrace_130973 : CollatzResearch.WordTrace tailWord_130973 prefixEnd_130973 39853097340101511843065 := by
  unfold tailWord_130973
  simp only [CollatzResearch.WordTrace]
  refine ⟨4776977754514664252669573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3184651836343109501779715 4776977754514664252669573)
  ·
    refine ⟨895683328971499547375545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4776977754514664252669573 895683328971499547375545)
    ·
      refine ⟨671762496728624660531659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895683328971499547375545 671762496728624660531659)
      ·
        refine ⟨1007643745092936990797489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671762496728624660531659 1007643745092936990797489)
        ·
          refine ⟨755732808819702743098117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1007643745092936990797489 755732808819702743098117)
          ·
            refine ⟨141699901653694264330897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 755732808819702743098117 141699901653694264330897)
            ·
              refine ⟨106274926240270698248173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141699901653694264330897 106274926240270698248173)
              ·
                refine ⟨39853097340101511843065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106274926240270698248173 39853097340101511843065)
                ·
                  rfl

theorem cell19_130973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 3].length) (baseStart_130973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130973 prefixEnd_130973 := by exact prefixLift 130973
  have htrace : WordTrace (prefixWord ++ tailWord_130973) baseStart_130973 baseEnd_130973 := by
    simpa [prefixWord, tailWord_130973, baseEnd_130973] using wordTrace_append hprefix tailTrace_130973
  have hstable : (prefixWord ++ tailWord_130973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130973).length < 2 ^ (prefixWord ++ tailWord_130973).sum := by decide
  have hdescent : baseEnd_130973 < baseStart_130973 := by decide
  rcases family_descends (prefixWord ++ tailWord_130973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130975 : List Nat := [1, 1, 2, 5, 3, 1, 1, 5]
def baseStart_130975 : Nat := 118140960795 + 130975 * 2 ^ 59
def prefixEnd_130975 : Nat := 4983230072969 + 3 ^ 40 * 130975 * 2
def baseEnd_130975 : Nat := 39853705909766099798615

theorem tailTrace_130975 : CollatzResearch.WordTrace tailWord_130975 prefixEnd_130975 39853705909766099798615 := by
  unfold tailWord_130975
  simp only [CollatzResearch.WordTrace]
  refine ⟨4777050700507418594242379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3184700467004945729494919 4777050700507418594242379)
  ·
    refine ⟨7165576050761127891363569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4777050700507418594242379 7165576050761127891363569)
    ·
      refine ⟨5374182038070845918522677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7165576050761127891363569 5374182038070845918522677)
      ·
        refine ⟨503829566069141804861501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5374182038070845918522677 503829566069141804861501)
        ·
          refine ⟨188936087275928176823063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503829566069141804861501 188936087275928176823063)
          ·
            refine ⟨283404130913892265234595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188936087275928176823063 283404130913892265234595)
            ·
              refine ⟨425106196370838397851893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283404130913892265234595 425106196370838397851893)
              ·
                refine ⟨39853705909766099798615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 425106196370838397851893 39853705909766099798615)
                ·
                  rfl

theorem cell19_130975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_130975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_130975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_130975 prefixEnd_130975 := by exact prefixLift 130975
  have htrace : WordTrace (prefixWord ++ tailWord_130975) baseStart_130975 baseEnd_130975 := by
    simpa [prefixWord, tailWord_130975, baseEnd_130975] using wordTrace_append hprefix tailTrace_130975
  have hstable : (prefixWord ++ tailWord_130975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130975).length < 2 ^ (prefixWord ++ tailWord_130975).sum := by decide
  have hdescent : baseEnd_130975 < baseStart_130975 := by decide
  rcases family_descends (prefixWord ++ tailWord_130975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131108 : List Nat := [2, 3, 1, 4, 2, 1, 6]
def baseStart_131108 : Nat := 118140960795 + 131108 * 2 ^ 59
def prefixEnd_131108 : Nat := 4983230072969 + 3 ^ 40 * 131108 * 2
def baseEnd_131108 : Nat := 13298058597487066280899

theorem tailTrace_131108 : CollatzResearch.WordTrace tailWord_131108 prefixEnd_131108 13298058597487066280899 := by
  unfold tailWord_131108
  simp only [CollatzResearch.WordTrace]
  refine ⟨2390950804512791154416989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3187934406017054872555985 2390950804512791154416989)
  ·
    refine ⟨896606551692296682906371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2390950804512791154416989 896606551692296682906371)
    ·
      refine ⟨1344909827538445024359557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 896606551692296682906371 1344909827538445024359557)
      ·
        refine ⟨252170592663458442067417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1344909827538445024359557 252170592663458442067417)
        ·
          refine ⟨189127944497593831550563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252170592663458442067417 189127944497593831550563)
          ·
            refine ⟨283691916746390747325845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189127944497593831550563 283691916746390747325845)
            ·
              refine ⟨13298058597487066280899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 283691916746390747325845 13298058597487066280899)
              ·
                rfl

theorem cell19_131108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_131108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131108 prefixEnd_131108 := by exact prefixLift 131108
  have htrace : WordTrace (prefixWord ++ tailWord_131108) baseStart_131108 baseEnd_131108 := by
    simpa [prefixWord, tailWord_131108, baseEnd_131108] using wordTrace_append hprefix tailTrace_131108
  have hstable : (prefixWord ++ tailWord_131108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131108).length < 2 ^ (prefixWord ++ tailWord_131108).sum := by decide
  have hdescent : baseEnd_131108 < baseStart_131108 := by decide
  rcases family_descends (prefixWord ++ tailWord_131108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131165 : List Nat := [1, 4, 4, 1, 1, 1, 7]
def baseStart_131165 : Nat := 118140960795 + 131165 * 2 ^ 59
def prefixEnd_131165 : Nat := 4983230072969 + 3 ^ 40 * 131165 * 2
def baseEnd_131165 : Nat := 13303840009300651858625

theorem tailTrace_131165 : CollatzResearch.WordTrace tailWord_131165 prefixEnd_131165 13303840009300651858625 := by
  unfold tailWord_131165
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783980569819081043658949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3189320379879387362439299 4783980569819081043658949)
  ·
    refine ⟨896996356841077695686053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4783980569819081043658949 896996356841077695686053)
    ·
      refine ⟨168186816907702067941135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 896996356841077695686053 168186816907702067941135)
      ·
        refine ⟨252280225361553101911703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168186816907702067941135 252280225361553101911703)
        ·
          refine ⟨378420338042329652867555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252280225361553101911703 378420338042329652867555)
          ·
            refine ⟨567630507063494479301333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378420338042329652867555 567630507063494479301333)
            ·
              refine ⟨13303840009300651858625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 567630507063494479301333 13303840009300651858625)
              ·
                rfl

theorem cell19_131165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_131165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131165 prefixEnd_131165 := by exact prefixLift 131165
  have htrace : WordTrace (prefixWord ++ tailWord_131165) baseStart_131165 baseEnd_131165 := by
    simpa [prefixWord, tailWord_131165, baseEnd_131165] using wordTrace_append hprefix tailTrace_131165
  have hstable : (prefixWord ++ tailWord_131165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131165).length < 2 ^ (prefixWord ++ tailWord_131165).sum := by decide
  have hdescent : baseEnd_131165 < baseStart_131165 := by decide
  rcases family_descends (prefixWord ++ tailWord_131165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131186 : List Nat := [3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_131186 : Nat := 118140960795 + 131186 * 2 ^ 59
def prefixEnd_131186 : Nat := 4983230072969 + 3 ^ 40 * 131186 * 2
def baseEnd_131186 : Nat := 39917910009380129109151

theorem tailTrace_131186 : CollatzResearch.WordTrace tailWord_131186 prefixEnd_131186 39917910009380129109151 := by
  unfold tailWord_131186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196186625685750407543353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3189831001828667753448941 1196186625685750407543353)
  ·
    refine ⟨897139969264312805657515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1196186625685750407543353 897139969264312805657515)
    ·
      refine ⟨1345709953896469208486273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 897139969264312805657515 1345709953896469208486273)
      ·
        refine ⟨1009282465422351906364705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1345709953896469208486273 1009282465422351906364705)
        ·
          refine ⟨756961849066763929773529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009282465422351906364705 756961849066763929773529)
          ·
            refine ⟨567721386800072947330147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756961849066763929773529 567721386800072947330147)
            ·
              refine ⟨851582080200109420995221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567721386800072947330147 851582080200109420995221)
              ·
                refine ⟨39917910009380129109151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 851582080200109420995221 39917910009380129109151)
                ·
                  rfl

theorem cell19_131186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_131186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131186 prefixEnd_131186 := by exact prefixLift 131186
  have htrace : WordTrace (prefixWord ++ tailWord_131186) baseStart_131186 baseEnd_131186 := by
    simpa [prefixWord, tailWord_131186, baseEnd_131186] using wordTrace_append hprefix tailTrace_131186
  have hstable : (prefixWord ++ tailWord_131186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131186).length < 2 ^ (prefixWord ++ tailWord_131186).sum := by decide
  have hdescent : baseEnd_131186 < baseStart_131186 := by decide
  rcases family_descends (prefixWord ++ tailWord_131186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131205 : List Nat := [1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_131205 : Nat := 118140960795 + 131205 * 2 ^ 59
def prefixEnd_131205 : Nat := 4983230072969 + 3 ^ 40 * 131205 * 2
def baseEnd_131205 : Nat := 39923691421193714686877

theorem tailTrace_131205 : CollatzResearch.WordTrace tailWord_131205 prefixEnd_131205 39923691421193714686877 := by
  unfold tailWord_131205
  simp only [CollatzResearch.WordTrace]
  refine ⟨4785439489674167875115069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3190292993116111916743379 4785439489674167875115069)
  ·
    refine ⟨1794539808627812953168151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4785439489674167875115069 1794539808627812953168151)
    ·
      refine ⟨2691809712941719429752227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1794539808627812953168151 2691809712941719429752227)
      ·
        refine ⟨4037714569412579144628341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2691809712941719429752227 4037714569412579144628341)
        ·
          refine ⟨378535740882429294808907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4037714569412579144628341 378535740882429294808907)
          ·
            refine ⟨567803611323643942213361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378535740882429294808907 567803611323643942213361)
            ·
              refine ⟨425852708492732956660021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567803611323643942213361 425852708492732956660021)
              ·
                refine ⟨39923691421193714686877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 425852708492732956660021 39923691421193714686877)
                ·
                  rfl

theorem cell19_131205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_131205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131205 prefixEnd_131205 := by exact prefixLift 131205
  have htrace : WordTrace (prefixWord ++ tailWord_131205) baseStart_131205 baseEnd_131205 := by
    simpa [prefixWord, tailWord_131205, baseEnd_131205] using wordTrace_append hprefix tailTrace_131205
  have hstable : (prefixWord ++ tailWord_131205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131205).length < 2 ^ (prefixWord ++ tailWord_131205).sum := by decide
  have hdescent : baseEnd_131205 < baseStart_131205 := by decide
  rcases family_descends (prefixWord ++ tailWord_131205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131220 : List Nat := [2, 4, 2, 3, 2, 6]
def baseStart_131220 : Nat := 118140960795 + 131220 * 2 ^ 59
def prefixEnd_131220 : Nat := 4983230072969 + 3 ^ 40 * 131220 * 2
def baseEnd_131220 : Nat := 4436472854853124928167

theorem tailTrace_131220 : CollatzResearch.WordTrace tailWord_131220 prefixEnd_131220 4436472854853124928167 := by
  unfold tailWord_131220
  simp only [CollatzResearch.WordTrace]
  refine ⟨2392993292309912718455557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3190657723079883624607409 2392993292309912718455557)
  ·
    refine ⟨448686242308108634710417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2392993292309912718455557 448686242308108634710417)
    ·
      refine ⟨336514681731081476032813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448686242308108634710417 336514681731081476032813)
      ·
        refine ⟨126193005649155553512305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336514681731081476032813 126193005649155553512305)
        ·
          refine ⟨94644754236866665134229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126193005649155553512305 94644754236866665134229)
          ·
            refine ⟨4436472854853124928167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94644754236866665134229 4436472854853124928167)
            ·
              rfl

theorem cell19_131220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 6].length) (baseStart_131220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131220 prefixEnd_131220 := by exact prefixLift 131220
  have htrace : WordTrace (prefixWord ++ tailWord_131220) baseStart_131220 baseEnd_131220 := by
    simpa [prefixWord, tailWord_131220, baseEnd_131220] using wordTrace_append hprefix tailTrace_131220
  have hstable : (prefixWord ++ tailWord_131220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131220).length < 2 ^ (prefixWord ++ tailWord_131220).sum := by decide
  have hdescent : baseEnd_131220 < baseStart_131220 := by decide
  rcases family_descends (prefixWord ++ tailWord_131220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131224 : List Nat := [2, 1, 2, 4, 3, 7]
def baseStart_131224 : Nat := 118140960795 + 131224 * 2 ^ 59
def prefixEnd_131224 : Nat := 4983230072969 + 3 ^ 40 * 131224 * 2
def baseEnd_131224 : Nat := 4436608092556366696067

theorem tailTrace_131224 : CollatzResearch.WordTrace tailWord_131224 prefixEnd_131224 4436608092556366696067 := by
  unfold tailWord_131224
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393066238302667060028363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3190754984403556080037817 2393066238302667060028363)
  ·
    refine ⟨3589599357454000590042545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2393066238302667060028363 3589599357454000590042545)
    ·
      refine ⟨2692199518090500442531909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3589599357454000590042545 2692199518090500442531909)
      ·
        refine ⟨504787409641968832974733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2692199518090500442531909 504787409641968832974733)
        ·
          refine ⟨189295278615738312365525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504787409641968832974733 189295278615738312365525)
          ·
            refine ⟨4436608092556366696067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 189295278615738312365525 4436608092556366696067)
            ·
              rfl

theorem cell19_131224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 7].length) (baseStart_131224 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131224 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131224 prefixEnd_131224 := by exact prefixLift 131224
  have htrace : WordTrace (prefixWord ++ tailWord_131224) baseStart_131224 baseEnd_131224 := by
    simpa [prefixWord, tailWord_131224, baseEnd_131224] using wordTrace_append hprefix tailTrace_131224
  have hstable : (prefixWord ++ tailWord_131224).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131224).length < 2 ^ (prefixWord ++ tailWord_131224).sum := by decide
  have hdescent : baseEnd_131224 < baseStart_131224 := by decide
  rcases family_descends (prefixWord ++ tailWord_131224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131239 : List Nat := [1, 1, 6, 2, 2, 2, 1, 4]
def baseStart_131239 : Nat := 118140960795 + 131239 * 2 ^ 59
def prefixEnd_131239 : Nat := 4983230072969 + 3 ^ 40 * 131239 * 2
def baseEnd_131239 : Nat := 39934037105491709931229

theorem tailTrace_131239 : CollatzResearch.WordTrace tailWord_131239 prefixEnd_131239 39934037105491709931229 := by
  unfold tailWord_131239
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786679571550991681852771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3191119714367327787901847 4786679571550991681852771)
  ·
    refine ⟨7180019357326487522779157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4786679571550991681852771 7180019357326487522779157)
    ·
      refine ⟨336563407374679102630273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7180019357326487522779157 336563407374679102630273)
      ·
        refine ⟨252422555531009326972705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336563407374679102630273 252422555531009326972705)
        ·
          refine ⟨189316916648256995229529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252422555531009326972705 189316916648256995229529)
          ·
            refine ⟨141987687486192746422147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189316916648256995229529 141987687486192746422147)
            ·
              refine ⟨212981531229289119633221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141987687486192746422147 212981531229289119633221)
              ·
                refine ⟨39934037105491709931229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212981531229289119633221 39934037105491709931229)
                ·
                  rfl

theorem cell19_131239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_131239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131239 prefixEnd_131239 := by exact prefixLift 131239
  have htrace : WordTrace (prefixWord ++ tailWord_131239) baseStart_131239 baseEnd_131239 := by
    simpa [prefixWord, tailWord_131239, baseEnd_131239] using wordTrace_append hprefix tailTrace_131239
  have hstable : (prefixWord ++ tailWord_131239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131239).length < 2 ^ (prefixWord ++ tailWord_131239).sum := by decide
  have hdescent : baseEnd_131239 < baseStart_131239 := by decide
  rcases family_descends (prefixWord ++ tailWord_131239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131393 : List Nat := [1, 2, 5, 2, 3, 6]
def baseStart_131393 : Nat := 118140960795 + 131393 * 2 ^ 59
def prefixEnd_131393 : Nat := 4983230072969 + 3 ^ 40 * 131393 * 2
def baseEnd_131393 : Nat := 4442321885518331389843

theorem tailTrace_131393 : CollatzResearch.WordTrace tailWord_131393 prefixEnd_131393 4442321885518331389843 := by
  unfold tailWord_131393
  simp only [CollatzResearch.WordTrace]
  refine ⟨4792296412993075982958833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3194864275328717321972555 4792296412993075982958833)
  ·
    refine ⟨3594222309744806987219125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4792296412993075982958833 3594222309744806987219125)
    ·
      refine ⟨336958341538575655051793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3594222309744806987219125 336958341538575655051793)
      ·
        refine ⟨252718756153931741288845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336958341538575655051793 252718756153931741288845)
        ·
          refine ⟨94769533557724402983317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252718756153931741288845 94769533557724402983317)
          ·
            refine ⟨4442321885518331389843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94769533557724402983317 4442321885518331389843)
            ·
              rfl

theorem cell19_131393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 6].length) (baseStart_131393 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131393 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131393 prefixEnd_131393 := by exact prefixLift 131393
  have htrace : WordTrace (prefixWord ++ tailWord_131393) baseStart_131393 baseEnd_131393 := by
    simpa [prefixWord, tailWord_131393, baseEnd_131393] using wordTrace_append hprefix tailTrace_131393
  have hstable : (prefixWord ++ tailWord_131393).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131393).length < 2 ^ (prefixWord ++ tailWord_131393).sum := by decide
  have hdescent : baseEnd_131393 < baseStart_131393 := by decide
  rcases family_descends (prefixWord ++ tailWord_131393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131412 : List Nat := [2, 4, 1, 1, 2, 4, 1, 4]
def baseStart_131412 : Nat := 118140960795 + 131412 * 2 ^ 59
def prefixEnd_131412 : Nat := 4983230072969 + 3 ^ 40 * 131412 * 2
def baseEnd_131412 : Nat := 39986678381478568086313

theorem tailTrace_131412 : CollatzResearch.WordTrace tailWord_131412 prefixEnd_131412 39986678381478568086313 := by
  unfold tailWord_131412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2396494699962121113950245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3195326266616161485266993 2396494699962121113950245)
  ·
    refine ⟨449342756242897708865671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2396494699962121113950245 449342756242897708865671)
    ·
      refine ⟨674014134364346563298507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449342756242897708865671 674014134364346563298507)
      ·
        refine ⟨1011021201546519844947761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674014134364346563298507 1011021201546519844947761)
        ·
          refine ⟨758265901159889883710821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011021201546519844947761 758265901159889883710821)
          ·
            refine ⟨142174856467479353195779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 758265901159889883710821 142174856467479353195779)
            ·
              refine ⟨213262284701219029793669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142174856467479353195779 213262284701219029793669)
              ·
                refine ⟨39986678381478568086313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213262284701219029793669 39986678381478568086313)
                ·
                  rfl

theorem cell19_131412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_131412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131412 prefixEnd_131412 := by exact prefixLift 131412
  have htrace : WordTrace (prefixWord ++ tailWord_131412) baseStart_131412 baseEnd_131412 := by
    simpa [prefixWord, tailWord_131412, baseEnd_131412] using wordTrace_append hprefix tailTrace_131412
  have hstable : (prefixWord ++ tailWord_131412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131412).length < 2 ^ (prefixWord ++ tailWord_131412).sum := by decide
  have hdescent : baseEnd_131412 < baseStart_131412 := by decide
  rcases family_descends (prefixWord ++ tailWord_131412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131416 : List Nat := [2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_131416 : Nat := 118140960795 + 131416 * 2 ^ 59
def prefixEnd_131416 : Nat := 4983230072969 + 3 ^ 40 * 131416 * 2
def baseEnd_131416 : Nat := 39987895520807743997413

theorem tailTrace_131416 : CollatzResearch.WordTrace tailWord_131416 prefixEnd_131416 39987895520807743997413 := by
  unfold tailWord_131416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2396567645954875455523051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3195423527939833940697401 2396567645954875455523051)
  ·
    refine ⟨3594851468932313183284577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2396567645954875455523051 3594851468932313183284577)
    ·
      refine ⟨2696138601699234887463433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3594851468932313183284577 2696138601699234887463433)
      ·
        refine ⟨2022103951274426165597575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2696138601699234887463433 2022103951274426165597575)
        ·
          refine ⟨3033155926911639248396363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2022103951274426165597575 3033155926911639248396363)
          ·
            refine ⟨4549733890367458872594545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033155926911639248396363 4549733890367458872594545)
            ·
              refine ⟨3412300417775594154445909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4549733890367458872594545 3412300417775594154445909)
              ·
                refine ⟨39987895520807743997413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3412300417775594154445909 39987895520807743997413)
                ·
                  rfl

theorem cell19_131416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_131416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131416 prefixEnd_131416 := by exact prefixLift 131416
  have htrace : WordTrace (prefixWord ++ tailWord_131416) baseStart_131416 baseEnd_131416 := by
    simpa [prefixWord, tailWord_131416, baseEnd_131416] using wordTrace_append hprefix tailTrace_131416
  have hstable : (prefixWord ++ tailWord_131416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131416).length < 2 ^ (prefixWord ++ tailWord_131416).sum := by decide
  have hdescent : baseEnd_131416 < baseStart_131416 := by decide
  rcases family_descends (prefixWord ++ tailWord_131416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131431 : List Nat := [1, 1, 5, 1, 3, 2, 3, 3]
def baseStart_131431 : Nat := 118140960795 + 131431 * 2 ^ 59
def prefixEnd_131431 : Nat := 4983230072969 + 3 ^ 40 * 131431 * 2
def baseEnd_131431 : Nat := 39992459793292153664039

theorem tailTrace_131431 : CollatzResearch.WordTrace tailWord_131431 prefixEnd_131431 39992459793292153664039 := by
  unfold tailWord_131431
  simp only [CollatzResearch.WordTrace]
  refine ⟨4793682386855408472842147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3195788257903605648561431 4793682386855408472842147)
  ·
    refine ⟨7190523580283112709263221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4793682386855408472842147 7190523580283112709263221)
    ·
      refine ⟨674111585651541816493427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7190523580283112709263221 674111585651541816493427)
      ·
        refine ⟨1011167378477312724740141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674111585651541816493427 1011167378477312724740141)
        ·
          refine ⟨379187766928992271777553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1011167378477312724740141 379187766928992271777553)
          ·
            refine ⟨284390825196744203833165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379187766928992271777553 284390825196744203833165)
            ·
              refine ⟨106646559448779076437437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284390825196744203833165 106646559448779076437437)
              ·
                refine ⟨39992459793292153664039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106646559448779076437437 39992459793292153664039)
                ·
                  rfl

theorem cell19_131431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 3].length) (baseStart_131431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131431 prefixEnd_131431 := by exact prefixLift 131431
  have htrace : WordTrace (prefixWord ++ tailWord_131431) baseStart_131431 baseEnd_131431 := by
    simpa [prefixWord, tailWord_131431, baseEnd_131431] using wordTrace_append hprefix tailTrace_131431
  have hstable : (prefixWord ++ tailWord_131431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131431).length < 2 ^ (prefixWord ++ tailWord_131431).sum := by decide
  have hdescent : baseEnd_131431 < baseStart_131431 := by decide
  rcases family_descends (prefixWord ++ tailWord_131431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131433 : List Nat := [1, 2, 1, 1, 1, 3, 7, 3]
def baseStart_131433 : Nat := 118140960795 + 131433 * 2 ^ 59
def prefixEnd_131433 : Nat := 4983230072969 + 3 ^ 40 * 131433 * 2
def baseEnd_131433 : Nat := 39993068362956741619589

theorem tailTrace_131433 : CollatzResearch.WordTrace tailWord_131433 prefixEnd_131433 39993068362956741619589 := by
  unfold tailWord_131433
  simp only [CollatzResearch.WordTrace]
  refine ⟨4793755332848162814414953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3195836888565441876276635 4793755332848162814414953)
  ·
    refine ⟨3595316499636122110811215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4793755332848162814414953 3595316499636122110811215)
    ·
      refine ⟨5392974749454183166216823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595316499636122110811215 5392974749454183166216823)
      ·
        refine ⟨8089462124181274749325235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5392974749454183166216823 8089462124181274749325235)
        ·
          refine ⟨12134193186271912123987853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8089462124181274749325235 12134193186271912123987853)
          ·
            refine ⟨4550322444851967046495445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12134193186271912123987853 4550322444851967046495445)
            ·
              refine ⟨106648182301217977652237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4550322444851967046495445 106648182301217977652237)
              ·
                refine ⟨39993068362956741619589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106648182301217977652237 39993068362956741619589)
                ·
                  rfl

theorem cell19_131433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 3].length) (baseStart_131433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131433 prefixEnd_131433 := by exact prefixLift 131433
  have htrace : WordTrace (prefixWord ++ tailWord_131433) baseStart_131433 baseEnd_131433 := by
    simpa [prefixWord, tailWord_131433, baseEnd_131433] using wordTrace_append hprefix tailTrace_131433
  have hstable : (prefixWord ++ tailWord_131433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131433).length < 2 ^ (prefixWord ++ tailWord_131433).sum := by decide
  have hdescent : baseEnd_131433 < baseStart_131433 := by decide
  rcases family_descends (prefixWord ++ tailWord_131433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131486 : List Nat := [4, 3, 1, 2, 1, 1, 4, 3]
def baseStart_131486 : Nat := 118140960795 + 131486 * 2 ^ 59
def prefixEnd_131486 : Nat := 4983230072969 + 3 ^ 40 * 131486 * 2
def baseEnd_131486 : Nat := 40009195459068322441667

theorem tailTrace_131486 : CollatzResearch.WordTrace tailWord_131486 prefixEnd_131486 40009195459068322441667 := by
  unfold tailWord_131486
  simp only [CollatzResearch.WordTrace]
  refine ⟨599461050207019108261789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3197125601104101910729541 599461050207019108261789)
  ·
    refine ⟨224797893827632165598171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 599461050207019108261789 224797893827632165598171)
    ·
      refine ⟨337196840741448248397257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224797893827632165598171 337196840741448248397257)
      ·
        refine ⟨252897630556086186297943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337196840741448248397257 252897630556086186297943)
        ·
          refine ⟨379346445834129279446915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252897630556086186297943 379346445834129279446915)
          ·
            refine ⟨569019668751193919170373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379346445834129279446915 569019668751193919170373)
            ·
              refine ⟨106691187890848859844445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 569019668751193919170373 106691187890848859844445)
              ·
                refine ⟨40009195459068322441667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106691187890848859844445 40009195459068322441667)
                ·
                  rfl

theorem cell19_131486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_131486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131486 prefixEnd_131486 := by exact prefixLift 131486
  have htrace : WordTrace (prefixWord ++ tailWord_131486) baseStart_131486 baseEnd_131486 := by
    simpa [prefixWord, tailWord_131486, baseEnd_131486] using wordTrace_append hprefix tailTrace_131486
  have hstable : (prefixWord ++ tailWord_131486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131486).length < 2 ^ (prefixWord ++ tailWord_131486).sum := by decide
  have hdescent : baseEnd_131486 < baseStart_131486 := by decide
  rcases family_descends (prefixWord ++ tailWord_131486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131488 : List Nat := [2, 1, 1, 4, 1, 5, 2, 3]
def baseStart_131488 : Nat := 118140960795 + 131488 * 2 ^ 59
def prefixEnd_131488 : Nat := 4983230072969 + 3 ^ 40 * 131488 * 2
def baseEnd_131488 : Nat := 40009804028732910397217

theorem tailTrace_131488 : CollatzResearch.WordTrace tailWord_131488 prefixEnd_131488 40009804028732910397217 := by
  unfold tailWord_131488
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397880673824453603833559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3197174231765938138444745 2397880673824453603833559)
  ·
    refine ⟨3596821010736680405750339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2397880673824453603833559 3596821010736680405750339)
    ·
      refine ⟨5395231516105020608625509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3596821010736680405750339 5395231516105020608625509)
      ·
        refine ⟨1011605909269691364117283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5395231516105020608625509 1011605909269691364117283)
        ·
          refine ⟨1517408863904537046175925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011605909269691364117283 1517408863904537046175925)
          ·
            refine ⟨142257080991050348078993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1517408863904537046175925 142257080991050348078993)
            ·
              refine ⟨106692810743287761059245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142257080991050348078993 106692810743287761059245)
              ·
                refine ⟨40009804028732910397217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106692810743287761059245 40009804028732910397217)
                ·
                  rfl

theorem cell19_131488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_131488 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131488 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131488 prefixEnd_131488 := by exact prefixLift 131488
  have htrace : WordTrace (prefixWord ++ tailWord_131488) baseStart_131488 baseEnd_131488 := by
    simpa [prefixWord, tailWord_131488, baseEnd_131488] using wordTrace_append hprefix tailTrace_131488
  have hstable : (prefixWord ++ tailWord_131488).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131488).length < 2 ^ (prefixWord ++ tailWord_131488).sum := by decide
  have hdescent : baseEnd_131488 < baseStart_131488 := by decide
  rcases family_descends (prefixWord ++ tailWord_131488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131490 : List Nat := [3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_131490 : Nat := 118140960795 + 131490 * 2 ^ 59
def prefixEnd_131490 : Nat := 4983230072969 + 3 ^ 40 * 131490 * 2
def baseEnd_131490 : Nat := 40010412598397498352767

theorem tailTrace_131490 : CollatzResearch.WordTrace tailWord_131490 prefixEnd_131490 40010412598397498352767 := by
  unfold tailWord_131490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198958573410415387309981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3197222862427774366159949 1198958573410415387309981)
  ·
    refine ⟨449609465028905770241243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1198958573410415387309981 449609465028905770241243)
    ·
      refine ⟨674414197543358655361865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449609465028905770241243 674414197543358655361865)
      ·
        refine ⟨505810648157518991521399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674414197543358655361865 505810648157518991521399)
        ·
          refine ⟨758715972236278487282099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505810648157518991521399 758715972236278487282099)
          ·
            refine ⟨1138073958354417730923149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758715972236278487282099 1138073958354417730923149)
            ·
              refine ⟨426777734382906649096181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1138073958354417730923149 426777734382906649096181)
              ·
                refine ⟨40010412598397498352767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 426777734382906649096181 40010412598397498352767)
                ·
                  rfl

theorem cell19_131490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_131490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131490 prefixEnd_131490 := by exact prefixLift 131490
  have htrace : WordTrace (prefixWord ++ tailWord_131490) baseStart_131490 baseEnd_131490 := by
    simpa [prefixWord, tailWord_131490, baseEnd_131490] using wordTrace_append hprefix tailTrace_131490
  have hstable : (prefixWord ++ tailWord_131490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131490).length < 2 ^ (prefixWord ++ tailWord_131490).sum := by decide
  have hdescent : baseEnd_131490 < baseStart_131490 := by decide
  rcases family_descends (prefixWord ++ tailWord_131490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131511 : List Nat := [1, 1, 3, 1, 3, 3, 7]
def baseStart_131511 : Nat := 118140960795 + 131511 * 2 ^ 59
def prefixEnd_131511 : Nat := 4983230072969 + 3 ^ 40 * 131511 * 2
def baseEnd_131511 : Nat := 13338934193291890628681

theorem tailTrace_131511 : CollatzResearch.WordTrace tailWord_131511 prefixEnd_131511 13338934193291890628681 := by
  unfold tailWord_131511
  simp only [CollatzResearch.WordTrace]
  refine ⟨4796600226565582135754387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3197733484377054757169591 4796600226565582135754387)
  ·
    refine ⟨7194900339848373203631581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4796600226565582135754387 7194900339848373203631581)
    ·
      refine ⟨2698087627443139951361843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7194900339848373203631581 2698087627443139951361843)
      ·
        refine ⟨4047131441164709927042765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2698087627443139951361843 4047131441164709927042765)
        ·
          refine ⟨1517674290436766222641037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4047131441164709927042765 1517674290436766222641037)
          ·
            refine ⟨569127858913787333490389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1517674290436766222641037 569127858913787333490389)
            ·
              refine ⟨13338934193291890628681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 569127858913787333490389 13338934193291890628681)
              ·
                rfl

theorem cell19_131511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_131511 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131511 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131511 prefixEnd_131511 := by exact prefixLift 131511
  have htrace : WordTrace (prefixWord ++ tailWord_131511) baseStart_131511 baseEnd_131511 := by
    simpa [prefixWord, tailWord_131511, baseEnd_131511] using wordTrace_append hprefix tailTrace_131511
  have hstable : (prefixWord ++ tailWord_131511).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131511).length < 2 ^ (prefixWord ++ tailWord_131511).sum := by decide
  have hdescent : baseEnd_131511 < baseStart_131511 := by decide
  rcases family_descends (prefixWord ++ tailWord_131511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131528 : List Nat := [2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_131528 : Nat := 118140960795 + 131528 * 2 ^ 59
def prefixEnd_131528 : Nat := 4983230072969 + 3 ^ 40 * 131528 * 2
def baseEnd_131528 : Nat := 40021975422024669508219

theorem tailTrace_131528 : CollatzResearch.WordTrace tailWord_131528 prefixEnd_131528 40021975422024669508219 := by
  unfold tailWord_131528
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398610133751997019561619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3198146845002662692748825 2398610133751997019561619)
  ·
    refine ⟨3597915200627995529342429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2398610133751997019561619 3597915200627995529342429)
    ·
      refine ⟨1349218200235498323503411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3597915200627995529342429 1349218200235498323503411)
      ·
        refine ⟨2023827300353247485255117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349218200235498323503411 2023827300353247485255117)
        ·
          refine ⟨758935237632467806970669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2023827300353247485255117 758935237632467806970669)
          ·
            refine ⟨284600714112175427614001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 758935237632467806970669 284600714112175427614001)
            ·
              refine ⟨213450535584131570710501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284600714112175427614001 213450535584131570710501)
              ·
                refine ⟨40021975422024669508219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213450535584131570710501 40021975422024669508219)
                ·
                  rfl

theorem cell19_131528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_131528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131528 prefixEnd_131528 := by exact prefixLift 131528
  have htrace : WordTrace (prefixWord ++ tailWord_131528) baseStart_131528 baseEnd_131528 := by
    simpa [prefixWord, tailWord_131528, baseEnd_131528] using wordTrace_append hprefix tailTrace_131528
  have hstable : (prefixWord ++ tailWord_131528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131528).length < 2 ^ (prefixWord ++ tailWord_131528).sum := by decide
  have hdescent : baseEnd_131528 < baseStart_131528 := by decide
  rcases family_descends (prefixWord ++ tailWord_131528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131585 : List Nat := [1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_131585 : Nat := 118140960795 + 131585 * 2 ^ 59
def prefixEnd_131585 : Nat := 4983230072969 + 3 ^ 40 * 131585 * 2
def baseEnd_131585 : Nat := 40039319657465426241397

theorem tailTrace_131585 : CollatzResearch.WordTrace tailWord_131585 prefixEnd_131585 40039319657465426241397 := by
  unfold tailWord_131585
  simp only [CollatzResearch.WordTrace]
  refine ⟨4799299228297492773948209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3199532818864995182632139 4799299228297492773948209)
  ·
    refine ⟨3599474421223119580461157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4799299228297492773948209 3599474421223119580461157)
    ·
      refine ⟨674901453979334921336467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3599474421223119580461157 674901453979334921336467)
      ·
        refine ⟨1012352180969002382004701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674901453979334921336467 1012352180969002382004701)
        ·
          refine ⟨379632067863375893251763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1012352180969002382004701 379632067863375893251763)
          ·
            refine ⟨569448101795063839877645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379632067863375893251763 569448101795063839877645)
            ·
              refine ⟨213543038173148939954117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569448101795063839877645 213543038173148939954117)
              ·
                refine ⟨40039319657465426241397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213543038173148939954117 40039319657465426241397)
                ·
                  rfl

theorem cell19_131585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_131585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131585 prefixEnd_131585 := by exact prefixLift 131585
  have htrace : WordTrace (prefixWord ++ tailWord_131585) baseStart_131585 baseEnd_131585 := by
    simpa [prefixWord, tailWord_131585, baseEnd_131585] using wordTrace_append hprefix tailTrace_131585
  have hstable : (prefixWord ++ tailWord_131585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131585).length < 2 ^ (prefixWord ++ tailWord_131585).sum := by decide
  have hdescent : baseEnd_131585 < baseStart_131585 := by decide
  rcases family_descends (prefixWord ++ tailWord_131585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131775 : List Nat := [1, 1, 2, 2, 2, 5, 3, 3]
def baseStart_131775 : Nat := 118140960795 + 131775 * 2 ^ 59
def prefixEnd_131775 : Nat := 4983230072969 + 3 ^ 40 * 131775 * 2
def baseEnd_131775 : Nat := 40097133775601282018657

theorem tailTrace_131775 : CollatzResearch.WordTrace tailWord_131775 prefixEnd_131775 40097133775601282018657 := by
  unfold tailWord_131775
  simp only [CollatzResearch.WordTrace]
  refine ⟨4806229097609155223364779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3204152731739436815576519 4806229097609155223364779)
  ·
    refine ⟨7209343646413732835047169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4806229097609155223364779 7209343646413732835047169)
    ·
      refine ⟨5407007734810299626285377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7209343646413732835047169 5407007734810299626285377)
      ·
        refine ⟨4055255801107724719714033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5407007734810299626285377 4055255801107724719714033)
        ·
          refine ⟨3041441850830793539785525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4055255801107724719714033 3041441850830793539785525)
          ·
            refine ⟨285135173515386894354893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3041441850830793539785525 285135173515386894354893)
            ·
              refine ⟨106925690068270085383085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285135173515386894354893 106925690068270085383085)
              ·
                refine ⟨40097133775601282018657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106925690068270085383085 40097133775601282018657)
                ·
                  rfl

theorem cell19_131775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 3].length) (baseStart_131775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131775 prefixEnd_131775 := by exact prefixLift 131775
  have htrace : WordTrace (prefixWord ++ tailWord_131775) baseStart_131775 baseEnd_131775 := by
    simpa [prefixWord, tailWord_131775, baseEnd_131775] using wordTrace_append hprefix tailTrace_131775
  have hstable : (prefixWord ++ tailWord_131775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131775).length < 2 ^ (prefixWord ++ tailWord_131775).sum := by decide
  have hdescent : baseEnd_131775 < baseStart_131775 := by decide
  rcases family_descends (prefixWord ++ tailWord_131775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131794 : List Nat := [3, 2, 2, 2, 3, 1, 6]
def baseStart_131794 : Nat := 118140960795 + 131794 * 2 ^ 59
def prefixEnd_131794 : Nat := 4983230072969 + 3 ^ 40 * 131794 * 2
def baseEnd_131794 : Nat := 13367638395804955865461

theorem tailTrace_131794 : CollatzResearch.WordTrace tailWord_131794 prefixEnd_131794 13367638395804955865461 := by
  unfold tailWord_131794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201730521135080367076609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3204614723026880978870957 1201730521135080367076609)
  ·
    refine ⟨901297890851310275307457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1201730521135080367076609 901297890851310275307457)
    ·
      refine ⟨675973418138482706480593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 901297890851310275307457 675973418138482706480593)
      ·
        refine ⟨506980063603862029860445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675973418138482706480593 506980063603862029860445)
        ·
          refine ⟨190117523851448261197667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506980063603862029860445 190117523851448261197667)
          ·
            refine ⟨285176285777172391796501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190117523851448261197667 285176285777172391796501)
            ·
              refine ⟨13367638395804955865461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 285176285777172391796501 13367638395804955865461)
              ·
                rfl

theorem cell19_131794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_131794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_131794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_131794 prefixEnd_131794 := by exact prefixLift 131794
  have htrace : WordTrace (prefixWord ++ tailWord_131794) baseStart_131794 baseEnd_131794 := by
    simpa [prefixWord, tailWord_131794, baseEnd_131794] using wordTrace_append hprefix tailTrace_131794
  have hstable : (prefixWord ++ tailWord_131794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131794).length < 2 ^ (prefixWord ++ tailWord_131794).sum := by decide
  have hdescent : baseEnd_131794 < baseStart_131794 := by decide
  rcases family_descends (prefixWord ++ tailWord_131794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
