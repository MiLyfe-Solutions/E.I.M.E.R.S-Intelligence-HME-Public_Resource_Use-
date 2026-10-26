import V185TrunkScan23Chunk0519

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3074388 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_3074388 : Nat := 118140960795 + 3074388 * 2 ^ 59
def prefixEnd_3074388 : Nat := 4983230072969 + 3 ^ 40 * 3074388 * 2
def baseEnd_3074388 : Nat := 526212920805007558837051

theorem tailTrace_3074388 : CollatzResearch.WordTrace tailWord_3074388 prefixEnd_3074388 526212920805007558837051 := by
  unfold tailWord_3074388
  simp only [CollatzResearch.WordTrace]
  refine ⟨56066071193012407256527909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74754761590683209675370545 56066071193012407256527909)
  ·
    refine ⟨10512388348689826360598983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56066071193012407256527909 10512388348689826360598983)
    ·
      refine ⟨15768582523034739540898475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10512388348689826360598983 15768582523034739540898475)
      ·
        refine ⟨23652873784552109311347713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15768582523034739540898475 23652873784552109311347713)
        ·
          refine ⟨17739655338414081983510785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23652873784552109311347713 17739655338414081983510785)
          ·
            refine ⟨13304741503810561487633089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17739655338414081983510785 13304741503810561487633089)
            ·
              refine ⟨9978556127857921115724817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13304741503810561487633089 9978556127857921115724817)
              ·
                refine ⟨7483917095893440836793613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9978556127857921115724817 7483917095893440836793613)
                ·
                  refine ⟨2806468910960040313797605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7483917095893440836793613 2806468910960040313797605)
                  ·
                    refine ⟨526212920805007558837051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2806468910960040313797605 526212920805007558837051)
                    ·
                      rfl

theorem cell23_3074388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_3074388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074388 prefixEnd_3074388 := by exact prefixLift 3074388
  have htrace : WordTrace (prefixWord ++ tailWord_3074388) baseStart_3074388 baseEnd_3074388 := by
    simpa [prefixWord, tailWord_3074388, baseEnd_3074388] using wordTrace_append hprefix tailTrace_3074388
  have hstable : (prefixWord ++ tailWord_3074388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074388).length < 2 ^ (prefixWord ++ tailWord_3074388).sum := by decide
  have hdescent : baseEnd_3074388 < baseStart_3074388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074405 : List Nat := [1, 3, 1, 3, 1, 3, 3, 3, 1, 4]
def baseStart_3074405 : Nat := 118140960795 + 3074405 * 2 ^ 59
def prefixEnd_3074405 : Nat := 4983230072969 + 3 ^ 40 * 3074405 * 2
def baseEnd_3074405 : Nat := 526215830528716369999525

theorem tailTrace_3074405 : CollatzResearch.WordTrace tailWord_3074405 prefixEnd_3074405 526215830528716369999525 := by
  unfold tailWord_3074405
  simp only [CollatzResearch.WordTrace]
  refine ⟨112132762426963226416424669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74755174951308817610949779 112132762426963226416424669)
  ·
    refine ⟨42049785910111209906159251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112132762426963226416424669 42049785910111209906159251)
    ·
      refine ⟨63074678865166814859238877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42049785910111209906159251 63074678865166814859238877)
      ·
        refine ⟨23653004574437555572214579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63074678865166814859238877 23653004574437555572214579)
        ·
          refine ⟨35479506861656333358321869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23653004574437555572214579 35479506861656333358321869)
          ·
            refine ⟨13304815073121125009370701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35479506861656333358321869 13304815073121125009370701)
            ·
              refine ⟨4989305652420421878514013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13304815073121125009370701 4989305652420421878514013)
              ·
                refine ⟨1870989619657658204442755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4989305652420421878514013 1870989619657658204442755)
                ·
                  refine ⟨2806484429486487306664133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1870989619657658204442755 2806484429486487306664133)
                  ·
                    refine ⟨526215830528716369999525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2806484429486487306664133 526215830528716369999525)
                    ·
                      rfl

theorem cell23_3074405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_3074405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074405 prefixEnd_3074405 := by exact prefixLift 3074405
  have htrace : WordTrace (prefixWord ++ tailWord_3074405) baseStart_3074405 baseEnd_3074405 := by
    simpa [prefixWord, tailWord_3074405, baseEnd_3074405] using wordTrace_append hprefix tailTrace_3074405
  have hstable : (prefixWord ++ tailWord_3074405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074405).length < 2 ^ (prefixWord ++ tailWord_3074405).sum := by decide
  have hdescent : baseEnd_3074405 < baseStart_3074405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074428 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_3074428 : Nat := 118140960795 + 3074428 * 2 ^ 59
def prefixEnd_3074428 : Nat := 4983230072969 + 3 ^ 40 * 3074428 * 2
def baseEnd_3074428 : Nat := 1578659301641202520010969

theorem tailTrace_3074428 : CollatzResearch.WordTrace tailWord_3074428 prefixEnd_3074428 1578659301641202520010969 := by
  unfold tailWord_3074428
  simp only [CollatzResearch.WordTrace]
  refine ⟨56066800652939950672255969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74755734203919934229674625 56066800652939950672255969)
  ·
    refine ⟨42050100489704963004191977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56066800652939950672255969 42050100489704963004191977)
    ·
      refine ⟨31537575367278722253143983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42050100489704963004191977 31537575367278722253143983)
      ·
        refine ⟨47306363050918083379715975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31537575367278722253143983 47306363050918083379715975)
        ·
          refine ⟨70959544576377125069573963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47306363050918083379715975 70959544576377125069573963)
          ·
            refine ⟨106439316864565687604360945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70959544576377125069573963 106439316864565687604360945)
            ·
              refine ⟨79829487648424265703270709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106439316864565687604360945 79829487648424265703270709)
              ·
                refine ⟨7484014467039774909681629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79829487648424265703270709 7484014467039774909681629)
                ·
                  refine ⟨2806505425139915591130611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7484014467039774909681629 2806505425139915591130611)
                  ·
                    refine ⟨4209758137709873386695917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2806505425139915591130611 4209758137709873386695917)
                    ·
                      refine ⟨1578659301641202520010969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4209758137709873386695917 1578659301641202520010969)
                      ·
                        rfl

theorem cell23_3074428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_3074428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074428 prefixEnd_3074428 := by exact prefixLift 3074428
  have htrace : WordTrace (prefixWord ++ tailWord_3074428) baseStart_3074428 baseEnd_3074428 := by
    simpa [prefixWord, tailWord_3074428, baseEnd_3074428] using wordTrace_append hprefix tailTrace_3074428
  have hstable : (prefixWord ++ tailWord_3074428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074428).length < 2 ^ (prefixWord ++ tailWord_3074428).sum := by decide
  have hdescent : baseEnd_3074428 < baseStart_3074428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074435 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 6]
def baseStart_3074435 : Nat := 118140960795 + 3074435 * 2 ^ 59
def prefixEnd_3074435 : Nat := 4983230072969 + 3 ^ 40 * 3074435 * 2
def baseEnd_3074435 : Nat := 175406988445087110291493

theorem tailTrace_3074435 : CollatzResearch.WordTrace tailWord_3074435 prefixEnd_3074435 175406988445087110291493 := by
  unfold tailWord_3074435
  simp only [CollatzResearch.WordTrace]
  refine ⟨112133856616854541540016759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74755904411236361026677839 112133856616854541540016759)
  ·
    refine ⟨168200784925281812310025139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112133856616854541540016759 168200784925281812310025139)
    ·
      refine ⟨252301177387922718465037709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168200784925281812310025139 252301177387922718465037709)
      ·
        refine ⟨94612941520471019424389141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252301177387922718465037709 94612941520471019424389141)
        ·
          refine ⟨4434981633772079035518241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94612941520471019424389141 4434981633772079035518241)
          ·
            refine ⟨3326236225329059276638681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4434981633772079035518241 3326236225329059276638681)
            ·
              refine ⟨2494677168996794457479011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3326236225329059276638681 2494677168996794457479011)
              ·
                refine ⟨3742015753495191686218517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494677168996794457479011 3742015753495191686218517)
                ·
                  refine ⟨175406988445087110291493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3742015753495191686218517 175406988445087110291493)
                  ·
                    rfl

theorem cell23_3074435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 6].length) (baseStart_3074435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074435 prefixEnd_3074435 := by exact prefixLift 3074435
  have htrace : WordTrace (prefixWord ++ tailWord_3074435) baseStart_3074435 baseEnd_3074435 := by
    simpa [prefixWord, tailWord_3074435, baseEnd_3074435] using wordTrace_append hprefix tailTrace_3074435
  have hstable : (prefixWord ++ tailWord_3074435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074435).length < 2 ^ (prefixWord ++ tailWord_3074435).sum := by decide
  have hdescent : baseEnd_3074435 < baseStart_3074435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074468 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_3074468 : Nat := 118140960795 + 3074468 * 2 ^ 59
def prefixEnd_3074468 : Nat := 4983230072969 + 3 ^ 40 * 3074468 * 2
def baseEnd_3074468 : Nat := 1578679840867382363510785

theorem tailTrace_3074468 : CollatzResearch.WordTrace tailWord_3074468 prefixEnd_3074468 1578679840867382363510785 := by
  unfold tailWord_3074468
  simp only [CollatzResearch.WordTrace]
  refine ⟨56067530112867494087984029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74756706817156658783978705 56067530112867494087984029)
  ·
    refine ⟨21025323792325310282994011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56067530112867494087984029 21025323792325310282994011)
    ·
      refine ⟨31537985688487965424491017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21025323792325310282994011 31537985688487965424491017)
      ·
        refine ⟨23653489266365974068368263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31537985688487965424491017 23653489266365974068368263)
        ·
          refine ⟨35480233899548961102552395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23653489266365974068368263 35480233899548961102552395)
          ·
            refine ⟨53220350849323441653828593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35480233899548961102552395 53220350849323441653828593)
            ·
              refine ⟨39915263136992581240371445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53220350849323441653828593 39915263136992581240371445)
              ·
                refine ⟨3742055919093054491284823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39915263136992581240371445 3742055919093054491284823)
                ·
                  refine ⟨5613083878639581736927235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742055919093054491284823 5613083878639581736927235)
                  ·
                    refine ⟨8419625817959372605390853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5613083878639581736927235 8419625817959372605390853)
                    ·
                      refine ⟨1578679840867382363510785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8419625817959372605390853 1578679840867382363510785)
                      ·
                        rfl

theorem cell23_3074468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_3074468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074468 prefixEnd_3074468 := by exact prefixLift 3074468
  have htrace : WordTrace (prefixWord ++ tailWord_3074468) baseStart_3074468 baseEnd_3074468 := by
    simpa [prefixWord, tailWord_3074468, baseEnd_3074468] using wordTrace_append hprefix tailTrace_3074468
  have hstable : (prefixWord ++ tailWord_3074468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074468).length < 2 ^ (prefixWord ++ tailWord_3074468).sum := by decide
  have hdescent : baseEnd_3074468 < baseStart_3074468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074472 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_3074472 : Nat := 118140960795 + 3074472 * 2 ^ 59
def prefixEnd_3074472 : Nat := 4983230072969 + 3 ^ 40 * 3074472 * 2
def baseEnd_3074472 : Nat := 1578681894790000347860767

theorem tailTrace_3074472 : CollatzResearch.WordTrace tailWord_3074472 prefixEnd_3074472 1578681894790000347860767 := by
  unfold tailWord_3074472
  simp only [CollatzResearch.WordTrace]
  refine ⟨56067603058860248429556835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74756804078480331239409113 56067603058860248429556835)
  ·
    refine ⟨84101404588290372644335253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56067603058860248429556835 84101404588290372644335253)
    ·
      refine ⟨3942253340076111217703215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84101404588290372644335253 3942253340076111217703215)
      ·
        refine ⟨5913380010114166826554823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3942253340076111217703215 5913380010114166826554823)
        ·
          refine ⟨8870070015171250239832235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5913380010114166826554823 8870070015171250239832235)
          ·
            refine ⟨13305105022756875359748353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8870070015171250239832235 13305105022756875359748353)
            ·
              refine ⟨9978828767067656519811265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13305105022756875359748353 9978828767067656519811265)
              ·
                refine ⟨7484121575300742389858449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9978828767067656519811265 7484121575300742389858449)
                ·
                  refine ⟨5613091181475556792393837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7484121575300742389858449 5613091181475556792393837)
                  ·
                    refine ⟨2104909193053333797147689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5613091181475556792393837 2104909193053333797147689)
                    ·
                      refine ⟨1578681894790000347860767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104909193053333797147689 1578681894790000347860767)
                      ·
                        rfl

theorem cell23_3074472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_3074472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074472 prefixEnd_3074472 := by exact prefixLift 3074472
  have htrace : WordTrace (prefixWord ++ tailWord_3074472) baseStart_3074472 baseEnd_3074472 := by
    simpa [prefixWord, tailWord_3074472, baseEnd_3074472] using wordTrace_append hprefix tailTrace_3074472
  have hstable : (prefixWord ++ tailWord_3074472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074472).length < 2 ^ (prefixWord ++ tailWord_3074472).sum := by decide
  have hdescent : baseEnd_3074472 < baseStart_3074472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074535 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3074535 : Nat := 118140960795 + 3074535 * 2 ^ 59
def prefixEnd_3074535 : Nat := 4983230072969 + 3 ^ 40 * 3074535 * 2
def baseEnd_3074535 : Nat := 1578714244071233601372977

theorem tailTrace_3074535 : CollatzResearch.WordTrace tailWord_3074535 prefixEnd_3074535 1578714244071233601372977 := by
  unfold tailWord_3074535
  simp only [CollatzResearch.WordTrace]
  refine ⟨112137503916492258618657059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74758335944328172412438039 112137503916492258618657059)
  ·
    refine ⟨168206255874738387927985589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112137503916492258618657059 168206255874738387927985589)
    ·
      refine ⟨15769336488256723868248649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168206255874738387927985589 15769336488256723868248649)
      ·
        refine ⟨11827002366192542901186487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15769336488256723868248649 11827002366192542901186487)
        ·
          refine ⟨17740503549288814351779731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11827002366192542901186487 17740503549288814351779731)
          ·
            refine ⟨26610755323933221527669597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17740503549288814351779731 26610755323933221527669597)
            ·
              refine ⟨9979033246474958072876099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26610755323933221527669597 9979033246474958072876099)
              ·
                refine ⟨14968549869712437109314149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9979033246474958072876099 14968549869712437109314149)
                ·
                  refine ⟨2806603100571081957996403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14968549869712437109314149 2806603100571081957996403)
                  ·
                    refine ⟨4209904650856622936994605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2806603100571081957996403 4209904650856622936994605)
                    ·
                      refine ⟨1578714244071233601372977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4209904650856622936994605 1578714244071233601372977)
                      ·
                        rfl

theorem cell23_3074535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3074535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074535 prefixEnd_3074535 := by exact prefixLift 3074535
  have htrace : WordTrace (prefixWord ++ tailWord_3074535) baseStart_3074535 baseEnd_3074535 := by
    simpa [prefixWord, tailWord_3074535, baseEnd_3074535] using wordTrace_append hprefix tailTrace_3074535
  have hstable : (prefixWord ++ tailWord_3074535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074535).length < 2 ^ (prefixWord ++ tailWord_3074535).sum := by decide
  have hdescent : baseEnd_3074535 < baseStart_3074535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074549 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3074549 : Nat := 118140960795 + 3074549 * 2 ^ 59
def prefixEnd_3074549 : Nat := 4983230072969 + 3 ^ 40 * 3074549 * 2
def baseEnd_3074549 : Nat := 1578721432800396546597913

theorem tailTrace_3074549 : CollatzResearch.WordTrace tailWord_3074549 prefixEnd_3074549 1578721432800396546597913 := by
  unfold tailWord_3074549
  simp only [CollatzResearch.WordTrace]
  refine ⟨112138014538441539009666701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74758676358961026006444467 112138014538441539009666701)
  ·
    refine ⟨42051755451915577128625013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112138014538441539009666701 42051755451915577128625013)
    ·
      refine ⟨3942352073617085355808595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42051755451915577128625013 3942352073617085355808595)
      ·
        refine ⟨5913528110425628033712893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3942352073617085355808595 5913528110425628033712893)
        ·
          refine ⟨2217573041409610512642335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5913528110425628033712893 2217573041409610512642335)
          ·
            refine ⟨3326359562114415768963503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217573041409610512642335 3326359562114415768963503)
            ·
              refine ⟨4989539343171623653445255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3326359562114415768963503 4989539343171623653445255)
              ·
                refine ⟨7484309014757435480167883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4989539343171623653445255 7484309014757435480167883)
                ·
                  refine ⟨11226463522136153220251825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7484309014757435480167883 11226463522136153220251825)
                  ·
                    refine ⟨8419847641602114915188869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11226463522136153220251825 8419847641602114915188869)
                    ·
                      refine ⟨1578721432800396546597913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8419847641602114915188869 1578721432800396546597913)
                      ·
                        rfl

theorem cell23_3074549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3074549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074549 prefixEnd_3074549 := by exact prefixLift 3074549
  have htrace : WordTrace (prefixWord ++ tailWord_3074549) baseStart_3074549 baseEnd_3074549 := by
    simpa [prefixWord, tailWord_3074549, baseEnd_3074549] using wordTrace_append hprefix tailTrace_3074549
  have hstable : (prefixWord ++ tailWord_3074549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074549).length < 2 ^ (prefixWord ++ tailWord_3074549).sum := by decide
  have hdescent : baseEnd_3074549 < baseStart_3074549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074552 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 2, 1, 3]
def baseStart_3074552 : Nat := 118140960795 + 3074552 * 2 ^ 59
def prefixEnd_3074552 : Nat := 4983230072969 + 3 ^ 40 * 3074552 * 2
def baseEnd_3074552 : Nat := 1578722973242360034860399

theorem tailTrace_3074552 : CollatzResearch.WordTrace tailWord_3074552 prefixEnd_3074552 1578722973242360034860399 := by
  unfold tailWord_3074552
  simp only [CollatzResearch.WordTrace]
  refine ⟨56069061978715335261012955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74758749304953780348017273 56069061978715335261012955)
  ·
    refine ⟨84103592968073002891519433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56069061978715335261012955 84103592968073002891519433)
    ·
      refine ⟨63077694726054752168639575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84103592968073002891519433 63077694726054752168639575)
      ·
        refine ⟨94616542089082128252959363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63077694726054752168639575 94616542089082128252959363)
        ·
          refine ⟨141924813133623192379439045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94616542089082128252959363 141924813133623192379439045)
          ·
            refine ⟨26610902462554348571144821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141924813133623192379439045 26610902462554348571144821)
            ·
              refine ⟨2494772105864470178544827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26610902462554348571144821 2494772105864470178544827)
              ·
                refine ⟨3742158158796705267817241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494772105864470178544827 3742158158796705267817241)
                ·
                  refine ⟨2806618619097528950862931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3742158158796705267817241 2806618619097528950862931)
                  ·
                    refine ⟨4209927928646293426294397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2806618619097528950862931 4209927928646293426294397)
                    ·
                      refine ⟨1578722973242360034860399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4209927928646293426294397 1578722973242360034860399)
                      ·
                        rfl

theorem cell23_3074552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_3074552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074552 prefixEnd_3074552 := by exact prefixLift 3074552
  have htrace : WordTrace (prefixWord ++ tailWord_3074552) baseStart_3074552 baseEnd_3074552 := by
    simpa [prefixWord, tailWord_3074552, baseEnd_3074552] using wordTrace_append hprefix tailTrace_3074552
  have hstable : (prefixWord ++ tailWord_3074552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074552).length < 2 ^ (prefixWord ++ tailWord_3074552).sum := by decide
  have hdescent : baseEnd_3074552 < baseStart_3074552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074575 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 4, 2, 2]
def baseStart_3074575 : Nat := 118140960795 + 3074575 * 2 ^ 59
def prefixEnd_3074575 : Nat := 4983230072969 + 3 ^ 40 * 3074575 * 2
def baseEnd_3074575 : Nat := 1578734783297413444872793

theorem tailTrace_3074575 : CollatzResearch.WordTrace tailWord_3074575 prefixEnd_3074575 1578734783297413444872793 := by
  unfold tailWord_3074575
  simp only [CollatzResearch.WordTrace]
  refine ⟨112138962836347345450113179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74759308557564896966742119 112138962836347345450113179)
  ·
    refine ⟨168208444254521018175169769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112138962836347345450113179 168208444254521018175169769)
    ·
      refine ⟨126156333190890763631377327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168208444254521018175169769 126156333190890763631377327)
      ·
        refine ⟨189234499786336145447065991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126156333190890763631377327 189234499786336145447065991)
        ·
          refine ⟨283851749679504218170598987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189234499786336145447065991 283851749679504218170598987)
          ·
            refine ⟨425777624519256327255898481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283851749679504218170598987 425777624519256327255898481)
            ·
              refine ⟨319333218389442245441923861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425777624519256327255898481 319333218389442245441923861)
              ·
                refine ⟨14968744612005105255090181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 319333218389442245441923861 14968744612005105255090181)
                ·
                  refine ⟨2806639614750957235329409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14968744612005105255090181 2806639614750957235329409)
                  ·
                    refine ⟨2104979711063217926497057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2806639614750957235329409 2104979711063217926497057)
                    ·
                      refine ⟨1578734783297413444872793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104979711063217926497057 1578734783297413444872793)
                      ·
                        rfl

theorem cell23_3074575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 2, 2].length) (baseStart_3074575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074575 prefixEnd_3074575 := by exact prefixLift 3074575
  have htrace : WordTrace (prefixWord ++ tailWord_3074575) baseStart_3074575 baseEnd_3074575 := by
    simpa [prefixWord, tailWord_3074575, baseEnd_3074575] using wordTrace_append hprefix tailTrace_3074575
  have hstable : (prefixWord ++ tailWord_3074575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074575).length < 2 ^ (prefixWord ++ tailWord_3074575).sum := by decide
  have hdescent : baseEnd_3074575 < baseStart_3074575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074591 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_3074591 : Nat := 118140960795 + 3074591 * 2 ^ 59
def prefixEnd_3074591 : Nat := 4983230072969 + 3 ^ 40 * 3074591 * 2
def baseEnd_3074591 : Nat := 1578742998987885382272719

theorem tailTrace_3074591 : CollatzResearch.WordTrace tailWord_3074591 prefixEnd_3074591 1578742998987885382272719 := by
  unfold tailWord_3074591
  simp only [CollatzResearch.WordTrace]
  refine ⟨112139546404289380182695627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74759697602859586788463751 112139546404289380182695627)
  ·
    refine ⟨168209319606434070274043441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112139546404289380182695627 168209319606434070274043441)
    ·
      refine ⟨126156989704825552705532581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168209319606434070274043441 126156989704825552705532581)
      ·
        refine ⟨23654435569654791132287359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126156989704825552705532581 23654435569654791132287359)
        ·
          refine ⟨35481653354482186698431039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23654435569654791132287359 35481653354482186698431039)
          ·
            refine ⟨53222480031723280047646559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35481653354482186698431039 53222480031723280047646559)
            ·
              refine ⟨79833720047584920071469839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53222480031723280047646559 79833720047584920071469839)
              ·
                refine ⟨119750580071377380107204759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79833720047584920071469839 119750580071377380107204759)
                ·
                  refine ⟨179625870107066070160807139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119750580071377380107204759 179625870107066070160807139)
                  ·
                    refine ⟨269438805160599105241210709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179625870107066070160807139 269438805160599105241210709)
                    ·
                      refine ⟨1578742998987885382272719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 269438805160599105241210709 1578742998987885382272719)
                      ·
                        rfl

theorem cell23_3074591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_3074591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074591 prefixEnd_3074591 := by exact prefixLift 3074591
  have htrace : WordTrace (prefixWord ++ tailWord_3074591) baseStart_3074591 baseEnd_3074591 := by
    simpa [prefixWord, tailWord_3074591, baseEnd_3074591] using wordTrace_append hprefix tailTrace_3074591
  have hstable : (prefixWord ++ tailWord_3074591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074591).length < 2 ^ (prefixWord ++ tailWord_3074591).sum := by decide
  have hdescent : baseEnd_3074591 < baseStart_3074591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074608 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 3]
def baseStart_3074608 : Nat := 118140960795 + 3074608 * 2 ^ 59
def prefixEnd_3074608 : Nat := 4983230072969 + 3 ^ 40 * 3074608 * 2
def baseEnd_3074608 : Nat := 1578751728159011815760141

theorem tailTrace_3074608 : CollatzResearch.WordTrace tailWord_3074608 prefixEnd_3074608 1578751728159011815760141 := by
  unfold tailWord_3074608
  simp only [CollatzResearch.WordTrace]
  refine ⟨56070083222613896043032239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74760110963485194724042985 56070083222613896043032239)
  ·
    refine ⟨84105124833920844064548359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56070083222613896043032239 84105124833920844064548359)
    ·
      refine ⟨126157687250881266096822539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84105124833920844064548359 126157687250881266096822539)
      ·
        refine ⟨189236530876321899145233809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126157687250881266096822539 189236530876321899145233809)
        ·
          refine ⟨141927398157241424358925357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189236530876321899145233809 141927398157241424358925357)
          ·
            refine ⟨53222774308965534134597009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141927398157241424358925357 53222774308965534134597009)
            ·
              refine ⟨39917080731724150600947757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53222774308965534134597009 39917080731724150600947757)
              ·
                refine ⟨14968905274396556475355409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39917080731724150600947757 14968905274396556475355409)
                ·
                  refine ⟨11226678955797417356516557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14968905274396556475355409 11226678955797417356516557)
                  ·
                    refine ⟨4210004608424031508693709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11226678955797417356516557 4210004608424031508693709)
                    ·
                      refine ⟨1578751728159011815760141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4210004608424031508693709 1578751728159011815760141)
                      ·
                        rfl

theorem cell23_3074608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 3].length) (baseStart_3074608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074608 prefixEnd_3074608 := by exact prefixLift 3074608
  have htrace : WordTrace (prefixWord ++ tailWord_3074608) baseStart_3074608 baseEnd_3074608 := by
    simpa [prefixWord, tailWord_3074608, baseEnd_3074608] using wordTrace_append hprefix tailTrace_3074608
  have hstable : (prefixWord ++ tailWord_3074608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074608).length < 2 ^ (prefixWord ++ tailWord_3074608).sum := by decide
  have hdescent : baseEnd_3074608 < baseStart_3074608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074609 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 2, 2, 2]
def baseStart_3074609 : Nat := 118140960795 + 3074609 * 2 ^ 59
def prefixEnd_3074609 : Nat := 4983230072969 + 3 ^ 40 * 3074609 * 2
def baseEnd_3074609 : Nat := 1578752241639666311847637

theorem tailTrace_3074609 : CollatzResearch.WordTrace tailWord_3074609 prefixEnd_3074609 1578752241639666311847637 := by
  unfold tailWord_3074609
  simp only [CollatzResearch.WordTrace]
  refine ⟨112140202918224169256850881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74760135278816112837900587 112140202918224169256850881)
  ·
    refine ⟨84105152188668126942638161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112140202918224169256850881 84105152188668126942638161)
    ·
      refine ⟨63078864141501095206978621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84105152188668126942638161 63078864141501095206978621)
      ·
        refine ⟨23654574053062910702616983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63078864141501095206978621 23654574053062910702616983)
        ·
          refine ⟨35481861079594366053925475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23654574053062910702616983 35481861079594366053925475)
          ·
            refine ⟨53222791619391549080888213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35481861079594366053925475 53222791619391549080888213)
            ·
              refine ⟨2494818357158978863166635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53222791619391549080888213 2494818357158978863166635)
              ·
                refine ⟨3742227535738468294749953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494818357158978863166635 3742227535738468294749953)
                ·
                  refine ⟨2806670651803851221062465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3742227535738468294749953 2806670651803851221062465)
                  ·
                    refine ⟨2105002988852888415796849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2806670651803851221062465 2105002988852888415796849)
                    ·
                      refine ⟨1578752241639666311847637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105002988852888415796849 1578752241639666311847637)
                      ·
                        rfl

theorem cell23_3074609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_3074609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074609 prefixEnd_3074609 := by exact prefixLift 3074609
  have htrace : WordTrace (prefixWord ++ tailWord_3074609) baseStart_3074609 baseEnd_3074609 := by
    simpa [prefixWord, tailWord_3074609, baseEnd_3074609] using wordTrace_append hprefix tailTrace_3074609
  have hstable : (prefixWord ++ tailWord_3074609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074609).length < 2 ^ (prefixWord ++ tailWord_3074609).sum := by decide
  have hdescent : baseEnd_3074609 < baseStart_3074609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074638 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_3074638 : Nat := 118140960795 + 3074638 * 2 ^ 59
def prefixEnd_3074638 : Nat := 4983230072969 + 3 ^ 40 * 3074638 * 2
def baseEnd_3074638 : Nat := 1578767132578646698385003

theorem tailTrace_3074638 : CollatzResearch.WordTrace tailWord_3074638 prefixEnd_3074638 1578767132578646698385003 := by
  unfold tailWord_3074638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14017657579389888401207071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74760840423412738139771045 14017657579389888401207071)
  ·
    refine ⟨21026486369084832601810607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14017657579389888401207071 21026486369084832601810607)
    ·
      refine ⟨31539729553627248902715911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21026486369084832601810607 31539729553627248902715911)
      ·
        refine ⟨47309594330440873354073867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31539729553627248902715911 47309594330440873354073867)
        ·
          refine ⟨70964391495661310031110801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47309594330440873354073867 70964391495661310031110801)
          ·
            refine ⟨53223293621745982523333101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70964391495661310031110801 53223293621745982523333101)
            ·
              refine ⟨19958735108154743446249913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53223293621745982523333101 19958735108154743446249913)
              ·
                refine ⟨14969051331116057584687435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19958735108154743446249913 14969051331116057584687435)
                ·
                  refine ⟨22453576996674086377031153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14969051331116057584687435 22453576996674086377031153)
                  ·
                    refine ⟨16840182747505564782773365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22453576996674086377031153 16840182747505564782773365)
                    ·
                      refine ⟨1578767132578646698385003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16840182747505564782773365 1578767132578646698385003)
                      ·
                        rfl

theorem cell23_3074638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_3074638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074638 prefixEnd_3074638 := by exact prefixLift 3074638
  have htrace : WordTrace (prefixWord ++ tailWord_3074638) baseStart_3074638 baseEnd_3074638 := by
    simpa [prefixWord, tailWord_3074638, baseEnd_3074638] using wordTrace_append hprefix tailTrace_3074638
  have hstable : (prefixWord ++ tailWord_3074638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074638).length < 2 ^ (prefixWord ++ tailWord_3074638).sum := by decide
  have hdescent : baseEnd_3074638 < baseStart_3074638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074735 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 1, 5]
def baseStart_3074735 : Nat := 118140960795 + 3074735 * 2 ^ 59
def prefixEnd_3074735 : Nat := 4983230072969 + 3 ^ 40 * 3074735 * 2
def baseEnd_3074735 : Nat := 526272313400710939624019

theorem tailTrace_3074735 : CollatzResearch.WordTrace tailWord_3074735 prefixEnd_3074735 526272313400710939624019 := by
  unfold tailWord_3074735
  simp only [CollatzResearch.WordTrace]
  refine ⟨112144798515767692775937659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74763199010511795183958439 112144798515767692775937659)
  ·
    refine ⟨168217197773651539163906489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112144798515767692775937659 168217197773651539163906489)
    ·
      refine ⟨126162898330238654372929867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168217197773651539163906489 126162898330238654372929867)
      ·
        refine ⟨189244347495357981559394801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126162898330238654372929867 189244347495357981559394801)
        ·
          refine ⟨141933260621518486169546101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189244347495357981559394801 141933260621518486169546101)
          ·
            refine ⟨13306243183267358078394947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141933260621518486169546101 13306243183267358078394947)
            ·
              refine ⟨19959364774901037117592421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13306243183267358078394947 19959364774901037117592421)
              ·
                refine ⟨3742380895293944459548579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19959364774901037117592421 3742380895293944459548579)
                ·
                  refine ⟨5613571342940916689322869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742380895293944459548579 5613571342940916689322869)
                  ·
                    refine ⟨526272313400710939624019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5613571342940916689322869 526272313400710939624019)
                    ·
                      rfl

theorem cell23_3074735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 5].length) (baseStart_3074735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074735 prefixEnd_3074735 := by exact prefixLift 3074735
  have htrace : WordTrace (prefixWord ++ tailWord_3074735) baseStart_3074735 baseEnd_3074735 := by
    simpa [prefixWord, tailWord_3074735, baseEnd_3074735] using wordTrace_append hprefix tailTrace_3074735
  have hstable : (prefixWord ++ tailWord_3074735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074735).length < 2 ^ (prefixWord ++ tailWord_3074735).sum := by decide
  have hdescent : baseEnd_3074735 < baseStart_3074735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074775 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_3074775 : Nat := 118140960795 + 3074775 * 2 ^ 59
def prefixEnd_3074775 : Nat := 4983230072969 + 3 ^ 40 * 3074775 * 2
def baseEnd_3074775 : Nat := 1578837479428312662371873

theorem tailTrace_3074775 : CollatzResearch.WordTrace tailWord_3074775 prefixEnd_3074775 1578837479428312662371873 := by
  unfold tailWord_3074775
  simp only [CollatzResearch.WordTrace]
  refine ⟨112146257435622779607393779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74764171623748519738262519 112146257435622779607393779)
  ·
    refine ⟨168219386153434169411090669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112146257435622779607393779 168219386153434169411090669)
    ·
      refine ⟨63082269807537813529159001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168219386153434169411090669 63082269807537813529159001)
      ·
        refine ⟨47311702355653360146869251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63082269807537813529159001 47311702355653360146869251)
        ·
          refine ⟨70967553533480040220303877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47311702355653360146869251 70967553533480040220303877)
          ·
            refine ⟨13306416287527507541306977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70967553533480040220303877 13306416287527507541306977)
            ·
              refine ⟨9979812215645630655980233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13306416287527507541306977 9979812215645630655980233)
              ·
                refine ⟨7484859161734222991985175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9979812215645630655980233 7484859161734222991985175)
                ·
                  refine ⟨11227288742601334487977763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7484859161734222991985175 11227288742601334487977763)
                  ·
                    refine ⟨16840933113902001731966645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11227288742601334487977763 16840933113902001731966645)
                    ·
                      refine ⟨1578837479428312662371873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16840933113902001731966645 1578837479428312662371873)
                      ·
                        rfl

theorem cell23_3074775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_3074775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074775 prefixEnd_3074775 := by exact prefixLift 3074775
  have htrace : WordTrace (prefixWord ++ tailWord_3074775) baseStart_3074775 baseEnd_3074775 := by
    simpa [prefixWord, tailWord_3074775, baseEnd_3074775] using wordTrace_append hprefix tailTrace_3074775
  have hstable : (prefixWord ++ tailWord_3074775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074775).length < 2 ^ (prefixWord ++ tailWord_3074775).sum := by decide
  have hdescent : baseEnd_3074775 < baseStart_3074775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074785 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_3074785 : Nat := 118140960795 + 3074785 * 2 ^ 59
def prefixEnd_3074785 : Nat := 4983230072969 + 3 ^ 40 * 3074785 * 2
def baseEnd_3074785 : Nat := 1578842614234857623246827

theorem tailTrace_3074785 : CollatzResearch.WordTrace tailWord_3074785 prefixEnd_3074785 1578842614234857623246827 := by
  unfold tailWord_3074785
  simp only [CollatzResearch.WordTrace]
  refine ⟨112146622165586551315257809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74764414777057700876838539 112146622165586551315257809)
  ·
    refine ⟨84109966624189913486443357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112146622165586551315257809 84109966624189913486443357)
    ·
      refine ⟨31541237484071217557416259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84109966624189913486443357 31541237484071217557416259)
      ·
        refine ⟨47311856226106826336124389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31541237484071217557416259 47311856226106826336124389)
        ·
          refine ⟨8870973042395029938023323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47311856226106826336124389 8870973042395029938023323)
          ·
            refine ⟨13306459563592544907034985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8870973042395029938023323 13306459563592544907034985)
            ·
              refine ⟨9979844672694408680276239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13306459563592544907034985 9979844672694408680276239)
              ·
                refine ⟨14969767009041613020414359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9979844672694408680276239 14969767009041613020414359)
                ·
                  refine ⟨22454650513562419530621539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14969767009041613020414359 22454650513562419530621539)
                  ·
                    refine ⟨33681975770343629295932309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22454650513562419530621539 33681975770343629295932309)
                    ·
                      refine ⟨1578842614234857623246827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33681975770343629295932309 1578842614234857623246827)
                      ·
                        rfl

theorem cell23_3074785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_3074785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074785 prefixEnd_3074785 := by exact prefixLift 3074785
  have htrace : WordTrace (prefixWord ++ tailWord_3074785) baseStart_3074785 baseEnd_3074785 := by
    simpa [prefixWord, tailWord_3074785, baseEnd_3074785] using wordTrace_append hprefix tailTrace_3074785
  have hstable : (prefixWord ++ tailWord_3074785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074785).length < 2 ^ (prefixWord ++ tailWord_3074785).sum := by decide
  have hdescent : baseEnd_3074785 < baseStart_3074785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074789 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 4]
def baseStart_3074789 : Nat := 118140960795 + 3074789 * 2 ^ 59
def prefixEnd_3074789 : Nat := 4983230072969 + 3 ^ 40 * 3074789 * 2
def baseEnd_3074789 : Nat := 1578844668157475607596809

theorem tailTrace_3074789 : CollatzResearch.WordTrace tailWord_3074789 prefixEnd_3074789 1578844668157475607596809 := by
  unfold tailWord_3074789
  simp only [CollatzResearch.WordTrace]
  refine ⟨112146768057572059998403421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74764512038381373332268947 112146768057572059998403421)
  ·
    refine ⟨42055038021589522499401283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112146768057572059998403421 42055038021589522499401283)
    ·
      refine ⟨63082557032384283749101925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42055038021589522499401283 63082557032384283749101925)
      ·
        refine ⟨11827979443572053202956611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63082557032384283749101925 11827979443572053202956611)
        ·
          refine ⟨17741969165358079804434917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11827979443572053202956611 17741969165358079804434917)
          ·
            refine ⟨3326619218504639963331547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17741969165358079804434917 3326619218504639963331547)
            ·
              refine ⟨4989928827756959944997321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3326619218504639963331547 4989928827756959944997321)
              ·
                refine ⟨3742446620817719958747991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4989928827756959944997321 3742446620817719958747991)
                ·
                  refine ⟨5613669931226579938121987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742446620817719958747991 5613669931226579938121987)
                  ·
                    refine ⟨8420504896839869907182981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5613669931226579938121987 8420504896839869907182981)
                    ·
                      refine ⟨1578844668157475607596809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8420504896839869907182981 1578844668157475607596809)
                      ·
                        rfl

theorem cell23_3074789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_3074789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074789 prefixEnd_3074789 := by exact prefixLift 3074789
  have htrace : WordTrace (prefixWord ++ tailWord_3074789) baseStart_3074789 baseEnd_3074789 := by
    simpa [prefixWord, tailWord_3074789, baseEnd_3074789] using wordTrace_append hprefix tailTrace_3074789
  have hstable : (prefixWord ++ tailWord_3074789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074789).length < 2 ^ (prefixWord ++ tailWord_3074789).sum := by decide
  have hdescent : baseEnd_3074789 < baseStart_3074789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074802 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3074802 : Nat := 118140960795 + 3074802 * 2 ^ 59
def prefixEnd_3074802 : Nat := 4983230072969 + 3 ^ 40 * 3074802 * 2
def baseEnd_3074802 : Nat := 1578851343405984056734249

theorem tailTrace_3074802 : CollatzResearch.WordTrace tailWord_3074802 prefixEnd_3074802 1578851343405984056734249 := by
  unfold tailWord_3074802
  simp only [CollatzResearch.WordTrace]
  refine ⟨28036810551631240804656665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74764828137683308812417773 28036810551631240804656665)
  ·
    refine ⟨21027607913723430603492499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28036810551631240804656665 21027607913723430603492499)
    ·
      refine ⟨31541411870585145905238749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21027607913723430603492499 31541411870585145905238749)
      ·
        refine ⟨11828029451469429714464531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31541411870585145905238749 11828029451469429714464531)
        ·
          refine ⟨17742044177204144571696797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11828029451469429714464531 17742044177204144571696797)
          ·
            refine ⟨6653266566451554214386299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17742044177204144571696797 6653266566451554214386299)
            ·
              refine ⟨9979899849677331321579449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6653266566451554214386299 9979899849677331321579449)
              ·
                refine ⟨7484924887257998491184587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9979899849677331321579449 7484924887257998491184587)
                ·
                  refine ⟨11227387330886997736776881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7484924887257998491184587 11227387330886997736776881)
                  ·
                    refine ⟨8420540498165248302582661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11227387330886997736776881 8420540498165248302582661)
                    ·
                      refine ⟨1578851343405984056734249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8420540498165248302582661 1578851343405984056734249)
                      ·
                        rfl

theorem cell23_3074802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3074802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074802 prefixEnd_3074802 := by exact prefixLift 3074802
  have htrace : WordTrace (prefixWord ++ tailWord_3074802) baseStart_3074802 baseEnd_3074802 := by
    simpa [prefixWord, tailWord_3074802, baseEnd_3074802] using wordTrace_append hprefix tailTrace_3074802
  have hstable : (prefixWord ++ tailWord_3074802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074802).length < 2 ^ (prefixWord ++ tailWord_3074802).sum := by decide
  have hdescent : baseEnd_3074802 < baseStart_3074802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074823 : List Nat := [1, 1, 4, 4, 1, 2, 1, 4, 1, 2, 2]
def baseStart_3074823 : Nat := 118140960795 + 3074823 * 2 ^ 59
def prefixEnd_3074823 : Nat := 4983230072969 + 3 ^ 40 * 3074823 * 2
def baseEnd_3074823 : Nat := 1578862126499728474571653

theorem tailTrace_3074823 : CollatzResearch.WordTrace tailWord_3074823 prefixEnd_3074823 1578862126499728474571653 := by
  unfold tailWord_3074823
  simp only [CollatzResearch.WordTrace]
  refine ⟨112148008139448883805141123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74765338759632589203427415 112148008139448883805141123)
  ·
    refine ⟨168222012209173325707711685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112148008139448883805141123 168222012209173325707711685)
    ·
      refine ⟨31541627289219998570195941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168222012209173325707711685 31541627289219998570195941)
      ·
        refine ⟨5914055116728749731911739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31541627289219998570195941 5914055116728749731911739)
        ·
          refine ⟨8871082675093124597867609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5914055116728749731911739 8871082675093124597867609)
          ·
            refine ⟨6653312006319843448400707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8871082675093124597867609 6653312006319843448400707)
            ·
              refine ⟨9979968009479765172601061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6653312006319843448400707 9979968009479765172601061)
              ·
                refine ⟨1871244001777455969862699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9979968009479765172601061 1871244001777455969862699)
                ·
                  refine ⟨2806866002666183954794049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871244001777455969862699 2806866002666183954794049)
                  ·
                    refine ⟨2105149501999637966095537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2806866002666183954794049 2105149501999637966095537)
                    ·
                      refine ⟨1578862126499728474571653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105149501999637966095537 1578862126499728474571653)
                      ·
                        rfl

theorem cell23_3074823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_3074823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074823 prefixEnd_3074823 := by exact prefixLift 3074823
  have htrace : WordTrace (prefixWord ++ tailWord_3074823) baseStart_3074823 baseEnd_3074823 := by
    simpa [prefixWord, tailWord_3074823, baseEnd_3074823] using wordTrace_append hprefix tailTrace_3074823
  have hstable : (prefixWord ++ tailWord_3074823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074823).length < 2 ^ (prefixWord ++ tailWord_3074823).sum := by decide
  have hdescent : baseEnd_3074823 < baseStart_3074823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074839 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3074839 : Nat := 118140960795 + 3074839 * 2 ^ 59
def prefixEnd_3074839 : Nat := 4983230072969 + 3 ^ 40 * 3074839 * 2
def baseEnd_3074839 : Nat := 1578870342190200411971579

theorem tailTrace_3074839 : CollatzResearch.WordTrace tailWord_3074839 prefixEnd_3074839 1578870342190200411971579 := by
  unfold tailWord_3074839
  simp only [CollatzResearch.WordTrace]
  refine ⟨112148591707390918537723571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74765727804927279025149047 112148591707390918537723571)
  ·
    refine ⟨168222887561086377806585357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112148591707390918537723571 168222887561086377806585357)
    ·
      refine ⟨63083582835407391677469509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168222887561086377806585357 63083582835407391677469509)
      ·
        refine ⟨11828171781638885939525533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63083582835407391677469509 11828171781638885939525533)
        ·
          refine ⟨4435564418114582227322075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11828171781638885939525533 4435564418114582227322075)
          ·
            refine ⟨6653346627171873340983113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435564418114582227322075 6653346627171873340983113)
            ·
              refine ⟨4990009970378905005737335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6653346627171873340983113 4990009970378905005737335)
              ·
                refine ⟨7485014955568357508606003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4990009970378905005737335 7485014955568357508606003)
                ·
                  refine ⟨11227522433352536262909005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7485014955568357508606003 11227522433352536262909005)
                  ·
                    refine ⟨4210320912507201098590877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11227522433352536262909005 4210320912507201098590877)
                    ·
                      refine ⟨1578870342190200411971579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4210320912507201098590877 1578870342190200411971579)
                      ·
                        rfl

theorem cell23_3074839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3074839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074839 prefixEnd_3074839 := by exact prefixLift 3074839
  have htrace : WordTrace (prefixWord ++ tailWord_3074839) baseStart_3074839 baseEnd_3074839 := by
    simpa [prefixWord, tailWord_3074839, baseEnd_3074839] using wordTrace_append hprefix tailTrace_3074839
  have hstable : (prefixWord ++ tailWord_3074839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074839).length < 2 ^ (prefixWord ++ tailWord_3074839).sum := by decide
  have hdescent : baseEnd_3074839 < baseStart_3074839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074849 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 1, 3, 2]
def baseStart_3074849 : Nat := 118140960795 + 3074849 * 2 ^ 59
def prefixEnd_3074849 : Nat := 4983230072969 + 3 ^ 40 * 3074849 * 2
def baseEnd_3074849 : Nat := 1578875476996745372846533

theorem tailTrace_3074849 : CollatzResearch.WordTrace tailWord_3074849 prefixEnd_3074849 1578875476996745372846533 := by
  unfold tailWord_3074849
  simp only [CollatzResearch.WordTrace]
  refine ⟨112148956437354690245587601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74765970958236460163725067 112148956437354690245587601)
  ·
    refine ⟨84111717328016017684190701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112148956437354690245587601 84111717328016017684190701)
    ·
      refine ⟨31541893998006006631571513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84111717328016017684190701 31541893998006006631571513)
      ·
        refine ⟨23656420498504504973678635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31541893998006006631571513 23656420498504504973678635)
        ·
          refine ⟨35484630747756757460517953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23656420498504504973678635 35484630747756757460517953)
          ·
            refine ⟨26613473060817568095388465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35484630747756757460517953 26613473060817568095388465)
            ·
              refine ⟨19960104795613176071541349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26613473060817568095388465 19960104795613176071541349)
              ·
                refine ⟨3742519649177470513414003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19960104795613176071541349 3742519649177470513414003)
                ·
                  refine ⟨5613779473766205770121005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742519649177470513414003 5613779473766205770121005)
                  ·
                    refine ⟨2105167302662327163795377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5613779473766205770121005 2105167302662327163795377)
                    ·
                      refine ⟨1578875476996745372846533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105167302662327163795377 1578875476996745372846533)
                      ·
                        rfl

theorem cell23_3074849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_3074849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074849 prefixEnd_3074849 := by exact prefixLift 3074849
  have htrace : WordTrace (prefixWord ++ tailWord_3074849) baseStart_3074849 baseEnd_3074849 := by
    simpa [prefixWord, tailWord_3074849, baseEnd_3074849] using wordTrace_append hprefix tailTrace_3074849
  have hstable : (prefixWord ++ tailWord_3074849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074849).length < 2 ^ (prefixWord ++ tailWord_3074849).sum := by decide
  have hdescent : baseEnd_3074849 < baseStart_3074849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074865 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_3074865 : Nat := 118140960795 + 3074865 * 2 ^ 59
def prefixEnd_3074865 : Nat := 4983230072969 + 3 ^ 40 * 3074865 * 2
def baseEnd_3074865 : Nat := 1578883692687217310246459

theorem tailTrace_3074865 : CollatzResearch.WordTrace tailWord_3074865 prefixEnd_3074865 1578883692687217310246459 := by
  unfold tailWord_3074865
  simp only [CollatzResearch.WordTrace]
  refine ⟨112149540005296724978170049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74766360003531149985446699 112149540005296724978170049)
  ·
    refine ⟨84112155003972543733627537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112149540005296724978170049 84112155003972543733627537)
    ·
      refine ⟨63084116252979407800220653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84112155003972543733627537 63084116252979407800220653)
      ·
        refine ⟨23656543594867277925082745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63084116252979407800220653 23656543594867277925082745)
        ·
          refine ⟨17742407696150458443812059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23656543594867277925082745 17742407696150458443812059)
          ·
            refine ⟨26613611544225687665718089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17742407696150458443812059 26613611544225687665718089)
            ·
              refine ⟨19960208658169265749288567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26613611544225687665718089 19960208658169265749288567)
              ·
                refine ⟨29940312987253898623932851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19960208658169265749288567 29940312987253898623932851)
                ·
                  refine ⟨44910469480880847935899277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29940312987253898623932851 44910469480880847935899277)
                  ·
                    refine ⟨16841426055330317975962229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44910469480880847935899277 16841426055330317975962229)
                    ·
                      refine ⟨1578883692687217310246459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16841426055330317975962229 1578883692687217310246459)
                      ·
                        rfl

theorem cell23_3074865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_3074865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074865 prefixEnd_3074865 := by exact prefixLift 3074865
  have htrace : WordTrace (prefixWord ++ tailWord_3074865) baseStart_3074865 baseEnd_3074865 := by
    simpa [prefixWord, tailWord_3074865, baseEnd_3074865] using wordTrace_append hprefix tailTrace_3074865
  have hstable : (prefixWord ++ tailWord_3074865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074865).length < 2 ^ (prefixWord ++ tailWord_3074865).sum := by decide
  have hdescent : baseEnd_3074865 < baseStart_3074865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074892 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3074892 : Nat := 118140960795 + 3074892 * 2 ^ 59
def prefixEnd_3074892 : Nat := 4983230072969 + 3 ^ 40 * 3074892 * 2
def baseEnd_3074892 : Nat := 1578897556664888704608835

theorem tailTrace_3074892 : CollatzResearch.WordTrace tailWord_3074892 prefixEnd_3074892 1578897556664888704608835 := by
  unfold tailWord_3074892
  simp only [CollatzResearch.WordTrace]
  refine ⟨56075262388099454294701465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74767016517465939059601953 56075262388099454294701465)
  ·
    refine ⟨42056446791074590721026099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56075262388099454294701465 42056446791074590721026099)
    ·
      refine ⟨63084670186611886081539149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42056446791074590721026099 63084670186611886081539149)
      ·
        refine ⟨23656751319979457280577181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63084670186611886081539149 23656751319979457280577181)
        ·
          refine ⟨8871281744992296480216443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23656751319979457280577181 8871281744992296480216443)
          ·
            refine ⟨13306922617488444720324665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8871281744992296480216443 13306922617488444720324665)
            ·
              refine ⟨9980191963116333540243499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13306922617488444720324665 9980191963116333540243499)
              ·
                refine ⟨14970287944674500310365249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9980191963116333540243499 14970287944674500310365249)
                ·
                  refine ⟨11227715958505875232773937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14970287944674500310365249 11227715958505875232773937)
                  ·
                    refine ⟨8420786968879406424580453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11227715958505875232773937 8420786968879406424580453)
                    ·
                      refine ⟨1578897556664888704608835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8420786968879406424580453 1578897556664888704608835)
                      ·
                        rfl

theorem cell23_3074892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3074892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074892 prefixEnd_3074892 := by exact prefixLift 3074892
  have htrace : WordTrace (prefixWord ++ tailWord_3074892) baseStart_3074892 baseEnd_3074892 := by
    simpa [prefixWord, tailWord_3074892, baseEnd_3074892] using wordTrace_append hprefix tailTrace_3074892
  have hstable : (prefixWord ++ tailWord_3074892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074892).length < 2 ^ (prefixWord ++ tailWord_3074892).sum := by decide
  have hdescent : baseEnd_3074892 < baseStart_3074892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074919 : List Nat := [1, 1, 5, 1, 2, 2, 3, 3, 5]
def baseStart_3074919 : Nat := 118140960795 + 3074919 * 2 ^ 59
def prefixEnd_3074919 : Nat := 4983230072969 + 3 ^ 40 * 3074919 * 2
def baseEnd_3074919 : Nat := 175434602293617788774579

theorem tailTrace_3074919 : CollatzResearch.WordTrace tailWord_3074919 prefixEnd_3074919 175434602293617788774579 := by
  unfold tailWord_3074919
  simp only [CollatzResearch.WordTrace]
  refine ⟨112151509547101092200635811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74767673031400728133757207 112151509547101092200635811)
  ·
    refine ⟨168227264320651638300953717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112151509547101092200635811 168227264320651638300953717)
    ·
      refine ⟨15771306030061091090714411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168227264320651638300953717 15771306030061091090714411)
      ·
        refine ⟨23656959045091636636071617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15771306030061091090714411 23656959045091636636071617)
        ·
          refine ⟨17742719283818727477053713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23656959045091636636071617 17742719283818727477053713)
          ·
            refine ⟨13307039462864045607790285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17742719283818727477053713 13307039462864045607790285)
            ·
              refine ⟨4990139798574017102921357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13307039462864045607790285 4990139798574017102921357)
              ·
                refine ⟨1871302424465256413595509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4990139798574017102921357 1871302424465256413595509)
                ·
                  refine ⟨175434602293617788774579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1871302424465256413595509 175434602293617788774579)
                  ·
                    rfl

theorem cell23_3074919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 5].length) (baseStart_3074919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074919 prefixEnd_3074919 := by exact prefixLift 3074919
  have htrace : WordTrace (prefixWord ++ tailWord_3074919) baseStart_3074919 baseEnd_3074919 := by
    simpa [prefixWord, tailWord_3074919, baseEnd_3074919] using wordTrace_append hprefix tailTrace_3074919
  have hstable : (prefixWord ++ tailWord_3074919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074919).length < 2 ^ (prefixWord ++ tailWord_3074919).sum := by decide
  have hdescent : baseEnd_3074919 < baseStart_3074919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075019 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 5, 1, 3]
def baseStart_3075019 : Nat := 118140960795 + 3075019 * 2 ^ 59
def prefixEnd_3075019 : Nat := 4983230072969 + 3 ^ 40 * 3075019 * 2
def baseEnd_3075019 : Nat := 1578962768708009707720751

theorem tailTrace_3075019 : CollatzResearch.WordTrace tailWord_3075019 prefixEnd_3075019 1578962768708009707720751 := by
  unfold tailWord_3075019
  simp only [CollatzResearch.WordTrace]
  refine ⟨112155156846738809279276111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74770104564492539519517407 112155156846738809279276111)
  ·
    refine ⟨168232735270108213918914167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112155156846738809279276111 168232735270108213918914167)
    ·
      refine ⟨252349102905162320878371251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168232735270108213918914167 252349102905162320878371251)
      ·
        refine ⟨378523654357743481317556877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252349102905162320878371251 378523654357743481317556877)
        ·
          refine ⟨141946370384153805494083829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378523654357743481317556877 141946370384153805494083829)
          ·
            refine ⟨13307472223514419265070359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141946370384153805494083829 13307472223514419265070359)
            ·
              refine ⟨19961208335271628897605539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13307472223514419265070359 19961208335271628897605539)
              ·
                refine ⟨29941812502907443346408309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19961208335271628897605539 29941812502907443346408309)
                ·
                  refine ⟨2807044922147572813725779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29941812502907443346408309 2807044922147572813725779)
                  ·
                    refine ⟨4210567383221359220588669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2807044922147572813725779 4210567383221359220588669)
                    ·
                      refine ⟨1578962768708009707720751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4210567383221359220588669 1578962768708009707720751)
                      ·
                        rfl

theorem cell23_3075019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 1, 3].length) (baseStart_3075019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075019 prefixEnd_3075019 := by exact prefixLift 3075019
  have htrace : WordTrace (prefixWord ++ tailWord_3075019) baseStart_3075019 baseEnd_3075019 := by
    simpa [prefixWord, tailWord_3075019, baseEnd_3075019] using wordTrace_append hprefix tailTrace_3075019
  have hstable : (prefixWord ++ tailWord_3075019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075019).length < 2 ^ (prefixWord ++ tailWord_3075019).sum := by decide
  have hdescent : baseEnd_3075019 < baseStart_3075019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075030 : List Nat := [5, 2, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_3075030 : Nat := 118140960795 + 3075030 * 2 ^ 59
def prefixEnd_3075030 : Nat := 4983230072969 + 3 ^ 40 * 3075030 * 2
def baseEnd_3075030 : Nat := 526322805665069721561067

theorem tailTrace_3075030 : CollatzResearch.WordTrace tailWord_3075030 prefixEnd_3075030 526322805665069721561067 := by
  unfold tailWord_3075030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7009722378106184884870409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74770372033132638771951029 7009722378106184884870409)
  ·
    refine ⟨5257291783579638663652807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7009722378106184884870409 5257291783579638663652807)
    ·
      refine ⟨7885937675369457995479211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257291783579638663652807 7885937675369457995479211)
      ·
        refine ⟨11828906513054186993218817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7885937675369457995479211 11828906513054186993218817)
        ·
          refine ⟨8871679884790640244914113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11828906513054186993218817 8871679884790640244914113)
          ·
            refine ⟨6653759913592980183685585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8871679884790640244914113 6653759913592980183685585)
            ·
              refine ⟨4990319935194735137764189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6653759913592980183685585 4990319935194735137764189)
              ·
                refine ⟨1871369975698025676661571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4990319935194735137764189 1871369975698025676661571)
                ·
                  refine ⟨2807054963547038514992357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871369975698025676661571 2807054963547038514992357)
                  ·
                    refine ⟨526322805665069721561067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2807054963547038514992357 526322805665069721561067)
                    ·
                      rfl

theorem cell23_3075030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_3075030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075030 prefixEnd_3075030 := by exact prefixLift 3075030
  have htrace : WordTrace (prefixWord ++ tailWord_3075030) baseStart_3075030 baseEnd_3075030 := by
    simpa [prefixWord, tailWord_3075030, baseEnd_3075030] using wordTrace_append hprefix tailTrace_3075030
  have hstable : (prefixWord ++ tailWord_3075030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075030).length < 2 ^ (prefixWord ++ tailWord_3075030).sum := by decide
  have hdescent : baseEnd_3075030 < baseStart_3075030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075096 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3075096 : Nat := 118140960795 + 3075096 * 2 ^ 59
def prefixEnd_3075096 : Nat := 4983230072969 + 3 ^ 40 * 3075096 * 2
def baseEnd_3075096 : Nat := 1579002306718405906457897

theorem tailTrace_3075096 : CollatzResearch.WordTrace tailWord_3075096 prefixEnd_3075096 1579002306718405906457897 := by
  unfold tailWord_3075096
  simp only [CollatzResearch.WordTrace]
  refine ⟨56078982633729925714914571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74771976844973234286552761 56078982633729925714914571)
  ·
    refine ⟨84118473950594888572371857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56078982633729925714914571 84118473950594888572371857)
    ·
      refine ⟨63088855462946166429278893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84118473950594888572371857 63088855462946166429278893)
      ·
        refine ⟨23658320798604812410979585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63088855462946166429278893 23658320798604812410979585)
        ·
          refine ⟨17743740598953609308234689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23658320798604812410979585 17743740598953609308234689)
          ·
            refine ⟨13307805449215206981176017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17743740598953609308234689 13307805449215206981176017)
            ·
              refine ⟨9980854086911405235882013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13307805449215206981176017 9980854086911405235882013)
              ·
                refine ⟨3742820282591776963455755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9980854086911405235882013 3742820282591776963455755)
                ·
                  refine ⟨5614230423887665445183633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742820282591776963455755 5614230423887665445183633)
                  ·
                    refine ⟨4210672817915749083887725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5614230423887665445183633 4210672817915749083887725)
                    ·
                      refine ⟨1579002306718405906457897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4210672817915749083887725 1579002306718405906457897)
                      ·
                        rfl

theorem cell23_3075096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3075096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075096 prefixEnd_3075096 := by exact prefixLift 3075096
  have htrace : WordTrace (prefixWord ++ tailWord_3075096) baseStart_3075096 baseEnd_3075096 := by
    simpa [prefixWord, tailWord_3075096, baseEnd_3075096] using wordTrace_append hprefix tailTrace_3075096
  have hstable : (prefixWord ++ tailWord_3075096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075096).length < 2 ^ (prefixWord ++ tailWord_3075096).sum := by decide
  have hdescent : baseEnd_3075096 < baseStart_3075096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075136 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 3, 3, 2]
def baseStart_3075136 : Nat := 118140960795 + 3075136 * 2 ^ 59
def prefixEnd_3075136 : Nat := 4983230072969 + 3 ^ 40 * 3075136 * 2
def baseEnd_3075136 : Nat := 1579022845944585749957713

theorem tailTrace_3075136 : CollatzResearch.WordTrace tailWord_3075136 prefixEnd_3075136 1579022845944585749957713 := by
  unfold tailWord_3075136
  simp only [CollatzResearch.WordTrace]
  refine ⟨56079712093657469130642631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74772949458209958840856841 56079712093657469130642631)
  ·
    refine ⟨84119568140486203695963947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56079712093657469130642631 84119568140486203695963947)
    ·
      refine ⟨126179352210729305543945921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84119568140486203695963947 126179352210729305543945921)
      ·
        refine ⟨94634514158046979157959441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126179352210729305543945921 94634514158046979157959441)
        ·
          refine ⟨70975885618535234368469581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94634514158046979157959441 70975885618535234368469581)
          ·
            refine ⟨26615957106950712888176093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70975885618535234368469581 26615957106950712888176093)
            ·
              refine ⟨9980983915106517333066035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26615957106950712888176093 9980983915106517333066035)
              ·
                refine ⟨14971475872659775999599053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9980983915106517333066035 14971475872659775999599053)
                ·
                  refine ⟨5614303452247415999849645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14971475872659775999599053 5614303452247415999849645)
                  ·
                    refine ⟨2105363794592780999943617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5614303452247415999849645 2105363794592780999943617)
                    ·
                      refine ⟨1579022845944585749957713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105363794592780999943617 1579022845944585749957713)
                      ·
                        rfl

theorem cell23_3075136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_3075136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075136 prefixEnd_3075136 := by exact prefixLift 3075136
  have htrace : WordTrace (prefixWord ++ tailWord_3075136) baseStart_3075136 baseEnd_3075136 := by
    simpa [prefixWord, tailWord_3075136, baseEnd_3075136] using wordTrace_append hprefix tailTrace_3075136
  have hstable : (prefixWord ++ tailWord_3075136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075136).length < 2 ^ (prefixWord ++ tailWord_3075136).sum := by decide
  have hdescent : baseEnd_3075136 < baseStart_3075136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075169 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_3075169 : Nat := 118140960795 + 3075169 * 2 ^ 59
def prefixEnd_3075169 : Nat := 4983230072969 + 3 ^ 40 * 3075169 * 2
def baseEnd_3075169 : Nat := 1579039790806184120845061

theorem tailTrace_3075169 : CollatzResearch.WordTrace tailWord_3075169 prefixEnd_3075169 1579039790806184120845061 := by
  unfold tailWord_3075169
  simp only [CollatzResearch.WordTrace]
  refine ⟨112160627796195384897236561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74773751864130256598157707 112160627796195384897236561)
  ·
    refine ⟨84120470847146538672927421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112160627796195384897236561 84120470847146538672927421)
    ·
      refine ⟨31545176567679952002347783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84120470847146538672927421 31545176567679952002347783)
      ·
        refine ⟨47317764851519928003521675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31545176567679952002347783 47317764851519928003521675)
        ·
          refine ⟨70976647277279892005282513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47317764851519928003521675 70976647277279892005282513)
          ·
            refine ⟨53232485457959919003961885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70976647277279892005282513 53232485457959919003961885)
            ·
              refine ⟨19962182046734969626485707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53232485457959919003961885 19962182046734969626485707)
              ·
                refine ⟨29943273070102454439728561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19962182046734969626485707 29943273070102454439728561)
                ·
                  refine ⟨22457454802576840829796421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29943273070102454439728561 22457454802576840829796421)
                  ·
                    refine ⟨4210772775483157655586829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22457454802576840829796421 4210772775483157655586829)
                    ·
                      refine ⟨1579039790806184120845061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4210772775483157655586829 1579039790806184120845061)
                      ·
                        rfl

theorem cell23_3075169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_3075169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075169 prefixEnd_3075169 := by exact prefixLift 3075169
  have htrace : WordTrace (prefixWord ++ tailWord_3075169) baseStart_3075169 baseEnd_3075169 := by
    simpa [prefixWord, tailWord_3075169, baseEnd_3075169] using wordTrace_append hprefix tailTrace_3075169
  have hstable : (prefixWord ++ tailWord_3075169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075169).length < 2 ^ (prefixWord ++ tailWord_3075169).sum := by decide
  have hdescent : baseEnd_3075169 < baseStart_3075169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075183 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 2, 2, 2]
def baseStart_3075183 : Nat := 118140960795 + 3075183 * 2 ^ 59
def prefixEnd_3075183 : Nat := 4983230072969 + 3 ^ 40 * 3075183 * 2
def baseEnd_3075183 : Nat := 1579046979535347066069997

theorem tailTrace_3075183 : CollatzResearch.WordTrace tailWord_3075183 prefixEnd_3075183 1579046979535347066069997 := by
  unfold tailWord_3075183
  simp only [CollatzResearch.WordTrace]
  refine ⟨112161138418144665288246203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74774092278763110192164135 112161138418144665288246203)
  ·
    refine ⟨168241707627216997932369305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112161138418144665288246203 168241707627216997932369305)
    ·
      refine ⟨126181280720412748449276979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168241707627216997932369305 126181280720412748449276979)
      ·
        refine ⟨189271921080619122673915469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126181280720412748449276979 189271921080619122673915469)
        ·
          refine ⟨70976970405232171002718301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189271921080619122673915469 70976970405232171002718301)
          ·
            refine ⟨26616363901962064126019363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70976970405232171002718301 26616363901962064126019363)
            ·
              refine ⟨39924545852943096189029045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26616363901962064126019363 39924545852943096189029045)
              ·
                refine ⟨3742926173713415267721473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39924545852943096189029045 3742926173713415267721473)
                ·
                  refine ⟨2807194630285061450791105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3742926173713415267721473 2807194630285061450791105)
                  ·
                    refine ⟨2105395972713796088093329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2807194630285061450791105 2105395972713796088093329)
                    ·
                      refine ⟨1579046979535347066069997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105395972713796088093329 1579046979535347066069997)
                      ·
                        rfl

theorem cell23_3075183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 2, 2].length) (baseStart_3075183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075183 prefixEnd_3075183 := by exact prefixLift 3075183
  have htrace : WordTrace (prefixWord ++ tailWord_3075183) baseStart_3075183 baseEnd_3075183 := by
    simpa [prefixWord, tailWord_3075183, baseEnd_3075183] using wordTrace_append hprefix tailTrace_3075183
  have hstable : (prefixWord ++ tailWord_3075183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075183).length < 2 ^ (prefixWord ++ tailWord_3075183).sum := by decide
  have hdescent : baseEnd_3075183 < baseStart_3075183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075219 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 2, 5]
def baseStart_3075219 : Nat := 118140960795 + 3075219 * 2 ^ 59
def prefixEnd_3075219 : Nat := 4983230072969 + 3 ^ 40 * 3075219 * 2
def baseEnd_3075219 : Nat := 526355154946302975073277

theorem tailTrace_3075219 : CollatzResearch.WordTrace tailWord_3075219 prefixEnd_3075219 526355154946302975073277 := by
  unfold tailWord_3075219
  simp only [CollatzResearch.WordTrace]
  refine ⟨112162451446014243436556711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74774967630676162291037807 112162451446014243436556711)
  ·
    refine ⟨168243677169021365154835067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112162451446014243436556711 168243677169021365154835067)
    ·
      refine ⟨252365515753532047732252601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168243677169021365154835067 252365515753532047732252601)
      ·
        refine ⟨189274136815149035799189451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252365515753532047732252601 189274136815149035799189451)
        ·
          refine ⟨283911205222723553698784177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189274136815149035799189451 283911205222723553698784177)
          ·
            refine ⟨212933403917042665274088133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283911205222723553698784177 212933403917042665274088133)
            ·
              refine ⟨39925013234445499738891525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212933403917042665274088133 39925013234445499738891525)
              ·
                refine ⟨7485939981458531201042161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39925013234445499738891525 7485939981458531201042161)
                ·
                  refine ⟨5614454986093898400781621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7485939981458531201042161 5614454986093898400781621)
                  ·
                    refine ⟨526355154946302975073277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5614454986093898400781621 526355154946302975073277)
                    ·
                      rfl

theorem cell23_3075219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 5].length) (baseStart_3075219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075219 prefixEnd_3075219 := by exact prefixLift 3075219
  have htrace : WordTrace (prefixWord ++ tailWord_3075219) baseStart_3075219 baseEnd_3075219 := by
    simpa [prefixWord, tailWord_3075219, baseEnd_3075219] using wordTrace_append hprefix tailTrace_3075219
  have hstable : (prefixWord ++ tailWord_3075219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075219).length < 2 ^ (prefixWord ++ tailWord_3075219).sum := by decide
  have hdescent : baseEnd_3075219 < baseStart_3075219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075229 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_3075229 : Nat := 118140960795 + 3075229 * 2 ^ 59
def prefixEnd_3075229 : Nat := 4983230072969 + 3 ^ 40 * 3075229 * 2
def baseEnd_3075229 : Nat := 1579070599645453886094785

theorem tailTrace_3075229 : CollatzResearch.WordTrace tailWord_3075229 prefixEnd_3075229 1579070599645453886094785 := by
  unfold tailWord_3075229
  simp only [CollatzResearch.WordTrace]
  refine ⟨112162816175978015144420741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74775210783985343429613827 112162816175978015144420741)
  ·
    refine ⟨21030528032995877839578889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112162816175978015144420741 21030528032995877839578889)
    ·
      refine ⟨15772896024746908379684167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21030528032995877839578889 15772896024746908379684167)
      ·
        refine ⟨23659344037120362569526251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15772896024746908379684167 23659344037120362569526251)
        ·
          refine ⟨35489016055680543854289377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23659344037120362569526251 35489016055680543854289377)
          ·
            refine ⟨26616762041760407890717033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35489016055680543854289377 26616762041760407890717033)
            ·
              refine ⟨19962571531320305918037775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26616762041760407890717033 19962571531320305918037775)
              ·
                refine ⟨29943857296980458877056663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19962571531320305918037775 29943857296980458877056663)
                ·
                  refine ⟨44915785945470688315584995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29943857296980458877056663 44915785945470688315584995)
                  ·
                    refine ⟨67373678918206032473377493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44915785945470688315584995 67373678918206032473377493)
                    ·
                      refine ⟨1579070599645453886094785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67373678918206032473377493 1579070599645453886094785)
                      ·
                        rfl

theorem cell23_3075229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_3075229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075229 prefixEnd_3075229 := by exact prefixLift 3075229
  have htrace : WordTrace (prefixWord ++ tailWord_3075229) baseStart_3075229 baseEnd_3075229 := by
    simpa [prefixWord, tailWord_3075229, baseEnd_3075229] using wordTrace_append hprefix tailTrace_3075229
  have hstable : (prefixWord ++ tailWord_3075229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075229).length < 2 ^ (prefixWord ++ tailWord_3075229).sum := by decide
  have hdescent : baseEnd_3075229 < baseStart_3075229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075234 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_3075234 : Nat := 118140960795 + 3075234 * 2 ^ 59
def prefixEnd_3075234 : Nat := 4983230072969 + 3 ^ 40 * 3075234 * 2
def baseEnd_3075234 : Nat := 1579073167048726366532263

theorem tailTrace_3075234 : CollatzResearch.WordTrace tailWord_3075234 prefixEnd_3075234 1579073167048726366532263 := by
  unfold tailWord_3075234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28040749635239975249588189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74775332360639933998901837 28040749635239975249588189)
  ·
    refine ⟨10515281113214990718595571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28040749635239975249588189 10515281113214990718595571)
    ·
      refine ⟨15772921669822486077893357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10515281113214990718595571 15772921669822486077893357)
      ·
        refine ⟨5914845626183432279210009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15772921669822486077893357 5914845626183432279210009)
        ·
          refine ⟨4436134219637574209407507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5914845626183432279210009 4436134219637574209407507)
          ·
            refine ⟨6654201329456361314111261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436134219637574209407507 6654201329456361314111261)
            ·
              refine ⟨2495325498546135492791723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6654201329456361314111261 2495325498546135492791723)
              ·
                refine ⟨3742988247819203239187585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495325498546135492791723 3742988247819203239187585)
                ·
                  refine ⟨2807241185864402429390689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3742988247819203239187585 2807241185864402429390689)
                  ·
                    refine ⟨2105430889398301822043017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2807241185864402429390689 2105430889398301822043017)
                    ·
                      refine ⟨1579073167048726366532263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105430889398301822043017 1579073167048726366532263)
                      ·
                        rfl

theorem cell23_3075234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_3075234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075234 prefixEnd_3075234 := by exact prefixLift 3075234
  have htrace : WordTrace (prefixWord ++ tailWord_3075234) baseStart_3075234 baseEnd_3075234 := by
    simpa [prefixWord, tailWord_3075234, baseEnd_3075234] using wordTrace_append hprefix tailTrace_3075234
  have hstable : (prefixWord ++ tailWord_3075234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075234).length < 2 ^ (prefixWord ++ tailWord_3075234).sum := by decide
  have hdescent : baseEnd_3075234 < baseStart_3075234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075256 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 4, 4, 2]
def baseStart_3075256 : Nat := 118140960795 + 3075256 * 2 ^ 59
def prefixEnd_3075256 : Nat := 4983230072969 + 3 ^ 40 * 3075256 * 2
def baseEnd_3075256 : Nat := 1579084463623125280457161

theorem tailTrace_3075256 : CollatzResearch.WordTrace tailWord_3075256 prefixEnd_3075256 1579084463623125280457161 := by
  unfold tailWord_3075256
  simp only [CollatzResearch.WordTrace]
  refine ⟨56081900473440099377826811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74775867297920132503769081 56081900473440099377826811)
  ·
    refine ⟨84122850710160149066740217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56081900473440099377826811 84122850710160149066740217)
    ·
      refine ⟨63092138032620111800055163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84122850710160149066740217 63092138032620111800055163)
      ·
        refine ⟨94638207048930167700082745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63092138032620111800055163 94638207048930167700082745)
        ·
          refine ⟨70978655286697625775062059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94638207048930167700082745 70978655286697625775062059)
          ·
            refine ⟨106467982930046438662593089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70978655286697625775062059 106467982930046438662593089)
            ·
              refine ⟨79850987197534828996944817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106467982930046438662593089 79850987197534828996944817)
              ·
                refine ⟨59888240398151121747708613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79850987197534828996944817 59888240398151121747708613)
                ·
                  refine ⟨11229045074653335327695365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59888240398151121747708613 11229045074653335327695365)
                  ·
                    refine ⟨2105445951497500373942881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11229045074653335327695365 2105445951497500373942881)
                    ·
                      refine ⟨1579084463623125280457161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105445951497500373942881 1579084463623125280457161)
                      ·
                        rfl

theorem cell23_3075256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_3075256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075256 prefixEnd_3075256 := by exact prefixLift 3075256
  have htrace : WordTrace (prefixWord ++ tailWord_3075256) baseStart_3075256 baseEnd_3075256 := by
    simpa [prefixWord, tailWord_3075256, baseEnd_3075256] using wordTrace_append hprefix tailTrace_3075256
  have hstable : (prefixWord ++ tailWord_3075256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075256).length < 2 ^ (prefixWord ++ tailWord_3075256).sum := by decide
  have hdescent : baseEnd_3075256 < baseStart_3075256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075296 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 6]
def baseStart_3075296 : Nat := 118140960795 + 3075296 * 2 ^ 59
def prefixEnd_3075296 : Nat := 4983230072969 + 3 ^ 40 * 3075296 * 2
def baseEnd_3075296 : Nat := 175456111427700569328553

theorem tailTrace_3075296 : CollatzResearch.WordTrace tailWord_3075296 prefixEnd_3075296 175456111427700569328553 := by
  unfold tailWord_3075296
  simp only [CollatzResearch.WordTrace]
  refine ⟨56082629933367642793554871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74776839911156857058073161 56082629933367642793554871)
  ·
    refine ⟨84123944900051464190332307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56082629933367642793554871 84123944900051464190332307)
    ·
      refine ⟨126185917350077196285498461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84123944900051464190332307 126185917350077196285498461)
      ·
        refine ⟨47319719006278948607061923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126185917350077196285498461 47319719006278948607061923)
        ·
          refine ⟨70979578509418422910592885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47319719006278948607061923 70979578509418422910592885)
          ·
            refine ⟨6654335485257977147868083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70979578509418422910592885 6654335485257977147868083)
            ·
              refine ⟨9981503227886965721802125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6654335485257977147868083 9981503227886965721802125)
              ·
                refine ⟨3743063710457612145675797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9981503227886965721802125 3743063710457612145675797)
                ·
                  refine ⟨175456111427700569328553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3743063710457612145675797 175456111427700569328553)
                  ·
                    rfl

theorem cell23_3075296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 6].length) (baseStart_3075296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075296 prefixEnd_3075296 := by exact prefixLift 3075296
  have htrace : WordTrace (prefixWord ++ tailWord_3075296) baseStart_3075296 baseEnd_3075296 := by
    simpa [prefixWord, tailWord_3075296, baseEnd_3075296] using wordTrace_append hprefix tailTrace_3075296
  have hstable : (prefixWord ++ tailWord_3075296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075296).length < 2 ^ (prefixWord ++ tailWord_3075296).sum := by decide
  have hdescent : baseEnd_3075296 < baseStart_3075296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075330 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 6]
def baseStart_3075330 : Nat := 118140960795 + 3075330 * 2 ^ 59
def prefixEnd_3075330 : Nat := 4983230072969 + 3 ^ 40 * 3075330 * 2
def baseEnd_3075330 : Nat := 175458051243506443436869

theorem tailTrace_3075330 : CollatzResearch.WordTrace tailWord_3075330 prefixEnd_3075330 175458051243506443436869 := by
  unfold tailWord_3075330
  simp only [CollatzResearch.WordTrace]
  refine ⟨28041624987153027348461861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74777666632408072929231629 28041624987153027348461861)
  ·
    refine ⟨5257804685091192627836599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28041624987153027348461861 5257804685091192627836599)
    ·
      refine ⟨7886707027636788941754899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257804685091192627836599 7886707027636788941754899)
      ·
        refine ⟨11830060541455183412632349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7886707027636788941754899 11830060541455183412632349)
        ·
          refine ⟨4436272703045693779737131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11830060541455183412632349 4436272703045693779737131)
          ·
            refine ⟨6654409054568540669605697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436272703045693779737131 6654409054568540669605697)
            ·
              refine ⟨4990806790926405502204273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6654409054568540669605697 4990806790926405502204273)
              ·
                refine ⟨3743105093194804126653205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4990806790926405502204273 3743105093194804126653205)
                ·
                  refine ⟨175458051243506443436869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3743105093194804126653205 175458051243506443436869)
                  ·
                    rfl

theorem cell23_3075330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_3075330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075330 prefixEnd_3075330 := by exact prefixLift 3075330
  have htrace : WordTrace (prefixWord ++ tailWord_3075330) baseStart_3075330 baseEnd_3075330 := by
    simpa [prefixWord, tailWord_3075330, baseEnd_3075330] using wordTrace_append hprefix tailTrace_3075330
  have hstable : (prefixWord ++ tailWord_3075330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075330).length < 2 ^ (prefixWord ++ tailWord_3075330).sum := by decide
  have hdescent : baseEnd_3075330 < baseStart_3075330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075333 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 2, 3, 2]
def baseStart_3075333 : Nat := 118140960795 + 3075333 * 2 ^ 59
def prefixEnd_3075333 : Nat := 4983230072969 + 3 ^ 40 * 3075333 * 2
def baseEnd_3075333 : Nat := 1579124001633521479194307

theorem tailTrace_3075333 : CollatzResearch.WordTrace tailWord_3075333 prefixEnd_3075333 1579124001633521479194307 := by
  unfold tailWord_3075333
  simp only [CollatzResearch.WordTrace]
  refine ⟨112166609367601240906206653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74777739578400827270804435 112166609367601240906206653)
  ·
    refine ⟨42062478512850465339827495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112166609367601240906206653 42062478512850465339827495)
    ·
      refine ⟨63093717769275698009741243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42062478512850465339827495 63093717769275698009741243)
      ·
        refine ⟨94640576653913547014611865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63093717769275698009741243 94640576653913547014611865)
        ·
          refine ⟨70980432490435160260958899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94640576653913547014611865 70980432490435160260958899)
          ·
            refine ⟨106470648735652740391438349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70980432490435160260958899 106470648735652740391438349)
            ·
              refine ⟨39926493275869777646789381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106470648735652740391438349 39926493275869777646789381)
              ·
                refine ⟨7486217489225583308773009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39926493275869777646789381 7486217489225583308773009)
                ·
                  refine ⟨5614663116919187481579757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7486217489225583308773009 5614663116919187481579757)
                  ·
                    refine ⟨2105498668844695305592409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5614663116919187481579757 2105498668844695305592409)
                    ·
                      refine ⟨1579124001633521479194307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105498668844695305592409 1579124001633521479194307)
                      ·
                        rfl

theorem cell23_3075333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_3075333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075333 prefixEnd_3075333 := by exact prefixLift 3075333
  have htrace : WordTrace (prefixWord ++ tailWord_3075333) baseStart_3075333 baseEnd_3075333 := by
    simpa [prefixWord, tailWord_3075333, baseEnd_3075333] using wordTrace_append hprefix tailTrace_3075333
  have hstable : (prefixWord ++ tailWord_3075333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075333).length < 2 ^ (prefixWord ++ tailWord_3075333).sum := by decide
  have hdescent : baseEnd_3075333 < baseStart_3075333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075356 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_3075356 : Nat := 118140960795 + 3075356 * 2 ^ 59
def prefixEnd_3075356 : Nat := 4983230072969 + 3 ^ 40 * 3075356 * 2
def baseEnd_3075356 : Nat := 526378603896191629735567

theorem tailTrace_3075356 : CollatzResearch.WordTrace tailWord_3075356 prefixEnd_3075356 526378603896191629735567 := by
  unfold tailWord_3075356
  simp only [CollatzResearch.WordTrace]
  refine ⟨56083724123258957917146961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74778298831011943889529281 56083724123258957917146961)
  ·
    refine ⟨42062793092444218437860221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56083724123258957917146961 42062793092444218437860221)
    ·
      refine ⟨15773547409666581914197583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42062793092444218437860221 15773547409666581914197583)
      ·
        refine ⟨23660321114499872871296375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15773547409666581914197583 23660321114499872871296375)
        ·
          refine ⟨35490481671749809306944563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23660321114499872871296375 35490481671749809306944563)
          ·
            refine ⟨53235722507624713960416845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35490481671749809306944563 53235722507624713960416845)
            ·
              refine ⟨19963395940359267735156317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53235722507624713960416845 19963395940359267735156317)
              ·
                refine ⟨7486273477634725400683619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19963395940359267735156317 7486273477634725400683619)
                ·
                  refine ⟨11229410216452088101025429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7486273477634725400683619 11229410216452088101025429)
                  ·
                    refine ⟨526378603896191629735567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11229410216452088101025429 526378603896191629735567)
                    ·
                      rfl

theorem cell23_3075356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_3075356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075356 prefixEnd_3075356 := by exact prefixLift 3075356
  have htrace : WordTrace (prefixWord ++ tailWord_3075356) baseStart_3075356 baseEnd_3075356 := by
    simpa [prefixWord, tailWord_3075356, baseEnd_3075356] using wordTrace_append hprefix tailTrace_3075356
  have hstable : (prefixWord ++ tailWord_3075356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075356).length < 2 ^ (prefixWord ++ tailWord_3075356).sum := by decide
  have hdescent : baseEnd_3075356 < baseStart_3075356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075376 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 4]
def baseStart_3075376 : Nat := 118140960795 + 3075376 * 2 ^ 59
def prefixEnd_3075376 : Nat := 4983230072969 + 3 ^ 40 * 3075376 * 2
def baseEnd_3075376 : Nat := 1579146081301664810956609

theorem tailTrace_3075376 : CollatzResearch.WordTrace tailWord_3075376 prefixEnd_3075376 1579146081301664810956609 := by
  unfold tailWord_3075376
  simp only [CollatzResearch.WordTrace]
  refine ⟨56084088853222729625010991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74778785137630306166681321 56084088853222729625010991)
  ·
    refine ⟨84126133279834094437516487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56084088853222729625010991 84126133279834094437516487)
    ·
      refine ⟨126189199919751141656274731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84126133279834094437516487 126189199919751141656274731)
      ·
        refine ⟨189283799879626712484412097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126189199919751141656274731 189283799879626712484412097)
        ·
          refine ⟨141962849909720034363309073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189283799879626712484412097 141962849909720034363309073)
          ·
            refine ⟨106472137432290025772481805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141962849909720034363309073 106472137432290025772481805)
            ·
              refine ⟨39927051537108759664680677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106472137432290025772481805 39927051537108759664680677)
              ·
                refine ⟨7486322163207892437127627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39927051537108759664680677 7486322163207892437127627)
                ·
                  refine ⟨11229483244811838655691441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7486322163207892437127627 11229483244811838655691441)
                  ·
                    refine ⟨8422112433608878991768581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11229483244811838655691441 8422112433608878991768581)
                    ·
                      refine ⟨1579146081301664810956609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8422112433608878991768581 1579146081301664810956609)
                      ·
                        rfl

theorem cell23_3075376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_3075376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075376 prefixEnd_3075376 := by exact prefixLift 3075376
  have htrace : WordTrace (prefixWord ++ tailWord_3075376) baseStart_3075376 baseEnd_3075376 := by
    simpa [prefixWord, tailWord_3075376, baseEnd_3075376] using wordTrace_append hprefix tailTrace_3075376
  have hstable : (prefixWord ++ tailWord_3075376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075376).length < 2 ^ (prefixWord ++ tailWord_3075376).sum := by decide
  have hdescent : baseEnd_3075376 < baseStart_3075376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075380 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3075380 : Nat := 118140960795 + 3075380 * 2 ^ 59
def prefixEnd_3075380 : Nat := 4983230072969 + 3 ^ 40 * 3075380 * 2
def baseEnd_3075380 : Nat := 1579148135224282795306591

theorem tailTrace_3075380 : CollatzResearch.WordTrace tailWord_3075380 prefixEnd_3075380 1579148135224282795306591 := by
  unfold tailWord_3075380
  simp only [CollatzResearch.WordTrace]
  refine ⟨56084161799215483966583797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74778882398953978622111729 56084161799215483966583797)
  ·
    refine ⟨5257890168676451621867231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56084161799215483966583797 5257890168676451621867231)
    ·
      refine ⟨7886835253014677432800847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257890168676451621867231 7886835253014677432800847)
      ·
        refine ⟨11830252879522016149201271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7886835253014677432800847 11830252879522016149201271)
        ·
          refine ⟨17745379319283024223801907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11830252879522016149201271 17745379319283024223801907)
          ·
            refine ⟨26618068978924536335702861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17745379319283024223801907 26618068978924536335702861)
            ·
              refine ⟨9981775867096701125888573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26618068978924536335702861 9981775867096701125888573)
              ·
                refine ⟨3743165950161262922208215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9981775867096701125888573 3743165950161262922208215)
                ·
                  refine ⟨5614748925241894383312323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743165950161262922208215 5614748925241894383312323)
                  ·
                    refine ⟨8422123387862841574968485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5614748925241894383312323 8422123387862841574968485)
                    ·
                      refine ⟨1579148135224282795306591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8422123387862841574968485 1579148135224282795306591)
                      ·
                        rfl

theorem cell23_3075380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3075380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075380 prefixEnd_3075380 := by exact prefixLift 3075380
  have htrace : WordTrace (prefixWord ++ tailWord_3075380) baseStart_3075380 baseEnd_3075380 := by
    simpa [prefixWord, tailWord_3075380, baseEnd_3075380] using wordTrace_append hprefix tailTrace_3075380
  have hstable : (prefixWord ++ tailWord_3075380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075380).length < 2 ^ (prefixWord ++ tailWord_3075380).sum := by decide
  have hdescent : baseEnd_3075380 < baseStart_3075380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075431 : List Nat := [1, 1, 5, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_3075431 : Nat := 118140960795 + 3075431 * 2 ^ 59
def prefixEnd_3075431 : Nat := 4983230072969 + 3 ^ 40 * 3075431 * 2
def baseEnd_3075431 : Nat := 1579174322737662095768857

theorem tailTrace_3075431 : CollatzResearch.WordTrace tailWord_3075431 prefixEnd_3075431 1579174322737662095768857 := by
  unfold tailWord_3075431
  simp only [CollatzResearch.WordTrace]
  refine ⟨112170183721246203643274147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74780122480830802428849431 112170183721246203643274147)
  ·
    refine ⟨168255275581869305464911221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112170183721246203643274147 168255275581869305464911221)
    ·
      refine ⟨15773932085800247387335427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168255275581869305464911221 15773932085800247387335427)
      ·
        refine ⟨23660898128700371081003141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15773932085800247387335427 23660898128700371081003141)
        ·
          refine ⟨4436418399131319577688089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23660898128700371081003141 4436418399131319577688089)
          ·
            refine ⟨3327313799348489683266067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4436418399131319577688089 3327313799348489683266067)
            ·
              refine ⟨4990970699022734524899101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327313799348489683266067 4990970699022734524899101)
              ·
                refine ⟨1871614012133525446837163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4990970699022734524899101 1871614012133525446837163)
                ·
                  refine ⟨2807421018200288170255745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871614012133525446837163 2807421018200288170255745)
                  ·
                    refine ⟨2105565763650216127691809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2807421018200288170255745 2105565763650216127691809)
                    ·
                      refine ⟨1579174322737662095768857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105565763650216127691809 1579174322737662095768857)
                      ·
                        rfl

theorem cell23_3075431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_3075431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075431 prefixEnd_3075431 := by exact prefixLift 3075431
  have htrace : WordTrace (prefixWord ++ tailWord_3075431) baseStart_3075431 baseEnd_3075431 := by
    simpa [prefixWord, tailWord_3075431, baseEnd_3075431] using wordTrace_append hprefix tailTrace_3075431
  have hstable : (prefixWord ++ tailWord_3075431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075431).length < 2 ^ (prefixWord ++ tailWord_3075431).sum := by decide
  have hdescent : baseEnd_3075431 < baseStart_3075431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075440 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 1, 3, 2]
def baseStart_3075440 : Nat := 118140960795 + 3075440 * 2 ^ 59
def prefixEnd_3075440 : Nat := 4983230072969 + 3 ^ 40 * 3075440 * 2
def baseEnd_3075440 : Nat := 1579178944063552560556315

theorem tailTrace_3075440 : CollatzResearch.WordTrace tailWord_3075440 prefixEnd_3075440 1579178944063552560556315 := by
  unfold tailWord_3075440
  simp only [CollatzResearch.WordTrace]
  refine ⟨56085255989106799090175887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74780341318809065453567849 56085255989106799090175887)
  ·
    refine ⟨84127883983660198635263831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56085255989106799090175887 84127883983660198635263831)
    ·
      refine ⟨126191825975490297952895747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84127883983660198635263831 126191825975490297952895747)
      ·
        refine ⟨189287738963235446929343621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126191825975490297952895747 189287738963235446929343621)
        ·
          refine ⟨35491451055606646299251929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189287738963235446929343621 35491451055606646299251929)
          ·
            refine ⟨26618588291704984724438947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35491451055606646299251929 26618588291704984724438947)
            ·
              refine ⟨39927882437557477086658421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26618588291704984724438947 39927882437557477086658421)
              ·
                refine ⟨3743238978521013476874227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39927882437557477086658421 3743238978521013476874227)
                ·
                  refine ⟨5614858467781520215311341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743238978521013476874227 5614858467781520215311341)
                  ·
                    refine ⟨2105571925418070080741753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5614858467781520215311341 2105571925418070080741753)
                    ·
                      refine ⟨1579178944063552560556315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105571925418070080741753 1579178944063552560556315)
                      ·
                        rfl

theorem cell23_3075440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 3, 2].length) (baseStart_3075440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075440 prefixEnd_3075440 := by exact prefixLift 3075440
  have htrace : WordTrace (prefixWord ++ tailWord_3075440) baseStart_3075440 baseEnd_3075440 := by
    simpa [prefixWord, tailWord_3075440, baseEnd_3075440] using wordTrace_append hprefix tailTrace_3075440
  have hstable : (prefixWord ++ tailWord_3075440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075440).length < 2 ^ (prefixWord ++ tailWord_3075440).sum := by decide
  have hdescent : baseEnd_3075440 < baseStart_3075440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075464 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 2, 1, 3]
def baseStart_3075464 : Nat := 118140960795 + 3075464 * 2 ^ 59
def prefixEnd_3075464 : Nat := 4983230072969 + 3 ^ 40 * 3075464 * 2
def baseEnd_3075464 : Nat := 1579191267599260466656205

theorem tailTrace_3075464 : CollatzResearch.WordTrace tailWord_3075464 prefixEnd_3075464 1579191267599260466656205 := by
  unfold tailWord_3075464
  simp only [CollatzResearch.WordTrace]
  refine ⟨56085693665063325139612723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74780924886751100186150297 56085693665063325139612723)
  ·
    refine ⟨84128540497594987709419085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56085693665063325139612723 84128540497594987709419085)
    ·
      refine ⟨31548202686598120391032157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84128540497594987709419085 31548202686598120391032157)
      ·
        refine ⟨11830576007474295146637059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31548202686598120391032157 11830576007474295146637059)
        ·
          refine ⟨17745864011211442719955589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11830576007474295146637059 17745864011211442719955589)
          ·
            refine ⟨3327349502102145509991673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17745864011211442719955589 3327349502102145509991673)
            ·
              refine ⟨2495512126576609132493755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3327349502102145509991673 2495512126576609132493755)
              ·
                refine ⟨3743268189864913698740633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495512126576609132493755 3743268189864913698740633)
                ·
                  refine ⟨2807451142398685274055475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3743268189864913698740633 2807451142398685274055475)
                  ·
                    refine ⟨4211176713598027911083213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2807451142398685274055475 4211176713598027911083213)
                    ·
                      refine ⟨1579191267599260466656205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4211176713598027911083213 1579191267599260466656205)
                      ·
                        rfl

theorem cell23_3075464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_3075464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075464 prefixEnd_3075464 := by exact prefixLift 3075464
  have htrace : WordTrace (prefixWord ++ tailWord_3075464) baseStart_3075464 baseEnd_3075464 := by
    simpa [prefixWord, tailWord_3075464, baseEnd_3075464] using wordTrace_append hprefix tailTrace_3075464
  have hstable : (prefixWord ++ tailWord_3075464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075464).length < 2 ^ (prefixWord ++ tailWord_3075464).sum := by decide
  have hdescent : baseEnd_3075464 < baseStart_3075464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075474 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3075474 : Nat := 118140960795 + 3075474 * 2 ^ 59
def prefixEnd_3075474 : Nat := 4983230072969 + 3 ^ 40 * 3075474 * 2
def baseEnd_3075474 : Nat := 1579196402405805427531159

theorem tailTrace_3075474 : CollatzResearch.WordTrace tailWord_3075474 prefixEnd_3075474 1579196402405805427531159 := by
  unfold tailWord_3075474
  simp only [CollatzResearch.WordTrace]
  refine ⟨28042938015022605496772369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74781168040060281324726317 28042938015022605496772369)
  ·
    refine ⟨21032203511266954122579277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28042938015022605496772369 21032203511266954122579277)
    ·
      refine ⟨7887076316725107795967229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21032203511266954122579277 7887076316725107795967229)
      ·
        refine ⟨2957653618771915423487711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7887076316725107795967229 2957653618771915423487711)
        ·
          refine ⟨4436480428157873135231567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957653618771915423487711 4436480428157873135231567)
          ·
            refine ⟨6654720642236809702847351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436480428157873135231567 6654720642236809702847351)
            ·
              refine ⟨9982080963355214554271027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6654720642236809702847351 9982080963355214554271027)
              ·
                refine ⟨14973121445032821831406541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9982080963355214554271027 14973121445032821831406541)
                ·
                  refine ⟨5614920541887308186777453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14973121445032821831406541 5614920541887308186777453)
                  ·
                    refine ⟨2105595203207740570041545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5614920541887308186777453 2105595203207740570041545)
                    ·
                      refine ⟨1579196402405805427531159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105595203207740570041545 1579196402405805427531159)
                      ·
                        rfl

theorem cell23_3075474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3075474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075474 prefixEnd_3075474 := by exact prefixLift 3075474
  have htrace : WordTrace (prefixWord ++ tailWord_3075474) baseStart_3075474 baseEnd_3075474 := by
    simpa [prefixWord, tailWord_3075474, baseEnd_3075474] using wordTrace_append hprefix tailTrace_3075474
  have hstable : (prefixWord ++ tailWord_3075474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075474).length < 2 ^ (prefixWord ++ tailWord_3075474).sum := by decide
  have hdescent : baseEnd_3075474 < baseStart_3075474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075536 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 2, 8]
def baseStart_3075536 : Nat := 118140960795 + 3075536 * 2 ^ 59
def prefixEnd_3075536 : Nat := 4983230072969 + 3 ^ 40 * 3075536 * 2
def baseEnd_3075536 : Nat := 526409412735461394985291

theorem tailTrace_3075536 : CollatzResearch.WordTrace tailWord_3075536 prefixEnd_3075536 526409412735461394985291 := by
  unfold tailWord_3075536
  simp only [CollatzResearch.WordTrace]
  refine ⟨56087006692932903287923231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74782675590577204383897641 56087006692932903287923231)
  ·
    refine ⟨84130510039399354931884847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56087006692932903287923231 84130510039399354931884847)
    ·
      refine ⟨126195765059099032397827271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84130510039399354931884847 126195765059099032397827271)
      ·
        refine ⟨189293647588648548596740907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126195765059099032397827271 189293647588648548596740907)
        ·
          refine ⟨283940471382972822895111361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189293647588648548596740907 283940471382972822895111361)
          ·
            refine ⟨212955353537229617171333521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283940471382972822895111361 212955353537229617171333521)
            ·
              refine ⟨159716515152922212878500141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212955353537229617171333521 159716515152922212878500141)
              ·
                refine ⟨59893693182345829829437553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159716515152922212878500141 59893693182345829829437553)
                ·
                  refine ⟨44920269886759372372078165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59893693182345829829437553 44920269886759372372078165)
                  ·
                    refine ⟨526409412735461394985291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44920269886759372372078165 526409412735461394985291)
                    ·
                      rfl

theorem cell23_3075536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_3075536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075536 prefixEnd_3075536 := by exact prefixLift 3075536
  have htrace : WordTrace (prefixWord ++ tailWord_3075536) baseStart_3075536 baseEnd_3075536 := by
    simpa [prefixWord, tailWord_3075536, baseEnd_3075536] using wordTrace_append hprefix tailTrace_3075536
  have hstable : (prefixWord ++ tailWord_3075536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075536).length < 2 ^ (prefixWord ++ tailWord_3075536).sum := by decide
  have hdescent : baseEnd_3075536 < baseStart_3075536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075540 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_3075540 : Nat := 118140960795 + 3075540 * 2 ^ 59
def prefixEnd_3075540 : Nat := 4983230072969 + 3 ^ 40 * 3075540 * 2
def baseEnd_3075540 : Nat := 526410097376334056435285

theorem tailTrace_3075540 : CollatzResearch.WordTrace tailWord_3075540 prefixEnd_3075540 526410097376334056435285 := by
  unfold tailWord_3075540
  simp only [CollatzResearch.WordTrace]
  refine ⟨56087079638925657629496037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74782772851900876839328049 56087079638925657629496037)
  ·
    refine ⟨10516327432298560805530507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56087079638925657629496037 10516327432298560805530507)
    ·
      refine ⟨15774491148447841208295761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10516327432298560805530507 15774491148447841208295761)
      ·
        refine ⟨11830868361335880906221821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15774491148447841208295761 11830868361335880906221821)
        ·
          refine ⟨4436575635500955339833183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11830868361335880906221821 4436575635500955339833183)
          ·
            refine ⟨6654863453251433009749775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436575635500955339833183 6654863453251433009749775)
            ·
              refine ⟨9982295179877149514624663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6654863453251433009749775 9982295179877149514624663)
              ·
                refine ⟨14973442769815724271936995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9982295179877149514624663 14973442769815724271936995)
                ·
                  refine ⟨22460164154723586407905493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14973442769815724271936995 22460164154723586407905493)
                  ·
                    refine ⟨526410097376334056435285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22460164154723586407905493 526410097376334056435285)
                    ·
                      rfl

theorem cell23_3075540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_3075540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075540 prefixEnd_3075540 := by exact prefixLift 3075540
  have htrace : WordTrace (prefixWord ++ tailWord_3075540) baseStart_3075540 baseEnd_3075540 := by
    simpa [prefixWord, tailWord_3075540, baseEnd_3075540] using wordTrace_append hprefix tailTrace_3075540
  have hstable : (prefixWord ++ tailWord_3075540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075540).length < 2 ^ (prefixWord ++ tailWord_3075540).sum := by decide
  have hdescent : baseEnd_3075540 < baseStart_3075540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075560 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_3075560 : Nat := 118140960795 + 3075560 * 2 ^ 59
def prefixEnd_3075560 : Nat := 4983230072969 + 3 ^ 40 * 3075560 * 2
def baseEnd_3075560 : Nat := 1579240561742092091055763

theorem tailTrace_3075560 : CollatzResearch.WordTrace tailWord_3075560 prefixEnd_3075560 1579240561742092091055763 := by
  unfold tailWord_3075560
  simp only [CollatzResearch.WordTrace]
  refine ⟨56087444368889429337360067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74783259158519239116480089 56087444368889429337360067)
  ·
    refine ⟨84131166553334144006040101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56087444368889429337360067 84131166553334144006040101)
    ·
      refine ⟨15774593728750152001132519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84131166553334144006040101 15774593728750152001132519)
      ·
        refine ⟨23661890593125228001698779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15774593728750152001132519 23661890593125228001698779)
        ·
          refine ⟨35492835889687842002548169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23661890593125228001698779 35492835889687842002548169)
          ·
            refine ⟨26619626917265881501911127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35492835889687842002548169 26619626917265881501911127)
            ·
              refine ⟨39929440375898822252866691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26619626917265881501911127 39929440375898822252866691)
              ·
                refine ⟨59894160563848233379300037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39929440375898822252866691 59894160563848233379300037)
                ·
                  refine ⟨11230155105721543758618757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59894160563848233379300037 11230155105721543758618757)
                  ·
                    refine ⟨2105654082322789454741017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11230155105721543758618757 2105654082322789454741017)
                    ·
                      refine ⟨1579240561742092091055763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105654082322789454741017 1579240561742092091055763)
                      ·
                        rfl

theorem cell23_3075560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_3075560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075560 prefixEnd_3075560 := by exact prefixLift 3075560
  have htrace : WordTrace (prefixWord ++ tailWord_3075560) baseStart_3075560 baseEnd_3075560 := by
    simpa [prefixWord, tailWord_3075560, baseEnd_3075560] using wordTrace_append hprefix tailTrace_3075560
  have hstable : (prefixWord ++ tailWord_3075560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075560).length < 2 ^ (prefixWord ++ tailWord_3075560).sum := by decide
  have hdescent : baseEnd_3075560 < baseStart_3075560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075593 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 2, 5, 3]
def baseStart_3075593 : Nat := 118140960795 + 3075593 * 2 ^ 59
def prefixEnd_3075593 : Nat := 4983230072969 + 3 ^ 40 * 3075593 * 2
def baseEnd_3075593 : Nat := 1579257506603690461943111

theorem tailTrace_3075593 : CollatzResearch.WordTrace tailWord_3075593 prefixEnd_3075593 1579257506603690461943111 := by
  unfold tailWord_3075593
  simp only [CollatzResearch.WordTrace]
  refine ⟨112176092346659305310671433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74784061564439536873780955 112176092346659305310671433)
  ·
    refine ⟨84132069259994478983003575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112176092346659305310671433 84132069259994478983003575)
    ·
      refine ⟨126198103889991718474505363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84132069259994478983003575 126198103889991718474505363)
      ·
        refine ⟨189297155834987577711758045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126198103889991718474505363 189297155834987577711758045)
        ·
          refine ⟨70986433438120341641909267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189297155834987577711758045 70986433438120341641909267)
          ·
            refine ⟨106479650157180512462863901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70986433438120341641909267 106479650157180512462863901)
            ·
              refine ⟨39929868808942692173573963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106479650157180512462863901 39929868808942692173573963)
              ·
                refine ⟨59894803213414038260360945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39929868808942692173573963 59894803213414038260360945)
                ·
                  refine ⟨44921102410060528695270709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59894803213414038260360945 44921102410060528695270709)
                  ·
                    refine ⟨4211353350943174565181629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44921102410060528695270709 4211353350943174565181629)
                    ·
                      refine ⟨1579257506603690461943111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4211353350943174565181629 1579257506603690461943111)
                      ·
                        rfl

theorem cell23_3075593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5, 3].length) (baseStart_3075593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075593 prefixEnd_3075593 := by exact prefixLift 3075593
  have htrace : WordTrace (prefixWord ++ tailWord_3075593) baseStart_3075593 baseEnd_3075593 := by
    simpa [prefixWord, tailWord_3075593, baseEnd_3075593] using wordTrace_append hprefix tailTrace_3075593
  have hstable : (prefixWord ++ tailWord_3075593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075593).length < 2 ^ (prefixWord ++ tailWord_3075593).sum := by decide
  have hdescent : baseEnd_3075593 < baseStart_3075593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075633 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_3075633 : Nat := 118140960795 + 3075633 * 2 ^ 59
def prefixEnd_3075633 : Nat := 4983230072969 + 3 ^ 40 * 3075633 * 2
def baseEnd_3075633 : Nat := 1579278045829870305442927

theorem tailTrace_3075633 : CollatzResearch.WordTrace tailWord_3075633 prefixEnd_3075633 1579278045829870305442927 := by
  unfold tailWord_3075633
  simp only [CollatzResearch.WordTrace]
  refine ⟨112177551266514392142127553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74785034177676261428085035 112177551266514392142127553)
  ·
    refine ⟨84133163449885794106595665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112177551266514392142127553 84133163449885794106595665)
    ·
      refine ⟨63099872587414345579946749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84133163449885794106595665 63099872587414345579946749)
      ·
        refine ⟨23662452220280379592480031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63099872587414345579946749 23662452220280379592480031)
        ·
          refine ⟨35493678330420569388720047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23662452220280379592480031 35493678330420569388720047)
          ·
            refine ⟨53240517495630854083080071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35493678330420569388720047 53240517495630854083080071)
            ·
              refine ⟨79860776243446281124620107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53240517495630854083080071 79860776243446281124620107)
              ·
                refine ⟨119791164365169421686930161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79860776243446281124620107 119791164365169421686930161)
                ·
                  refine ⟨89843373273877066265197621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119791164365169421686930161 89843373273877066265197621)
                  ·
                    refine ⟨8422816244425974962362277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89843373273877066265197621 8422816244425974962362277)
                    ·
                      refine ⟨1579278045829870305442927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8422816244425974962362277 1579278045829870305442927)
                      ·
                        rfl

theorem cell23_3075633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_3075633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075633 prefixEnd_3075633 := by exact prefixLift 3075633
  have htrace : WordTrace (prefixWord ++ tailWord_3075633) baseStart_3075633 baseEnd_3075633 := by
    simpa [prefixWord, tailWord_3075633, baseEnd_3075633] using wordTrace_append hprefix tailTrace_3075633
  have hstable : (prefixWord ++ tailWord_3075633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075633).length < 2 ^ (prefixWord ++ tailWord_3075633).sum := by decide
  have hdescent : baseEnd_3075633 < baseStart_3075633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075647 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 1, 5]
def baseStart_3075647 : Nat := 118140960795 + 3075647 * 2 ^ 59
def prefixEnd_3075647 : Nat := 4983230072969 + 3 ^ 40 * 3075647 * 2
def baseEnd_3075647 : Nat := 526428411519677750222621

theorem tailTrace_3075647 : CollatzResearch.WordTrace tailWord_3075647 prefixEnd_3075647 526428411519677750222621 := by
  unfold tailWord_3075647
  simp only [CollatzResearch.WordTrace]
  refine ⟨112178061888463672533137195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74785374592309115022091463 112178061888463672533137195)
  ·
    refine ⟨168267092832695508799705793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112178061888463672533137195 168267092832695508799705793)
    ·
      refine ⟨126200319624521631599779345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168267092832695508799705793 126200319624521631599779345)
      ·
        refine ⟨94650239718391223699834509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126200319624521631599779345 94650239718391223699834509)
        ·
          refine ⟨35493839894396708887437941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94650239718391223699834509 35493839894396708887437941)
          ·
            refine ⟨3327547490099691458197307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35493839894396708887437941 3327547490099691458197307)
            ·
              refine ⟨4991321235149537187295961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327547490099691458197307 4991321235149537187295961)
              ·
                refine ⟨3743490926362152890471971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4991321235149537187295961 3743490926362152890471971)
                ·
                  refine ⟨5615236389543229335707957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743490926362152890471971 5615236389543229335707957)
                  ·
                    refine ⟨526428411519677750222621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5615236389543229335707957 526428411519677750222621)
                    ·
                      rfl

theorem cell23_3075647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 5].length) (baseStart_3075647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075647 prefixEnd_3075647 := by exact prefixLift 3075647
  have htrace : WordTrace (prefixWord ++ tailWord_3075647) baseStart_3075647 baseEnd_3075647 := by
    simpa [prefixWord, tailWord_3075647, baseEnd_3075647] using wordTrace_append hprefix tailTrace_3075647
  have hstable : (prefixWord ++ tailWord_3075647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075647).length < 2 ^ (prefixWord ++ tailWord_3075647).sum := by decide
  have hdescent : baseEnd_3075647 < baseStart_3075647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075660 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_3075660 : Nat := 118140960795 + 3075660 * 2 ^ 59
def prefixEnd_3075660 : Nat := 4983230072969 + 3 ^ 40 * 3075660 * 2
def baseEnd_3075660 : Nat := 526430636602513899935101

theorem tailTrace_3075660 : CollatzResearch.WordTrace tailWord_3075660 prefixEnd_3075660 526430636602513899935101 := by
  unfold tailWord_3075660
  simp only [CollatzResearch.WordTrace]
  refine ⟨56089268018708287876680217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74785690691611050502240289 56089268018708287876680217)
  ·
    refine ⟨42066951014031215907510163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56089268018708287876680217 42066951014031215907510163)
    ·
      refine ⟨63100426521046823861265245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42066951014031215907510163 63100426521046823861265245)
      ·
        refine ⟨23662659945392558947974467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63100426521046823861265245 23662659945392558947974467)
        ·
          refine ⟨35493989918088838421961701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23662659945392558947974467 35493989918088838421961701)
          ·
            refine ⟨6655123109641657204117819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35493989918088838421961701 6655123109641657204117819)
            ·
              refine ⟨9982684664462485806176729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6655123109641657204117819 9982684664462485806176729)
              ·
                refine ⟨7487013498346864354632547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9982684664462485806176729 7487013498346864354632547)
                ·
                  refine ⟨11230520247520296531948821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487013498346864354632547 11230520247520296531948821)
                  ·
                    refine ⟨526430636602513899935101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11230520247520296531948821 526430636602513899935101)
                    ·
                      rfl

theorem cell23_3075660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_3075660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075660 prefixEnd_3075660 := by exact prefixLift 3075660
  have htrace : WordTrace (prefixWord ++ tailWord_3075660) baseStart_3075660 baseEnd_3075660 := by
    simpa [prefixWord, tailWord_3075660, baseEnd_3075660] using wordTrace_append hprefix tailTrace_3075660
  have hstable : (prefixWord ++ tailWord_3075660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075660).length < 2 ^ (prefixWord ++ tailWord_3075660).sum := by decide
  have hdescent : baseEnd_3075660 < baseStart_3075660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075690 : List Nat := [3, 1, 3, 2, 1, 2, 3, 8]
def baseStart_3075690 : Nat := 118140960795 + 3075690 * 2 ^ 59
def prefixEnd_3075690 : Nat := 4983230072969 + 3 ^ 40 * 3075690 * 2
def baseEnd_3075690 : Nat := 58492863489895428978895

theorem tailTrace_3075690 : CollatzResearch.WordTrace tailWord_3075690 prefixEnd_3075690 58492863489895428978895 := by
  unfold tailWord_3075690
  simp only [CollatzResearch.WordTrace]
  refine ⟨28044907556826972719238131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74786420151538593917968349 28044907556826972719238131)
  ·
    refine ⟨42067361335240459078857197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28044907556826972719238131 42067361335240459078857197)
    ·
      refine ⟨15775260500715172154571449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42067361335240459078857197 15775260500715172154571449)
      ·
        refine ⟨11831445375536379115928587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15775260500715172154571449 11831445375536379115928587)
        ·
          refine ⟨17747168063304568673892881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11831445375536379115928587 17747168063304568673892881)
          ·
            refine ⟨13310376047478426505419661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17747168063304568673892881 13310376047478426505419661)
            ·
              refine ⟨4991391017804409939532373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13310376047478426505419661 4991391017804409939532373)
              ·
                refine ⟨58492863489895428978895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4991391017804409939532373 58492863489895428978895)
                ·
                  rfl

theorem cell23_3075690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 8].length) (baseStart_3075690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075690 prefixEnd_3075690 := by exact prefixLift 3075690
  have htrace : WordTrace (prefixWord ++ tailWord_3075690) baseStart_3075690 baseEnd_3075690 := by
    simpa [prefixWord, tailWord_3075690, baseEnd_3075690] using wordTrace_append hprefix tailTrace_3075690
  have hstable : (prefixWord ++ tailWord_3075690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075690).length < 2 ^ (prefixWord ++ tailWord_3075690).sum := by decide
  have hdescent : baseEnd_3075690 < baseStart_3075690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075701 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_3075701 : Nat := 118140960795 + 3075701 * 2 ^ 59
def prefixEnd_3075701 : Nat := 4983230072969 + 3 ^ 40 * 3075701 * 2
def baseEnd_3075701 : Nat := 1579312962514376039392615

theorem tailTrace_3075701 : CollatzResearch.WordTrace tailWord_3075701 prefixEnd_3075701 1579312962514376039392615 := by
  unfold tailWord_3075701
  simp only [CollatzResearch.WordTrace]
  refine ⟨112180031430268039755602957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74786687620178693170401971 112180031430268039755602957)
  ·
    refine ⟨42067511786350514908351109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112180031430268039755602957 42067511786350514908351109)
    ·
      refine ⟨7887658459940721545315833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42067511786350514908351109 7887658459940721545315833)
      ·
        refine ⟨5915743844955541158986875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7887658459940721545315833 5915743844955541158986875)
        ·
          refine ⟨8873615767433311738480313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915743844955541158986875 8873615767433311738480313)
          ·
            refine ⟨6655211825574983803860235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8873615767433311738480313 6655211825574983803860235)
            ·
              refine ⟨9982817738362475705790353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6655211825574983803860235 9982817738362475705790353)
              ·
                refine ⟨7487113303771856779342765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9982817738362475705790353 7487113303771856779342765)
                ·
                  refine ⟨2807667488914446292253537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7487113303771856779342765 2807667488914446292253537)
                  ·
                    refine ⟨2105750616685834719190153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2807667488914446292253537 2105750616685834719190153)
                    ·
                      refine ⟨1579312962514376039392615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2105750616685834719190153 1579312962514376039392615)
                      ·
                        rfl

theorem cell23_3075701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_3075701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075701 prefixEnd_3075701 := by exact prefixLift 3075701
  have htrace : WordTrace (prefixWord ++ tailWord_3075701) baseStart_3075701 baseEnd_3075701 := by
    simpa [prefixWord, tailWord_3075701, baseEnd_3075701] using wordTrace_append hprefix tailTrace_3075701
  have hstable : (prefixWord ++ tailWord_3075701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075701).length < 2 ^ (prefixWord ++ tailWord_3075701).sum := by decide
  have hdescent : baseEnd_3075701 < baseStart_3075701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075703 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 4, 7]
def baseStart_3075703 : Nat := 118140960795 + 3075703 * 2 ^ 59
def prefixEnd_3075703 : Nat := 4983230072969 + 3 ^ 40 * 3075703 * 2
def baseEnd_3075703 : Nat := 526437996491895010522535

theorem tailTrace_3075703 : CollatzResearch.WordTrace tailWord_3075703 prefixEnd_3075703 526437996491895010522535 := by
  unfold tailWord_3075703
  simp only [CollatzResearch.WordTrace]
  refine ⟨112180104376260794097175763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74786736250840529398117175 112180104376260794097175763)
  ·
    refine ⟨168270156564391191145763645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112180104376260794097175763 168270156564391191145763645)
    ·
      refine ⟨63101308711646696679661367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168270156564391191145763645 63101308711646696679661367)
      ·
        refine ⟨94651963067470045019492051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63101308711646696679661367 94651963067470045019492051)
        ·
          refine ⟨141977944601205067529238077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94651963067470045019492051 141977944601205067529238077)
          ·
            refine ⟨53241729225451900323464279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141977944601205067529238077 53241729225451900323464279)
            ·
              refine ⟨79862593838177850485196419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53241729225451900323464279 79862593838177850485196419)
              ·
                refine ⟨119793890757266775727794629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79862593838177850485196419 119793890757266775727794629)
                ·
                  refine ⟨22461354516987520448961493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119793890757266775727794629 22461354516987520448961493)
                  ·
                    refine ⟨526437996491895010522535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22461354516987520448961493 526437996491895010522535)
                    ·
                      rfl

theorem cell23_3075703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_3075703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075703 prefixEnd_3075703 := by exact prefixLift 3075703
  have htrace : WordTrace (prefixWord ++ tailWord_3075703) baseStart_3075703 baseEnd_3075703 := by
    simpa [prefixWord, tailWord_3075703, baseEnd_3075703] using wordTrace_append hprefix tailTrace_3075703
  have hstable : (prefixWord ++ tailWord_3075703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075703).length < 2 ^ (prefixWord ++ tailWord_3075703).sum := by decide
  have hdescent : baseEnd_3075703 < baseStart_3075703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075717 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 4, 1, 3]
def baseStart_3075717 : Nat := 118140960795 + 3075717 * 2 ^ 59
def prefixEnd_3075717 : Nat := 4983230072969 + 3 ^ 40 * 3075717 * 2
def baseEnd_3075717 : Nat := 1579321178204847976792541

theorem tailTrace_3075717 : CollatzResearch.WordTrace tailWord_3075717 prefixEnd_3075717 1579321178204847976792541 := by
  unfold tailWord_3075717
  simp only [CollatzResearch.WordTrace]
  refine ⟨112180614998210074488185405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74787076665473382992123603 112180614998210074488185405)
  ·
    refine ⟨42067730624328777933069527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112180614998210074488185405 42067730624328777933069527)
    ·
      refine ⟨63101595936493166899604291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42067730624328777933069527 63101595936493166899604291)
      ·
        refine ⟨94652393904739750349406437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63101595936493166899604291 94652393904739750349406437)
        ·
          refine ⟨17747323857138703190513707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94652393904739750349406437 17747323857138703190513707)
          ·
            refine ⟨26620985785708054785770561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17747323857138703190513707 26620985785708054785770561)
            ·
              refine ⟨19965739339281041089327921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26620985785708054785770561 19965739339281041089327921)
              ·
                refine ⟨14974304504460780816995941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19965739339281041089327921 14974304504460780816995941)
                ·
                  refine ⟨2807682094586396403186739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14974304504460780816995941 2807682094586396403186739)
                  ·
                    refine ⟨4211523141879594604780109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2807682094586396403186739 4211523141879594604780109)
                    ·
                      refine ⟨1579321178204847976792541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4211523141879594604780109 1579321178204847976792541)
                      ·
                        rfl

theorem cell23_3075717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_3075717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075717 prefixEnd_3075717 := by exact prefixLift 3075717
  have htrace : WordTrace (prefixWord ++ tailWord_3075717) baseStart_3075717 baseEnd_3075717 := by
    simpa [prefixWord, tailWord_3075717, baseEnd_3075717] using wordTrace_append hprefix tailTrace_3075717
  have hstable : (prefixWord ++ tailWord_3075717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075717).length < 2 ^ (prefixWord ++ tailWord_3075717).sum := by decide
  have hdescent : baseEnd_3075717 < baseStart_3075717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075760 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 3]
def baseStart_3075760 : Nat := 118140960795 + 3075760 * 2 ^ 59
def prefixEnd_3075760 : Nat := 4983230072969 + 3 ^ 40 * 3075760 * 2
def baseEnd_3075760 : Nat := 1579343257872991308554843

theorem tailTrace_3075760 : CollatzResearch.WordTrace tailWord_3075760 prefixEnd_3075760 1579343257872991308554843 := by
  unfold tailWord_3075760
  simp only [CollatzResearch.WordTrace]
  refine ⟨56091091668527146416000367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74788122224702861888000489 56091091668527146416000367)
  ·
    refine ⟨84136637502790719624000551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56091091668527146416000367 84136637502790719624000551)
    ·
      refine ⟨126204956254186079436000827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84136637502790719624000551 126204956254186079436000827)
      ·
        refine ⟨189307434381279119154001241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126204956254186079436000827 189307434381279119154001241)
        ·
          refine ⟨141980575785959339365500931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189307434381279119154001241 141980575785959339365500931)
          ·
            refine ⟨212970863678939009048251397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141980575785959339365500931 212970863678939009048251397)
            ·
              refine ⟨39932036939801064196547137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212970863678939009048251397 39932036939801064196547137)
              ·
                refine ⟨29949027704850798147410353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39932036939801064196547137 29949027704850798147410353)
                ·
                  refine ⟨22461770778638098610557765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29949027704850798147410353 22461770778638098610557765)
                  ·
                    refine ⟨4211582020994643489479581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22461770778638098610557765 4211582020994643489479581)
                    ·
                      refine ⟨1579343257872991308554843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4211582020994643489479581 1579343257872991308554843)
                      ·
                        rfl

theorem cell23_3075760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 3].length) (baseStart_3075760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075760 prefixEnd_3075760 := by exact prefixLift 3075760
  have htrace : WordTrace (prefixWord ++ tailWord_3075760) baseStart_3075760 baseEnd_3075760 := by
    simpa [prefixWord, tailWord_3075760, baseEnd_3075760] using wordTrace_append hprefix tailTrace_3075760
  have hstable : (prefixWord ++ tailWord_3075760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075760).length < 2 ^ (prefixWord ++ tailWord_3075760).sum := by decide
  have hdescent : baseEnd_3075760 < baseStart_3075760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075790 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_3075790 : Nat := 118140960795 + 3075790 * 2 ^ 59
def prefixEnd_3075790 : Nat := 4983230072969 + 3 ^ 40 * 3075790 * 2
def baseEnd_3075790 : Nat := 1579358662292626191179705

theorem tailTrace_3075790 : CollatzResearch.WordTrace tailWord_3075790 prefixEnd_3075790 1579358662292626191179705 := by
  unfold tailWord_3075790
  simp only [CollatzResearch.WordTrace]
  refine ⟨14022909690868200994449103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74788851684630405303728549 14022909690868200994449103)
  ·
    refine ⟨21034364536302301491673655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14022909690868200994449103 21034364536302301491673655)
    ·
      refine ⟨31551546804453452237510483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21034364536302301491673655 31551546804453452237510483)
      ·
        refine ⟨47327320206680178356265725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31551546804453452237510483 47327320206680178356265725)
        ·
          refine ⟨17747745077505066883599647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47327320206680178356265725 17747745077505066883599647)
          ·
            refine ⟨26621617616257600325399471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17747745077505066883599647 26621617616257600325399471)
            ·
              refine ⟨39932426424386400488099207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26621617616257600325399471 39932426424386400488099207)
              ·
                refine ⟨59898639636579600732148811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39932426424386400488099207 59898639636579600732148811)
                ·
                  refine ⟨89847959454869401098223217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59898639636579600732148811 89847959454869401098223217)
                  ·
                    refine ⟨67385969591152050823667413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89847959454869401098223217 67385969591152050823667413)
                    ·
                      refine ⟨1579358662292626191179705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67385969591152050823667413 1579358662292626191179705)
                      ·
                        rfl

theorem cell23_3075790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_3075790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075790 prefixEnd_3075790 := by exact prefixLift 3075790
  have htrace : WordTrace (prefixWord ++ tailWord_3075790) baseStart_3075790 baseEnd_3075790 := by
    simpa [prefixWord, tailWord_3075790, baseEnd_3075790] using wordTrace_append hprefix tailTrace_3075790
  have hstable : (prefixWord ++ tailWord_3075790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075790).length < 2 ^ (prefixWord ++ tailWord_3075790).sum := by decide
  have hdescent : baseEnd_3075790 < baseStart_3075790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075857 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 3, 4]
def baseStart_3075857 : Nat := 118140960795 + 3075857 * 2 ^ 59
def prefixEnd_3075857 : Nat := 4983230072969 + 3 ^ 40 * 3075857 * 2
def baseEnd_3075857 : Nat := 526464355165492476347299

theorem tailTrace_3075857 : CollatzResearch.WordTrace tailWord_3075857 prefixEnd_3075857 526464355165492476347299 := by
  unfold tailWord_3075857
  simp only [CollatzResearch.WordTrace]
  refine ⟨112185721217702878398281825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74790480811801918932187883 112185721217702878398281825)
  ·
    refine ⟨84139290913277158798711369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112185721217702878398281825 84139290913277158798711369)
    ·
      refine ⟨63104468184957869099033527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84139290913277158798711369 63104468184957869099033527)
      ·
        refine ⟨94656702277436803648550291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63104468184957869099033527 94656702277436803648550291)
        ·
          refine ⟨141985053416155205472825437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94656702277436803648550291 141985053416155205472825437)
          ·
            refine ⟨53244395031058202052309539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141985053416155205472825437 53244395031058202052309539)
            ·
              refine ⟨79866592546587303078464309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53244395031058202052309539 79866592546587303078464309)
              ·
                refine ⟨7487493051242559663606029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79866592546587303078464309 7487493051242559663606029)
                ·
                  refine ⟨2807809894215959873852261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7487493051242559663606029 2807809894215959873852261)
                  ·
                    refine ⟨526464355165492476347299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2807809894215959873852261 526464355165492476347299)
                    ·
                      rfl

theorem cell23_3075857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_3075857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075857 prefixEnd_3075857 := by exact prefixLift 3075857
  have htrace : WordTrace (prefixWord ++ tailWord_3075857) baseStart_3075857 baseEnd_3075857 := by
    simpa [prefixWord, tailWord_3075857, baseEnd_3075857] using wordTrace_append hprefix tailTrace_3075857
  have hstable : (prefixWord ++ tailWord_3075857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075857).length < 2 ^ (prefixWord ++ tailWord_3075857).sum := by decide
  have hdescent : baseEnd_3075857 < baseStart_3075857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075874 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3075874 : Nat := 118140960795 + 3075874 * 2 ^ 59
def prefixEnd_3075874 : Nat := 4983230072969 + 3 ^ 40 * 3075874 * 2
def baseEnd_3075874 : Nat := 526467264889201287509773

theorem tailTrace_3075874 : CollatzResearch.WordTrace tailWord_3075874 prefixEnd_3075874 526467264889201287509773 := by
  unfold tailWord_3075874
  simp only [CollatzResearch.WordTrace]
  refine ⟨28046585314660322575412669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74790894172427526867767117 28046585314660322575412669)
  ·
    refine ⟨10517469492997620965779751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28046585314660322575412669 10517469492997620965779751)
    ·
      refine ⟨15776204239496431448669627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10517469492997620965779751 15776204239496431448669627)
      ·
        refine ⟨23664306359244647173004441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15776204239496431448669627 23664306359244647173004441)
        ·
          refine ⟨17748229769433485379753331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23664306359244647173004441 17748229769433485379753331)
          ·
            refine ⟨26622344654150228069629997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17748229769433485379753331 26622344654150228069629997)
            ·
              refine ⟨9983379245306335526111249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26622344654150228069629997 9983379245306335526111249)
              ·
                refine ⟨7487534433979751644583437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9983379245306335526111249 7487534433979751644583437)
                ·
                  refine ⟨2807825412742406866718789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7487534433979751644583437 2807825412742406866718789)
                  ·
                    refine ⟨526467264889201287509773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2807825412742406866718789 526467264889201287509773)
                    ·
                      rfl

theorem cell23_3075874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3075874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075874 prefixEnd_3075874 := by exact prefixLift 3075874
  have htrace : WordTrace (prefixWord ++ tailWord_3075874) baseStart_3075874 baseEnd_3075874 := by
    simpa [prefixWord, tailWord_3075874, baseEnd_3075874] using wordTrace_append hprefix tailTrace_3075874
  have hstable : (prefixWord ++ tailWord_3075874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075874).length < 2 ^ (prefixWord ++ tailWord_3075874).sum := by decide
  have hdescent : baseEnd_3075874 < baseStart_3075874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075884 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 3]
def baseStart_3075884 : Nat := 118140960795 + 3075884 * 2 ^ 59
def prefixEnd_3075884 : Nat := 4983230072969 + 3 ^ 40 * 3075884 * 2
def baseEnd_3075884 : Nat := 1579406929474148823404273

theorem tailTrace_3075884 : CollatzResearch.WordTrace tailWord_3075884 prefixEnd_3075884 1579406929474148823404273 := by
  unfold tailWord_3075884
  simp only [CollatzResearch.WordTrace]
  refine ⟨56093352994302531004757353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74791137325736708006343137 56093352994302531004757353)
  ·
    refine ⟨42070014745726898253568015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56093352994302531004757353 42070014745726898253568015)
    ·
      refine ⟨63105022118590347380352023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42070014745726898253568015 63105022118590347380352023)
      ·
        refine ⟨94657533177885521070528035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63105022118590347380352023 94657533177885521070528035)
        ·
          refine ⟨141986299766828281605792053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94657533177885521070528035 141986299766828281605792053)
          ·
            refine ⟨13311215603140151400543005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141986299766828281605792053 13311215603140151400543005)
            ·
              refine ⟨4991705851177556775203627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13311215603140151400543005 4991705851177556775203627)
              ·
                refine ⟨7487558776766335162805441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991705851177556775203627 7487558776766335162805441)
                ·
                  refine ⟨5615669082574751372104081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7487558776766335162805441 5615669082574751372104081)
                  ·
                    refine ⟨4211751811931063529078061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5615669082574751372104081 4211751811931063529078061)
                    ·
                      refine ⟨1579406929474148823404273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4211751811931063529078061 1579406929474148823404273)
                      ·
                        rfl

theorem cell23_3075884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_3075884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075884 prefixEnd_3075884 := by exact prefixLift 3075884
  have htrace : WordTrace (prefixWord ++ tailWord_3075884) baseStart_3075884 baseEnd_3075884 := by
    simpa [prefixWord, tailWord_3075884, baseEnd_3075884] using wordTrace_append hprefix tailTrace_3075884
  have hstable : (prefixWord ++ tailWord_3075884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075884).length < 2 ^ (prefixWord ++ tailWord_3075884).sum := by decide
  have hdescent : baseEnd_3075884 < baseStart_3075884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075894 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3075894 : Nat := 118140960795 + 3075894 * 2 ^ 59
def prefixEnd_3075894 : Nat := 4983230072969 + 3 ^ 40 * 3075894 * 2
def baseEnd_3075894 : Nat := 1579412064280693784279227

theorem tailTrace_3075894 : CollatzResearch.WordTrace tailWord_3075894 prefixEnd_3075894 1579412064280693784279227 := by
  unfold tailWord_3075894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011691919910552107336171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74791380479045889144919157 7011691919910552107336171)
  ·
    refine ⟨10517537879865828161004257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7011691919910552107336171 10517537879865828161004257)
    ·
      refine ⟨7888153409899371120753193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10517537879865828161004257 7888153409899371120753193)
      ·
        refine ⟨5916115057424528340564895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7888153409899371120753193 5916115057424528340564895)
        ·
          refine ⟨8874172586136792510847343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5916115057424528340564895 8874172586136792510847343)
          ·
            refine ⟨13311258879205188766271015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8874172586136792510847343 13311258879205188766271015)
            ·
              refine ⟨19966888318807783149406523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13311258879205188766271015 19966888318807783149406523)
              ·
                refine ⟨29950332478211674724109785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19966888318807783149406523 29950332478211674724109785)
                ·
                  refine ⟨22462749358658756043082339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29950332478211674724109785 22462749358658756043082339)
                  ·
                    refine ⟨33694124037988134064623509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22462749358658756043082339 33694124037988134064623509)
                    ·
                      refine ⟨1579412064280693784279227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33694124037988134064623509 1579412064280693784279227)
                      ·
                        rfl

theorem cell23_3075894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3075894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075894 prefixEnd_3075894 := by exact prefixLift 3075894
  have htrace : WordTrace (prefixWord ++ tailWord_3075894) baseStart_3075894 baseEnd_3075894 := by
    simpa [prefixWord, tailWord_3075894, baseEnd_3075894] using wordTrace_append hprefix tailTrace_3075894
  have hstable : (prefixWord ++ tailWord_3075894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075894).length < 2 ^ (prefixWord ++ tailWord_3075894).sum := by decide
  have hdescent : baseEnd_3075894 < baseStart_3075894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075948 : List Nat := [2, 2, 1, 1, 4, 2, 3, 3, 1, 1, 3]
def baseStart_3075948 : Nat := 118140960795 + 3075948 * 2 ^ 59
def prefixEnd_3075948 : Nat := 4983230072969 + 3 ^ 40 * 3075948 * 2
def baseEnd_3075948 : Nat := 1579439792236036573003979

theorem tailTrace_3075948 : CollatzResearch.WordTrace tailWord_3075948 prefixEnd_3075948 1579439792236036573003979 := by
  unfold tailWord_3075948
  simp only [CollatzResearch.WordTrace]
  refine ⟨56094520130186600469922249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74792693506915467293229665 56094520130186600469922249)
  ·
    refine ⟨42070890097639950352441687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56094520130186600469922249 42070890097639950352441687)
    ·
      refine ⟨63106335146459925528662531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42070890097639950352441687 63106335146459925528662531)
      ·
        refine ⟨94659502719689888292993797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63106335146459925528662531 94659502719689888292993797)
        ·
          refine ⟨17748656759941854054936337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94659502719689888292993797 17748656759941854054936337)
          ·
            refine ⟨13311492569956390541202253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17748656759941854054936337 13311492569956390541202253)
            ·
              refine ⟨4991809713733646452950845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13311492569956390541202253 4991809713733646452950845)
              ·
                refine ⟨1871928642650117419856567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4991809713733646452950845 1871928642650117419856567)
                ·
                  refine ⟨2807892963975176129784851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871928642650117419856567 2807892963975176129784851)
                  ·
                    refine ⟨4211839445962764194677277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2807892963975176129784851 4211839445962764194677277)
                    ·
                      refine ⟨1579439792236036573003979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4211839445962764194677277 1579439792236036573003979)
                      ·
                        rfl

theorem cell23_3075948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 1, 1, 3].length) (baseStart_3075948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075948 prefixEnd_3075948 := by exact prefixLift 3075948
  have htrace : WordTrace (prefixWord ++ tailWord_3075948) baseStart_3075948 baseEnd_3075948 := by
    simpa [prefixWord, tailWord_3075948, baseEnd_3075948] using wordTrace_append hprefix tailTrace_3075948
  have hstable : (prefixWord ++ tailWord_3075948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075948).length < 2 ^ (prefixWord ++ tailWord_3075948).sum := by decide
  have hdescent : baseEnd_3075948 < baseStart_3075948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075977 : List Nat := [1, 2, 1, 1, 5, 1, 4, 8]
def baseStart_3075977 : Nat := 118140960795 + 3075977 * 2 ^ 59
def prefixEnd_3075977 : Nat := 4983230072969 + 3 ^ 40 * 3075977 * 2
def baseEnd_3075977 : Nat := 58498321599074702205235

theorem tailTrace_3075977 : CollatzResearch.WordTrace tailWord_3075977 prefixEnd_3075977 58498321599074702205235 := by
  unfold tailWord_3075977
  simp only [CollatzResearch.WordTrace]
  refine ⟨112190097977268138892650185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74793398651512092595100123 112190097977268138892650185)
  ·
    refine ⟨84142573482951104169487639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112190097977268138892650185 84142573482951104169487639)
    ·
      refine ⟨126213860224426656254231459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84142573482951104169487639 126213860224426656254231459)
      ·
        refine ⟨189320790336639984381347189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126213860224426656254231459 189320790336639984381347189)
        ·
          refine ⟨17748824094059998535751299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189320790336639984381347189 17748824094059998535751299)
          ·
            refine ⟨26623236141089997803626949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17748824094059998535751299 26623236141089997803626949)
            ·
              refine ⟨4991856776454374588180053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26623236141089997803626949 4991856776454374588180053)
              ·
                refine ⟨58498321599074702205235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4991856776454374588180053 58498321599074702205235)
                ·
                  rfl

theorem cell23_3075977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 8].length) (baseStart_3075977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075977 prefixEnd_3075977 := by exact prefixLift 3075977
  have htrace : WordTrace (prefixWord ++ tailWord_3075977) baseStart_3075977 baseEnd_3075977 := by
    simpa [prefixWord, tailWord_3075977, baseEnd_3075977] using wordTrace_append hprefix tailTrace_3075977
  have hstable : (prefixWord ++ tailWord_3075977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075977).length < 2 ^ (prefixWord ++ tailWord_3075977).sum := by decide
  have hdescent : baseEnd_3075977 < baseStart_3075977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075988 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_3075988 : Nat := 118140960795 + 3075988 * 2 ^ 59
def prefixEnd_3075988 : Nat := 4983230072969 + 3 ^ 40 * 3075988 * 2
def baseEnd_3075988 : Nat := 1579460331462216416503795

theorem tailTrace_3075988 : CollatzResearch.WordTrace tailWord_3075988 prefixEnd_3075988 1579460331462216416503795 := by
  unfold tailWord_3075988
  simp only [CollatzResearch.WordTrace]
  refine ⟨56095249590114143885650309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74793666120152191847533745 56095249590114143885650309)
  ·
    refine ⟨10517859298146401978559433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56095249590114143885650309 10517859298146401978559433)
    ·
      refine ⟨7888394473609801483919575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10517859298146401978559433 7888394473609801483919575)
      ·
        refine ⟨11832591710414702225879363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7888394473609801483919575 11832591710414702225879363)
        ·
          refine ⟨17748887565622053338819045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11832591710414702225879363 17748887565622053338819045)
          ·
            refine ⟨3327916418554135001028571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17748887565622053338819045 3327916418554135001028571)
            ·
              refine ⟨4991874627831202501542857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327916418554135001028571 4991874627831202501542857)
              ·
                refine ⟨3743905970873401876157143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4991874627831202501542857 3743905970873401876157143)
                ·
                  refine ⟨5615858956310102814235715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743905970873401876157143 5615858956310102814235715)
                  ·
                    refine ⟨8423788434465154221353573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5615858956310102814235715 8423788434465154221353573)
                    ·
                      refine ⟨1579460331462216416503795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8423788434465154221353573 1579460331462216416503795)
                      ·
                        rfl

theorem cell23_3075988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_3075988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075988 prefixEnd_3075988 := by exact prefixLift 3075988
  have htrace : WordTrace (prefixWord ++ tailWord_3075988) baseStart_3075988 baseEnd_3075988 := by
    simpa [prefixWord, tailWord_3075988, baseEnd_3075988] using wordTrace_append hprefix tailTrace_3075988
  have hstable : (prefixWord ++ tailWord_3075988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075988).length < 2 ^ (prefixWord ++ tailWord_3075988).sum := by decide
  have hdescent : baseEnd_3075988 < baseStart_3075988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075991 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 1, 2, 3]
def baseStart_3075991 : Nat := 118140960795 + 3075991 * 2 ^ 59
def prefixEnd_3075991 : Nat := 4983230072969 + 3 ^ 40 * 3075991 * 2
def baseEnd_3075991 : Nat := 1579461871904179904766281

theorem tailTrace_3075991 : CollatzResearch.WordTrace tailWord_3075991 prefixEnd_3075991 1579461871904179904766281 := by
  unfold tailWord_3075991
  simp only [CollatzResearch.WordTrace]
  refine ⟨112190608599217419283659827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74793739066144946189106551 112190608599217419283659827)
  ·
    refine ⟨168285912898826128925489741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112190608599217419283659827 168285912898826128925489741)
    ·
      refine ⟨63107217337059798347058653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168285912898826128925489741 63107217337059798347058653)
      ·
        refine ⟨23665206501397424380146995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63107217337059798347058653 23665206501397424380146995)
        ·
          refine ⟨35497809752096136570220493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23665206501397424380146995 35497809752096136570220493)
          ·
            refine ⟨13311678657036051213832685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35497809752096136570220493 13311678657036051213832685)
            ·
              refine ⟨4991879496388519205187257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13311678657036051213832685 4991879496388519205187257)
              ·
                refine ⟨3743909622291389403890443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4991879496388519205187257 3743909622291389403890443)
                ·
                  refine ⟨5615864433437084105835665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743909622291389403890443 5615864433437084105835665)
                  ·
                    refine ⟨4211898325077813079376749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5615864433437084105835665 4211898325077813079376749)
                    ·
                      refine ⟨1579461871904179904766281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4211898325077813079376749 1579461871904179904766281)
                      ·
                        rfl

theorem cell23_3075991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_3075991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075991 prefixEnd_3075991 := by exact prefixLift 3075991
  have htrace : WordTrace (prefixWord ++ tailWord_3075991) baseStart_3075991 baseEnd_3075991 := by
    simpa [prefixWord, tailWord_3075991, baseEnd_3075991] using wordTrace_append hprefix tailTrace_3075991
  have hstable : (prefixWord ++ tailWord_3075991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075991).length < 2 ^ (prefixWord ++ tailWord_3075991).sum := by decide
  have hdescent : baseEnd_3075991 < baseStart_3075991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3075998 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_3075998 : Nat := 118140960795 + 3075998 * 2 ^ 59
def prefixEnd_3075998 : Nat := 4983230072969 + 3 ^ 40 * 3075998 * 2
def baseEnd_3075998 : Nat := 526488488756253792459583

theorem tailTrace_3075998 : CollatzResearch.WordTrace tailWord_3075998 prefixEnd_3075998 526488488756253792459583 := by
  unfold tailWord_3075998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14023857988774007434895581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74793909273461372986109765 14023857988774007434895581)
  ·
    refine ⟨5258946745790252788085843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14023857988774007434895581 5258946745790252788085843)
    ·
      refine ⟨7888420118685379182128765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5258946745790252788085843 7888420118685379182128765)
      ·
        refine ⟨2958157544507017193298287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7888420118685379182128765 2958157544507017193298287)
        ·
          refine ⟨4437236316760525789947431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958157544507017193298287 4437236316760525789947431)
          ·
            refine ⟨6655854475140788684921147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437236316760525789947431 6655854475140788684921147)
            ·
              refine ⟨9983781712711183027381721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6655854475140788684921147 9983781712711183027381721)
              ·
                refine ⟨7487836284533387270536291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9983781712711183027381721 7487836284533387270536291)
                ·
                  refine ⟨11231754426800080905804437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487836284533387270536291 11231754426800080905804437)
                  ·
                    refine ⟨526488488756253792459583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11231754426800080905804437 526488488756253792459583)
                    ·
                      rfl

theorem cell23_3075998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_3075998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3075998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3075998 prefixEnd_3075998 := by exact prefixLift 3075998
  have htrace : WordTrace (prefixWord ++ tailWord_3075998) baseStart_3075998 baseEnd_3075998 := by
    simpa [prefixWord, tailWord_3075998, baseEnd_3075998] using wordTrace_append hprefix tailTrace_3075998
  have hstable : (prefixWord ++ tailWord_3075998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3075998).length < 2 ^ (prefixWord ++ tailWord_3075998).sum := by decide
  have hdescent : baseEnd_3075998 < baseStart_3075998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3075998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076001 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3076001 : Nat := 118140960795 + 3076001 * 2 ^ 59
def prefixEnd_3076001 : Nat := 4983230072969 + 3 ^ 40 * 3076001 * 2
def baseEnd_3076001 : Nat := 1579467006710724865641235

theorem tailTrace_3076001 : CollatzResearch.WordTrace tailWord_3076001 prefixEnd_3076001 1579467006710724865641235 := by
  unfold tailWord_3076001
  simp only [CollatzResearch.WordTrace]
  refine ⟨112190973329181190991523857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74793982219454127327682571 112190973329181190991523857)
  ·
    refine ⟨84143229996885893243642893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112190973329181190991523857 84143229996885893243642893)
    ·
      refine ⟨31553711248832209966366085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84143229996885893243642893 31553711248832209966366085)
      ·
        refine ⟨5916320859156039368693641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31553711248832209966366085 5916320859156039368693641)
        ·
          refine ⟨4437240644367029526520231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5916320859156039368693641 4437240644367029526520231)
          ·
            refine ⟨6655860966550544289780347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437240644367029526520231 6655860966550544289780347)
            ·
              refine ⟨9983791449825816434670521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6655860966550544289780347 9983791449825816434670521)
              ·
                refine ⟨7487843587369362326002891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9983791449825816434670521 7487843587369362326002891)
                ·
                  refine ⟨11231765381054043489004337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487843587369362326002891 11231765381054043489004337)
                  ·
                    refine ⟨8423824035790532616753253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11231765381054043489004337 8423824035790532616753253)
                    ·
                      refine ⟨1579467006710724865641235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8423824035790532616753253 1579467006710724865641235)
                      ·
                        rfl

theorem cell23_3076001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3076001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076001 prefixEnd_3076001 := by exact prefixLift 3076001
  have htrace : WordTrace (prefixWord ++ tailWord_3076001) baseStart_3076001 baseEnd_3076001 := by
    simpa [prefixWord, tailWord_3076001, baseEnd_3076001] using wordTrace_append hprefix tailTrace_3076001
  have hstable : (prefixWord ++ tailWord_3076001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076001).length < 2 ^ (prefixWord ++ tailWord_3076001).sum := by decide
  have hdescent : baseEnd_3076001 < baseStart_3076001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076004 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_3076004 : Nat := 118140960795 + 3076004 * 2 ^ 59
def prefixEnd_3076004 : Nat := 4983230072969 + 3 ^ 40 * 3076004 * 2
def baseEnd_3076004 : Nat := 1579468547152688353903721

theorem tailTrace_3076004 : CollatzResearch.WordTrace tailWord_3076004 prefixEnd_3076004 1579468547152688353903721 := by
  unfold tailWord_3076004
  simp only [CollatzResearch.WordTrace]
  refine ⟨56095541374085161251941533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74794055165446881669255377 56095541374085161251941533)
  ·
    refine ⟨21035828015281935469478075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56095541374085161251941533 21035828015281935469478075)
    ·
      refine ⟨31553742022922903204217113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21035828015281935469478075 31553742022922903204217113)
      ·
        refine ⟨23665306517192177403162835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31553742022922903204217113 23665306517192177403162835)
        ·
          refine ⟨35497959775788266104744253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23665306517192177403162835 35497959775788266104744253)
          ·
            refine ⟨13311734915920599789279095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35497959775788266104744253 13311734915920599789279095)
            ·
              refine ⟨19967602373880899683918643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13311734915920599789279095 19967602373880899683918643)
              ·
                refine ⟨29951403560821349525877965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19967602373880899683918643 29951403560821349525877965)
                ·
                  refine ⟨11231776335308006072204237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29951403560821349525877965 11231776335308006072204237)
                  ·
                    refine ⟨4211916125740502277076589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11231776335308006072204237 4211916125740502277076589)
                    ·
                      refine ⟨1579468547152688353903721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4211916125740502277076589 1579468547152688353903721)
                      ·
                        rfl

theorem cell23_3076004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_3076004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076004 prefixEnd_3076004 := by exact prefixLift 3076004
  have htrace : WordTrace (prefixWord ++ tailWord_3076004) baseStart_3076004 baseEnd_3076004 := by
    simpa [prefixWord, tailWord_3076004, baseEnd_3076004] using wordTrace_append hprefix tailTrace_3076004
  have hstable : (prefixWord ++ tailWord_3076004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076004).length < 2 ^ (prefixWord ++ tailWord_3076004).sum := by decide
  have hdescent : baseEnd_3076004 < baseStart_3076004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076027 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 4]
def baseStart_3076027 : Nat := 118140960795 + 3076027 * 2 ^ 59
def prefixEnd_3076027 : Nat := 4983230072969 + 3 ^ 40 * 3076027 * 2
def baseEnd_3076027 : Nat := 1579480357207741763916115

theorem tailTrace_3076027 : CollatzResearch.WordTrace tailWord_3076027 prefixEnd_3076027 1579480357207741763916115 := by
  unfold tailWord_3076027
  simp only [CollatzResearch.WordTrace]
  refine ⟨112191921627086997431970335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74794614418057998287980223 112191921627086997431970335)
  ·
    refine ⟨168287882440630496147955503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112191921627086997431970335 168287882440630496147955503)
    ·
      refine ⟨252431823660945744221933255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168287882440630496147955503 252431823660945744221933255)
      ·
        refine ⟨378647735491418616332899883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252431823660945744221933255 378647735491418616332899883)
        ·
          refine ⟨567971603237127924499349825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378647735491418616332899883 567971603237127924499349825)
          ·
            refine ⟨425978702427845943374512369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567971603237127924499349825 425978702427845943374512369)
            ·
              refine ⟨319484026820884457530884277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425978702427845943374512369 319484026820884457530884277)
              ·
                refine ⟨29951627514457917893520401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 319484026820884457530884277 29951627514457917893520401)
                ·
                  refine ⟨22463720635843438420140301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29951627514457917893520401 22463720635843438420140301)
                  ·
                    refine ⟨8423895238441289407552613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22463720635843438420140301 8423895238441289407552613)
                    ·
                      refine ⟨1579480357207741763916115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8423895238441289407552613 1579480357207741763916115)
                      ·
                        rfl

theorem cell23_3076027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 4].length) (baseStart_3076027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076027 prefixEnd_3076027 := by exact prefixLift 3076027
  have htrace : WordTrace (prefixWord ++ tailWord_3076027) baseStart_3076027 baseEnd_3076027 := by
    simpa [prefixWord, tailWord_3076027, baseEnd_3076027] using wordTrace_append hprefix tailTrace_3076027
  have hstable : (prefixWord ++ tailWord_3076027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076027).length < 2 ^ (prefixWord ++ tailWord_3076027).sum := by decide
  have hdescent : baseEnd_3076027 < baseStart_3076027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076028 : List Nat := [2, 2, 2, 5, 2, 1, 1, 8]
def baseStart_3076028 : Nat := 118140960795 + 3076028 * 2 ^ 59
def prefixEnd_3076028 : Nat := 4983230072969 + 3 ^ 40 * 3076028 * 2
def baseEnd_3076028 : Nat := 58499291506977639259393

theorem tailTrace_3076028 : CollatzResearch.WordTrace tailWord_3076028 prefixEnd_3076028 58499291506977639259393 := by
  unfold tailWord_3076028
  simp only [CollatzResearch.WordTrace]
  refine ⟨56095979050041687301378369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74794638733388916401837825 56095979050041687301378369)
  ·
    refine ⟨42071984287531265476033777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56095979050041687301378369 42071984287531265476033777)
    ·
      refine ⟨31553988215648449107025333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42071984287531265476033777 31553988215648449107025333)
      ·
        refine ⟨2958186395217042103783625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31553988215648449107025333 2958186395217042103783625)
        ·
          refine ⟨2218639796412781577837719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2958186395217042103783625 2218639796412781577837719)
          ·
            refine ⟨3327959694619172366756579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218639796412781577837719 3327959694619172366756579)
            ·
              refine ⟨4991939541928758550134869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327959694619172366756579 4991939541928758550134869)
              ·
                refine ⟨58499291506977639259393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4991939541928758550134869 58499291506977639259393)
                ·
                  rfl

theorem cell23_3076028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 8].length) (baseStart_3076028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076028 prefixEnd_3076028 := by exact prefixLift 3076028
  have htrace : WordTrace (prefixWord ++ tailWord_3076028) baseStart_3076028 baseEnd_3076028 := by
    simpa [prefixWord, tailWord_3076028, baseEnd_3076028] using wordTrace_append hprefix tailTrace_3076028
  have hstable : (prefixWord ++ tailWord_3076028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076028).length < 2 ^ (prefixWord ++ tailWord_3076028).sum := by decide
  have hdescent : baseEnd_3076028 < baseStart_3076028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076074 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3076074 : Nat := 118140960795 + 3076074 * 2 ^ 59
def prefixEnd_3076074 : Nat := 4983230072969 + 3 ^ 40 * 3076074 * 2
def baseEnd_3076074 : Nat := 1579504490798503080028399

theorem tailTrace_3076074 : CollatzResearch.WordTrace tailWord_3076074 prefixEnd_3076074 1579504490798503080028399 := by
  unfold tailWord_3076074
  simp only [CollatzResearch.WordTrace]
  refine ⟨28048408964479181114732819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74795757238611149639287517 28048408964479181114732819)
  ·
    refine ⟨42072613446718771672099229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28048408964479181114732819 42072613446718771672099229)
    ·
      refine ⟨15777230042519539377037211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42072613446718771672099229 15777230042519539377037211)
      ·
        refine ⟨23665845063779309065555817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15777230042519539377037211 23665845063779309065555817)
        ·
          refine ⟨17749383797834481799166863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23665845063779309065555817 17749383797834481799166863)
          ·
            refine ⟨26624075696751722698750295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17749383797834481799166863 26624075696751722698750295)
            ·
              refine ⟨39936113545127584048125443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26624075696751722698750295 39936113545127584048125443)
              ·
                refine ⟨59904170317691376072188165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39936113545127584048125443 59904170317691376072188165)
                ·
                  refine ⟨11232031934567133013535281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59904170317691376072188165 11232031934567133013535281)
                  ·
                    refine ⟨8424023950925349760151461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11232031934567133013535281 8424023950925349760151461)
                    ·
                      refine ⟨1579504490798503080028399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8424023950925349760151461 1579504490798503080028399)
                      ·
                        rfl

theorem cell23_3076074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3076074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076074 prefixEnd_3076074 := by exact prefixLift 3076074
  have htrace : WordTrace (prefixWord ++ tailWord_3076074) baseStart_3076074 baseEnd_3076074 := by
    simpa [prefixWord, tailWord_3076074, baseEnd_3076074] using wordTrace_append hprefix tailTrace_3076074
  have hstable : (prefixWord ++ tailWord_3076074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076074).length < 2 ^ (prefixWord ++ tailWord_3076074).sum := by decide
  have hdescent : baseEnd_3076074 < baseStart_3076074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076135 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 7]
def baseStart_3076135 : Nat := 118140960795 + 3076135 * 2 ^ 59
def prefixEnd_3076135 : Nat := 4983230072969 + 3 ^ 40 * 3076135 * 2
def baseEnd_3076135 : Nat := 175503979235380815707291

theorem tailTrace_3076135 : CollatzResearch.WordTrace tailWord_3076135 prefixEnd_3076135 175503979235380815707291 := by
  unfold tailWord_3076135
  simp only [CollatzResearch.WordTrace]
  refine ⟨112195860710695731876901859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74797240473797154584601239 112195860710695731876901859)
  ·
    refine ⟨168293791066043597815352789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112195860710695731876901859 168293791066043597815352789)
    ·
      refine ⟨3944385728110396823797331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 168293791066043597815352789 3944385728110396823797331)
      ·
        refine ⟨5916578592165595235695997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3944385728110396823797331 5916578592165595235695997)
        ·
          refine ⟨2218716972062098213385999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5916578592165595235695997 2218716972062098213385999)
          ·
            refine ⟨3328075458093147320078999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218716972062098213385999 3328075458093147320078999)
            ·
              refine ⟨4992113187139720980118499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328075458093147320078999 4992113187139720980118499)
              ·
                refine ⟨7488169780709581470177749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992113187139720980118499 7488169780709581470177749)
                ·
                  refine ⟨175503979235380815707291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7488169780709581470177749 175503979235380815707291)
                  ·
                    rfl

theorem cell23_3076135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 7].length) (baseStart_3076135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076135 prefixEnd_3076135 := by exact prefixLift 3076135
  have htrace : WordTrace (prefixWord ++ tailWord_3076135) baseStart_3076135 baseEnd_3076135 := by
    simpa [prefixWord, tailWord_3076135, baseEnd_3076135] using wordTrace_append hprefix tailTrace_3076135
  have hstable : (prefixWord ++ tailWord_3076135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076135).length < 2 ^ (prefixWord ++ tailWord_3076135).sum := by decide
  have hdescent : baseEnd_3076135 < baseStart_3076135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076151 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 2, 4, 2]
def baseStart_3076151 : Nat := 118140960795 + 3076151 * 2 ^ 59
def prefixEnd_3076151 : Nat := 4983230072969 + 3 ^ 40 * 3076151 * 2
def baseEnd_3076151 : Nat := 1579544028808899278765545

theorem tailTrace_3076151 : CollatzResearch.WordTrace tailWord_3076151 prefixEnd_3076151 1579544028808899278765545 := by
  unfold tailWord_3076151
  simp only [CollatzResearch.WordTrace]
  refine ⟨112196444278637766609484307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74797629519091844406322871 112196444278637766609484307)
  ·
    refine ⟨168294666417956649914226461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112196444278637766609484307 168294666417956649914226461)
    ·
      refine ⟨63110499906733743717834923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168294666417956649914226461 63110499906733743717834923)
      ·
        refine ⟨94665749860100615576752385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63110499906733743717834923 94665749860100615576752385)
        ·
          refine ⟨70999312395075461682564289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94665749860100615576752385 70999312395075461682564289)
          ·
            refine ⟨53249484296306596261923217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70999312395075461682564289 53249484296306596261923217)
            ·
              refine ⟨39937113222229947196442413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53249484296306596261923217 39937113222229947196442413)
              ·
                refine ⟨14976417458336230198665905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39937113222229947196442413 14976417458336230198665905)
                ·
                  refine ⟨11232313093752172648999429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14976417458336230198665905 11232313093752172648999429)
                  ·
                    refine ⟨2106058705078532371687393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11232313093752172648999429 2106058705078532371687393)
                    ·
                      refine ⟨1579544028808899278765545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2106058705078532371687393 1579544028808899278765545)
                      ·
                        rfl

theorem cell23_3076151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_3076151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076151 prefixEnd_3076151 := by exact prefixLift 3076151
  have htrace : WordTrace (prefixWord ++ tailWord_3076151) baseStart_3076151 baseEnd_3076151 := by
    simpa [prefixWord, tailWord_3076151, baseEnd_3076151] using wordTrace_append hprefix tailTrace_3076151
  have hstable : (prefixWord ++ tailWord_3076151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076151).length < 2 ^ (prefixWord ++ tailWord_3076151).sum := by decide
  have hdescent : baseEnd_3076151 < baseStart_3076151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076188 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_3076188 : Nat := 118140960795 + 3076188 * 2 ^ 59
def prefixEnd_3076188 : Nat := 4983230072969 + 3 ^ 40 * 3076188 * 2
def baseEnd_3076188 : Nat := 1579563027593115634002875

theorem tailTrace_3076188 : CollatzResearch.WordTrace tailWord_3076188 prefixEnd_3076188 1579563027593115634002875 := by
  unfold tailWord_3076188
  simp only [CollatzResearch.WordTrace]
  refine ⟨56098896889751860964290609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74798529186335814619054145 56098896889751860964290609)
  ·
    refine ⟨42074172667313895723217957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56098896889751860964290609 42074172667313895723217957)
    ·
      refine ⟨7888907375121355448103367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42074172667313895723217957 7888907375121355448103367)
      ·
        refine ⟨11833361062682033172155051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7888907375121355448103367 11833361062682033172155051)
        ·
          refine ⟨17750041594023049758232577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11833361062682033172155051 17750041594023049758232577)
          ·
            refine ⟨13312531195517287318674433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17750041594023049758232577 13312531195517287318674433)
            ·
              refine ⟨9984398396637965489005825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13312531195517287318674433 9984398396637965489005825)
              ·
                refine ⟨7488298797478474116754369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9984398396637965489005825 7488298797478474116754369)
                ·
                  refine ⟨5616224098108855587565777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7488298797478474116754369 5616224098108855587565777)
                  ·
                    refine ⟨4212168073581641690674333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5616224098108855587565777 4212168073581641690674333)
                    ·
                      refine ⟨1579563027593115634002875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4212168073581641690674333 1579563027593115634002875)
                      ·
                        rfl

theorem cell23_3076188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_3076188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076188 prefixEnd_3076188 := by exact prefixLift 3076188
  have htrace : WordTrace (prefixWord ++ tailWord_3076188) baseStart_3076188 baseEnd_3076188 := by
    simpa [prefixWord, tailWord_3076188, baseEnd_3076188] using wordTrace_append hprefix tailTrace_3076188
  have hstable : (prefixWord ++ tailWord_3076188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076188).length < 2 ^ (prefixWord ++ tailWord_3076188).sum := by decide
  have hdescent : baseEnd_3076188 < baseStart_3076188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076195 : List Nat := [1, 1, 1, 5, 1, 1, 6, 2, 1, 4]
def baseStart_3076195 : Nat := 118140960795 + 3076195 * 2 ^ 59
def prefixEnd_3076195 : Nat := 4983230072969 + 3 ^ 40 * 3076195 * 2
def baseEnd_3076195 : Nat := 526522207319232368871781

theorem tailTrace_3076195 : CollatzResearch.WordTrace tailWord_3076195 prefixEnd_3076195 526522207319232368871781 := by
  unfold tailWord_3076195
  simp only [CollatzResearch.WordTrace]
  refine ⟨112198049090478362124086039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74798699393652241416057359 112198049090478362124086039)
  ·
    refine ⟨168297073635717543186129059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112198049090478362124086039 168297073635717543186129059)
    ·
      refine ⟨252445610453576314779193589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168297073635717543186129059 252445610453576314779193589)
      ·
        refine ⟨23666775980022779510549399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 252445610453576314779193589 23666775980022779510549399)
        ·
          refine ⟨35500163970034169265824099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23666775980022779510549399 35500163970034169265824099)
          ·
            refine ⟨53250245955051253898736149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35500163970034169265824099 53250245955051253898736149)
            ·
              refine ⟨2496105279143027526503257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53250245955051253898736149 2496105279143027526503257)
              ·
                refine ⟨1872078959357270644877443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496105279143027526503257 1872078959357270644877443)
                ·
                  refine ⟨2808118439035905967316165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872078959357270644877443 2808118439035905967316165)
                  ·
                    refine ⟨526522207319232368871781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2808118439035905967316165 526522207319232368871781)
                    ·
                      rfl

theorem cell23_3076195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 1, 4].length) (baseStart_3076195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076195 prefixEnd_3076195 := by exact prefixLift 3076195
  have htrace : WordTrace (prefixWord ++ tailWord_3076195) baseStart_3076195 baseEnd_3076195 := by
    simpa [prefixWord, tailWord_3076195, baseEnd_3076195] using wordTrace_append hprefix tailTrace_3076195
  have hstable : (prefixWord ++ tailWord_3076195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076195).length < 2 ^ (prefixWord ++ tailWord_3076195).sum := by decide
  have hdescent : baseEnd_3076195 < baseStart_3076195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076221 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_3076221 : Nat := 118140960795 + 3076221 * 2 ^ 59
def prefixEnd_3076221 : Nat := 4983230072969 + 3 ^ 40 * 3076221 * 2
def baseEnd_3076221 : Nat := 526526657484904668296741

theorem tailTrace_3076221 : CollatzResearch.WordTrace tailWord_3076221 prefixEnd_3076221 526526657484904668296741 := by
  unfold tailWord_3076221
  simp only [CollatzResearch.WordTrace]
  refine ⟨112198997388384168564532517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74799331592256112376355011 112198997388384168564532517)
  ·
    refine ⟨21037312010322031605849847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112198997388384168564532517 21037312010322031605849847)
    ·
      refine ⟨31555968015483047408774771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21037312010322031605849847 31555968015483047408774771)
      ·
        refine ⟨47333952023224571113162157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31555968015483047408774771 47333952023224571113162157)
        ·
          refine ⟨17750232008709214167435809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47333952023224571113162157 17750232008709214167435809)
          ·
            refine ⟨13312674006531910625576857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17750232008709214167435809 13312674006531910625576857)
            ·
              refine ⟨9984505504898932969182643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13312674006531910625576857 9984505504898932969182643)
              ·
                refine ⟨14976758257348399453773965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9984505504898932969182643 14976758257348399453773965)
                ·
                  refine ⟨5616284346505649795165237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14976758257348399453773965 5616284346505649795165237)
                  ·
                    refine ⟨526526657484904668296741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5616284346505649795165237 526526657484904668296741)
                    ·
                      rfl

theorem cell23_3076221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_3076221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076221 prefixEnd_3076221 := by exact prefixLift 3076221
  have htrace : WordTrace (prefixWord ++ tailWord_3076221) baseStart_3076221 baseEnd_3076221 := by
    simpa [prefixWord, tailWord_3076221, baseEnd_3076221] using wordTrace_append hprefix tailTrace_3076221
  have hstable : (prefixWord ++ tailWord_3076221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076221).length < 2 ^ (prefixWord ++ tailWord_3076221).sum := by decide
  have hdescent : baseEnd_3076221 < baseStart_3076221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076228 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_3076228 : Nat := 118140960795 + 3076228 * 2 ^ 59
def prefixEnd_3076228 : Nat := 4983230072969 + 3 ^ 40 * 3076228 * 2
def baseEnd_3076228 : Nat := 1579583566819295477502691

theorem tailTrace_3076228 : CollatzResearch.WordTrace tailWord_3076228 prefixEnd_3076228 1579583566819295477502691 := by
  unfold tailWord_3076228
  simp only [CollatzResearch.WordTrace]
  refine ⟨56099626349679404380018669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74799501799572539173358225 56099626349679404380018669)
  ·
    refine ⟨21037359881129776642507001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56099626349679404380018669 21037359881129776642507001)
    ·
      refine ⟨15778019910847332481880251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21037359881129776642507001 15778019910847332481880251)
      ·
        refine ⟨23667029866270998722820377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15778019910847332481880251 23667029866270998722820377)
        ·
          refine ⟨17750272399703249042115283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23667029866270998722820377 17750272399703249042115283)
          ·
            refine ⟨26625408599554873563172925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17750272399703249042115283 26625408599554873563172925)
            ·
              refine ⟨9984528224833077586189847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26625408599554873563172925 9984528224833077586189847)
              ·
                refine ⟨14976792337249616379284771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9984528224833077586189847 14976792337249616379284771)
                ·
                  refine ⟨22465188505874424568927157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14976792337249616379284771 22465188505874424568927157)
                  ·
                    refine ⟨2106111422425727303336921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22465188505874424568927157 2106111422425727303336921)
                    ·
                      refine ⟨1579583566819295477502691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2106111422425727303336921 1579583566819295477502691)
                      ·
                        rfl

theorem cell23_3076228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_3076228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076228 prefixEnd_3076228 := by exact prefixLift 3076228
  have htrace : WordTrace (prefixWord ++ tailWord_3076228) baseStart_3076228 baseEnd_3076228 := by
    simpa [prefixWord, tailWord_3076228, baseEnd_3076228] using wordTrace_append hprefix tailTrace_3076228
  have hstable : (prefixWord ++ tailWord_3076228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076228).length < 2 ^ (prefixWord ++ tailWord_3076228).sum := by decide
  have hdescent : baseEnd_3076228 < baseStart_3076228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076241 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 3, 8, 2]
def baseStart_3076241 : Nat := 118140960795 + 3076241 * 2 ^ 59
def prefixEnd_3076241 : Nat := 4983230072969 + 3 ^ 40 * 3076241 * 2
def baseEnd_3076241 : Nat := 1579590242067803926640131

theorem tailTrace_3076241 : CollatzResearch.WordTrace tailWord_3076241 prefixEnd_3076241 1579590242067803926640131 := by
  unfold tailWord_3076241
  simp only [CollatzResearch.WordTrace]
  refine ⟨112199726848311711980260577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74799817898874474653507051 112199726848311711980260577)
  ·
    refine ⟨84149795136233783985195433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112199726848311711980260577 84149795136233783985195433)
    ·
      refine ⟨63112346352175337988896575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84149795136233783985195433 63112346352175337988896575)
      ·
        refine ⟨94668519528263006983344863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63112346352175337988896575 94668519528263006983344863)
        ·
          refine ⟨142002779292394510475017295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94668519528263006983344863 142002779292394510475017295)
          ·
            refine ⟨213004168938591765712525943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142002779292394510475017295 213004168938591765712525943)
            ·
              refine ⟨319506253407887648568788915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213004168938591765712525943 319506253407887648568788915)
              ·
                refine ⟨479259380111831472853183373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319506253407887648568788915 479259380111831472853183373)
                ·
                  refine ⟨179722267541936802319943765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479259380111831472853183373 179722267541936802319943765)
                  ·
                    refine ⟨2106120322757071902186841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 179722267541936802319943765 2106120322757071902186841)
                    ·
                      refine ⟨1579590242067803926640131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2106120322757071902186841 1579590242067803926640131)
                      ·
                        rfl

theorem cell23_3076241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_3076241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076241 prefixEnd_3076241 := by exact prefixLift 3076241
  have htrace : WordTrace (prefixWord ++ tailWord_3076241) baseStart_3076241 baseEnd_3076241 := by
    simpa [prefixWord, tailWord_3076241, baseEnd_3076241] using wordTrace_append hprefix tailTrace_3076241
  have hstable : (prefixWord ++ tailWord_3076241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076241).length < 2 ^ (prefixWord ++ tailWord_3076241).sum := by decide
  have hdescent : baseEnd_3076241 < baseStart_3076241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076246 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3076246 : Nat := 118140960795 + 3076246 * 2 ^ 59
def prefixEnd_3076246 : Nat := 4983230072969 + 3 ^ 40 * 3076246 * 2
def baseEnd_3076246 : Nat := 526530936490358802359203

theorem tailTrace_3076246 : CollatzResearch.WordTrace tailWord_3076246 prefixEnd_3076246 526530936490358802359203 := by
  unfold tailWord_3076246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012494325830849864637037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74799939475529065222795061 7012494325830849864637037)
  ·
    refine ⟨2629685372186568699238889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7012494325830849864637037 2629685372186568699238889)
    ·
      refine ⟨1972264029139926524429167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2629685372186568699238889 1972264029139926524429167)
      ·
        refine ⟨2958396043709889786643751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972264029139926524429167 2958396043709889786643751)
        ·
          refine ⟨4437594065564834679965627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958396043709889786643751 4437594065564834679965627)
          ·
            refine ⟨6656391098347252019948441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437594065564834679965627 6656391098347252019948441)
            ·
              refine ⟨4992293323760439014961331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6656391098347252019948441 4992293323760439014961331)
              ·
                refine ⟨7488439985640658522441997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992293323760439014961331 7488439985640658522441997)
                ·
                  refine ⟨2808164994615246945915749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7488439985640658522441997 2808164994615246945915749)
                  ·
                    refine ⟨526530936490358802359203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2808164994615246945915749 526530936490358802359203)
                    ·
                      rfl

theorem cell23_3076246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3076246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076246 prefixEnd_3076246 := by exact prefixLift 3076246
  have htrace : WordTrace (prefixWord ++ tailWord_3076246) baseStart_3076246 baseEnd_3076246 := by
    simpa [prefixWord, tailWord_3076246, baseEnd_3076246] using wordTrace_append hprefix tailTrace_3076246
  have hstable : (prefixWord ++ tailWord_3076246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076246).length < 2 ^ (prefixWord ++ tailWord_3076246).sum := by decide
  have hdescent : baseEnd_3076246 < baseStart_3076246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076261 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_3076261 : Nat := 118140960795 + 3076261 * 2 ^ 59
def prefixEnd_3076261 : Nat := 4983230072969 + 3 ^ 40 * 3076261 * 2
def baseEnd_3076261 : Nat := 1579600511680893848390039

theorem tailTrace_3076261 : CollatzResearch.WordTrace tailWord_3076261 prefixEnd_3076261 1579600511680893848390039 := by
  unfold tailWord_3076261
  simp only [CollatzResearch.WordTrace]
  refine ⟨112200456308239255395988637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74800304205492836930659091 112200456308239255395988637)
  ·
    refine ⟨42075171115589720773495739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112200456308239255395988637 42075171115589720773495739)
    ·
      refine ⟨63112756673384581160243609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42075171115589720773495739 63112756673384581160243609)
      ·
        refine ⟨47334567505038435870182707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63112756673384581160243609 47334567505038435870182707)
        ·
          refine ⟨71001851257557653805274061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47334567505038435870182707 71001851257557653805274061)
          ·
            refine ⟨26625694221584120176977773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71001851257557653805274061 26625694221584120176977773)
            ·
              refine ⟨9984635333094045066366665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26625694221584120176977773 9984635333094045066366665)
              ·
                refine ⟨7488476499820533799774999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9984635333094045066366665 7488476499820533799774999)
                ·
                  refine ⟨11232714749730800699662499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7488476499820533799774999 11232714749730800699662499)
                  ·
                    refine ⟨16849072124596201049493749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11232714749730800699662499 16849072124596201049493749)
                    ·
                      refine ⟨1579600511680893848390039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16849072124596201049493749 1579600511680893848390039)
                      ·
                        rfl

theorem cell23_3076261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_3076261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076261 prefixEnd_3076261 := by exact prefixLift 3076261
  have htrace : WordTrace (prefixWord ++ tailWord_3076261) baseStart_3076261 baseEnd_3076261 := by
    simpa [prefixWord, tailWord_3076261, baseEnd_3076261] using wordTrace_append hprefix tailTrace_3076261
  have hstable : (prefixWord ++ tailWord_3076261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076261).length < 2 ^ (prefixWord ++ tailWord_3076261).sum := by decide
  have hdescent : baseEnd_3076261 < baseStart_3076261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076286 : List Nat := [4, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_3076286 : Nat := 118140960795 + 3076286 * 2 ^ 59
def prefixEnd_3076286 : Nat := 4983230072969 + 3 ^ 40 * 3076286 * 2
def baseEnd_3076286 : Nat := 1579613348697256250577425

theorem tailTrace_3076286 : CollatzResearch.WordTrace tailWord_3076286 prefixEnd_3076286 1579613348697256250577425 := by
  unfold tailWord_3076286
  simp only [CollatzResearch.WordTrace]
  refine ⟨14025171016643585583206089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74800912088765789777099141 14025171016643585583206089)
  ·
    refine ⟨10518878262482689187404567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14025171016643585583206089 10518878262482689187404567)
    ·
      refine ⟨15778317393724033781106851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10518878262482689187404567 15778317393724033781106851)
      ·
        refine ⟨23667476090586050671660277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15778317393724033781106851 23667476090586050671660277)
        ·
          refine ⟨2218825883492442250468151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23667476090586050671660277 2218825883492442250468151)
          ·
            refine ⟨3328238825238663375702227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218825883492442250468151 3328238825238663375702227)
            ·
              refine ⟨4992358237857995063553341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328238825238663375702227 4992358237857995063553341)
              ·
                refine ⟨1872134339196748148832503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4992358237857995063553341 1872134339196748148832503)
                ·
                  refine ⟨2808201508795122223248755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872134339196748148832503 2808201508795122223248755)
                  ·
                    refine ⟨4212302263192683334873133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2808201508795122223248755 4212302263192683334873133)
                    ·
                      refine ⟨1579613348697256250577425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4212302263192683334873133 1579613348697256250577425)
                      ·
                        rfl

theorem cell23_3076286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_3076286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076286 prefixEnd_3076286 := by exact prefixLift 3076286
  have htrace : WordTrace (prefixWord ++ tailWord_3076286) baseStart_3076286 baseEnd_3076286 := by
    simpa [prefixWord, tailWord_3076286, baseEnd_3076286] using wordTrace_append hprefix tailTrace_3076286
  have hstable : (prefixWord ++ tailWord_3076286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076286).length < 2 ^ (prefixWord ++ tailWord_3076286).sum := by decide
  have hdescent : baseEnd_3076286 < baseStart_3076286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076309 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 3, 2, 2]
def baseStart_3076309 : Nat := 118140960795 + 3076309 * 2 ^ 59
def prefixEnd_3076309 : Nat := 4983230072969 + 3 ^ 40 * 3076309 * 2
def baseEnd_3076309 : Nat := 1579625158752309660589819

theorem tailTrace_3076309 : CollatzResearch.WordTrace tailWord_3076309 prefixEnd_3076309 1579625158752309660589819 := by
  unfold tailWord_3076309
  simp only [CollatzResearch.WordTrace]
  refine ⟨112202207012065359593735981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74801471341376906395823987 112202207012065359593735981)
  ·
    refine ⟨42075827629524509847650993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112202207012065359593735981 42075827629524509847650993)
    ·
      refine ⟨31556870722143382385738245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42075827629524509847650993 31556870722143382385738245)
      ·
        refine ⟨5916913260401884197325921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31556870722143382385738245 5916913260401884197325921)
        ·
          refine ⟨4437684945301413147994441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5916913260401884197325921 4437684945301413147994441)
          ·
            refine ⟨3328263708976059860995831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4437684945301413147994441 3328263708976059860995831)
            ·
              refine ⟨4992395563464089791493747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328263708976059860995831 4992395563464089791493747)
              ·
                refine ⟨7488593345196134687240621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992395563464089791493747 7488593345196134687240621)
                ·
                  refine ⟨2808222504448550507715233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7488593345196134687240621 2808222504448550507715233)
                  ·
                    refine ⟨2106166878336412880786425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2808222504448550507715233 2106166878336412880786425)
                    ·
                      refine ⟨1579625158752309660589819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2106166878336412880786425 1579625158752309660589819)
                      ·
                        rfl

theorem cell23_3076309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_3076309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076309 prefixEnd_3076309 := by exact prefixLift 3076309
  have htrace : WordTrace (prefixWord ++ tailWord_3076309) baseStart_3076309 baseEnd_3076309 := by
    simpa [prefixWord, tailWord_3076309, baseEnd_3076309] using wordTrace_append hprefix tailTrace_3076309
  have hstable : (prefixWord ++ tailWord_3076309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076309).length < 2 ^ (prefixWord ++ tailWord_3076309).sum := by decide
  have hdescent : baseEnd_3076309 < baseStart_3076309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076335 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 3, 3, 2]
def baseStart_3076335 : Nat := 118140960795 + 3076335 * 2 ^ 59
def prefixEnd_3076335 : Nat := 4983230072969 + 3 ^ 40 * 3076335 * 2
def baseEnd_3076335 : Nat := 1579638509249326558864699

theorem tailTrace_3076335 : CollatzResearch.WordTrace tailWord_3076335 prefixEnd_3076335 1579638509249326558864699 := by
  unfold tailWord_3076335
  simp only [CollatzResearch.WordTrace]
  refine ⟨112203155309971166034182459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74802103539980777356121639 112203155309971166034182459)
  ·
    refine ⟨168304732964956749051273689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112203155309971166034182459 168304732964956749051273689)
    ·
      refine ⟨126228549723717561788455267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168304732964956749051273689 126228549723717561788455267)
      ·
        refine ⟨189342824585576342682682901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126228549723717561788455267 189342824585576342682682901)
        ·
          refine ⟨8875444902448891063250761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 189342824585576342682682901 8875444902448891063250761)
          ·
            refine ⟨6656583676836668297438071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8875444902448891063250761 6656583676836668297438071)
            ·
              refine ⟨9984875515255002446157107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6656583676836668297438071 9984875515255002446157107)
              ·
                refine ⟨14977313272882503669235661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9984875515255002446157107 14977313272882503669235661)
                ·
                  refine ⟨5616492477330938875963373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14977313272882503669235661 5616492477330938875963373)
                  ·
                    refine ⟨2106184678999102078486265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5616492477330938875963373 2106184678999102078486265)
                    ·
                      refine ⟨1579638509249326558864699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2106184678999102078486265 1579638509249326558864699)
                      ·
                        rfl

theorem cell23_3076335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 3, 2].length) (baseStart_3076335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076335 prefixEnd_3076335 := by exact prefixLift 3076335
  have htrace : WordTrace (prefixWord ++ tailWord_3076335) baseStart_3076335 baseEnd_3076335 := by
    simpa [prefixWord, tailWord_3076335, baseEnd_3076335] using wordTrace_append hprefix tailTrace_3076335
  have hstable : (prefixWord ++ tailWord_3076335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076335).length < 2 ^ (prefixWord ++ tailWord_3076335).sum := by decide
  have hdescent : baseEnd_3076335 < baseStart_3076335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076351 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_3076351 : Nat := 118140960795 + 3076351 * 2 ^ 59
def prefixEnd_3076351 : Nat := 4983230072969 + 3 ^ 40 * 3076351 * 2
def baseEnd_3076351 : Nat := 1579646724939798496264625

theorem tailTrace_3076351 : CollatzResearch.WordTrace tailWord_3076351 prefixEnd_3076351 1579646724939798496264625 := by
  unfold tailWord_3076351
  simp only [CollatzResearch.WordTrace]
  refine ⟨112203738877913200766764907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74802492585275467177843271 112203738877913200766764907)
  ·
    refine ⟨168305608316869801150147361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112203738877913200766764907 168305608316869801150147361)
    ·
      refine ⟨126229206237652350862610521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168305608316869801150147361 126229206237652350862610521)
      ·
        refine ⟨94671904678239263146957891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126229206237652350862610521 94671904678239263146957891)
        ·
          refine ⟨142007857017358894720436837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94671904678239263146957891 142007857017358894720436837)
          ·
            refine ⟨26626473190754792760081907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142007857017358894720436837 26626473190754792760081907)
            ·
              refine ⟨39939709786132189140122861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26626473190754792760081907 39939709786132189140122861)
              ·
                refine ⟨14977391169799570927546073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39939709786132189140122861 14977391169799570927546073)
                ·
                  refine ⟨11233043377349678195659555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14977391169799570927546073 11233043377349678195659555)
                  ·
                    refine ⟨16849565066024517293489333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11233043377349678195659555 16849565066024517293489333)
                    ·
                      refine ⟨1579646724939798496264625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16849565066024517293489333 1579646724939798496264625)
                      ·
                        rfl

theorem cell23_3076351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_3076351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076351 prefixEnd_3076351 := by exact prefixLift 3076351
  have htrace : WordTrace (prefixWord ++ tailWord_3076351) baseStart_3076351 baseEnd_3076351 := by
    simpa [prefixWord, tailWord_3076351, baseEnd_3076351] using wordTrace_append hprefix tailTrace_3076351
  have hstable : (prefixWord ++ tailWord_3076351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076351).length < 2 ^ (prefixWord ++ tailWord_3076351).sum := by decide
  have hdescent : baseEnd_3076351 < baseStart_3076351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076359 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3076359 : Nat := 118140960795 + 3076359 * 2 ^ 59
def prefixEnd_3076359 : Nat := 4983230072969 + 3 ^ 40 * 3076359 * 2
def baseEnd_3076359 : Nat := 1579650832785034464964589

theorem tailTrace_3076359 : CollatzResearch.WordTrace tailWord_3076359 prefixEnd_3076359 1579650832785034464964589 := by
  unfold tailWord_3076359
  simp only [CollatzResearch.WordTrace]
  refine ⟨112204030661884218133056131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74802687107922812088704087 112204030661884218133056131)
  ·
    refine ⟨168306045992826327199584197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112204030661884218133056131 168306045992826327199584197)
    ·
      refine ⟨31557383623654936349922037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168306045992826327199584197 31557383623654936349922037)
      ·
        refine ⟨2958504714717650282805191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31557383623654936349922037 2958504714717650282805191)
        ·
          refine ⟨4437757072076475424207787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958504714717650282805191 4437757072076475424207787)
          ·
            refine ⟨6656635608114713136311681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437757072076475424207787 6656635608114713136311681)
            ·
              refine ⟨4992476706086034852233761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6656635608114713136311681 4992476706086034852233761)
              ·
                refine ⟨3744357529564526139175321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4992476706086034852233761 3744357529564526139175321)
                ·
                  refine ⟨2808268147173394604381491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3744357529564526139175321 2808268147173394604381491)
                  ·
                    refine ⟨4212402220760091906572237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2808268147173394604381491 4212402220760091906572237)
                    ·
                      refine ⟨1579650832785034464964589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4212402220760091906572237 1579650832785034464964589)
                      ·
                        rfl

theorem cell23_3076359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3076359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076359 prefixEnd_3076359 := by exact prefixLift 3076359
  have htrace : WordTrace (prefixWord ++ tailWord_3076359) baseStart_3076359 baseEnd_3076359 := by
    simpa [prefixWord, tailWord_3076359, baseEnd_3076359] using wordTrace_append hprefix tailTrace_3076359
  have hstable : (prefixWord ++ tailWord_3076359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076359).length < 2 ^ (prefixWord ++ tailWord_3076359).sum := by decide
  have hdescent : baseEnd_3076359 < baseStart_3076359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076388 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 7]
def baseStart_3076388 : Nat := 118140960795 + 3076388 * 2 ^ 59
def prefixEnd_3076388 : Nat := 4983230072969 + 3 ^ 40 * 3076388 * 2
def baseEnd_3076388 : Nat := 175518413747112761277995

theorem tailTrace_3076388 : CollatzResearch.WordTrace tailWord_3076388 prefixEnd_3076388 175518413747112761277995 := by
  unfold tailWord_3076388
  simp only [CollatzResearch.WordTrace]
  refine ⟨56102544189389578042930909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74803392252519437390574545 56102544189389578042930909)
  ·
    refine ⟨21038454071021091766099091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56102544189389578042930909 21038454071021091766099091)
    ·
      refine ⟨31557681106531637649148637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21038454071021091766099091 31557681106531637649148637)
      ·
        refine ⟨11834130414949364118430739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31557681106531637649148637 11834130414949364118430739)
        ·
          refine ⟨17751195622424046177646109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11834130414949364118430739 17751195622424046177646109)
          ·
            refine ⟨6656698358409017316617291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17751195622424046177646109 6656698358409017316617291)
            ·
              refine ⟨9985047537613525974925937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6656698358409017316617291 9985047537613525974925937)
              ·
                refine ⟨7488785653210144481194453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9985047537613525974925937 7488785653210144481194453)
                ·
                  refine ⟨175518413747112761277995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7488785653210144481194453 175518413747112761277995)
                  ·
                    rfl

theorem cell23_3076388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_3076388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076388 prefixEnd_3076388 := by exact prefixLift 3076388
  have htrace : WordTrace (prefixWord ++ tailWord_3076388) baseStart_3076388 baseEnd_3076388 := by
    simpa [prefixWord, tailWord_3076388, baseEnd_3076388] using wordTrace_append hprefix tailTrace_3076388
  have hstable : (prefixWord ++ tailWord_3076388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076388).length < 2 ^ (prefixWord ++ tailWord_3076388).sum := by decide
  have hdescent : baseEnd_3076388 < baseStart_3076388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076405 : List Nat := [1, 3, 3, 1, 2, 1, 4, 3, 5]
def baseStart_3076405 : Nat := 118140960795 + 3076405 * 2 ^ 59
def prefixEnd_3076405 : Nat := 4983230072969 + 3 ^ 40 * 3076405 * 2
def baseEnd_3076405 : Nat := 175519383655015698332153

theorem tailTrace_3076405 : CollatzResearch.WordTrace tailWord_3076405 prefixEnd_3076405 175519383655015698332153 := by
  unfold tailWord_3076405
  simp only [CollatzResearch.WordTrace]
  refine ⟨112205708419717567989230669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74803805613145045326153779 112205708419717567989230669)
  ·
    refine ⟨42077140657394087995961501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112205708419717567989230669 42077140657394087995961501)
    ·
      refine ⟨15778927746522782998485563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42077140657394087995961501 15778927746522782998485563)
      ·
        refine ⟨23668391619784174497728345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15778927746522782998485563 23668391619784174497728345)
        ·
          refine ⟨17751293714838130873296259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23668391619784174497728345 17751293714838130873296259)
          ·
            refine ⟨26626940572257196309944389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17751293714838130873296259 26626940572257196309944389)
            ·
              refine ⟨4992551357298224308114573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26626940572257196309944389 4992551357298224308114573)
              ·
                refine ⟨1872206758986834115542965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4992551357298224308114573 1872206758986834115542965)
                ·
                  refine ⟨175519383655015698332153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1872206758986834115542965 175519383655015698332153)
                  ·
                    rfl

theorem cell23_3076405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_3076405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076405 prefixEnd_3076405 := by exact prefixLift 3076405
  have htrace : WordTrace (prefixWord ++ tailWord_3076405) baseStart_3076405 baseEnd_3076405 := by
    simpa [prefixWord, tailWord_3076405, baseEnd_3076405] using wordTrace_append hprefix tailTrace_3076405
  have hstable : (prefixWord ++ tailWord_3076405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076405).length < 2 ^ (prefixWord ++ tailWord_3076405).sum := by decide
  have hdescent : baseEnd_3076405 < baseStart_3076405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076475 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 3]
def baseStart_3076475 : Nat := 118140960795 + 3076475 * 2 ^ 59
def prefixEnd_3076475 : Nat := 4983230072969 + 3 ^ 40 * 3076475 * 2
def baseEnd_3076475 : Nat := 1579710396540956011114055

theorem tailTrace_3076475 : CollatzResearch.WordTrace tailWord_3076475 prefixEnd_3076475 1579710396540956011114055 := by
  unfold tailWord_3076475
  simp only [CollatzResearch.WordTrace]
  refine ⟨112208261529463969944278879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74805507686309313296185919 112208261529463969944278879)
  ·
    refine ⟨168312392294195954916418319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112208261529463969944278879 168312392294195954916418319)
    ·
      refine ⟨252468588441293932374627479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168312392294195954916418319 252468588441293932374627479)
      ·
        refine ⟨378702882661940898561941219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252468588441293932374627479 378702882661940898561941219)
        ·
          refine ⟨568054323992911347842911829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378702882661940898561941219 568054323992911347842911829)
          ·
            refine ⟨6656886609291929857534123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 568054323992911347842911829 6656886609291929857534123)
            ·
              refine ⟨9985329913937894786301185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6656886609291929857534123 9985329913937894786301185)
              ·
                refine ⟨7488997435453421089725889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9985329913937894786301185 7488997435453421089725889)
                ·
                  refine ⟨5616748076590065817294417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7488997435453421089725889 5616748076590065817294417)
                  ·
                    refine ⟨4212561057442549362970813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5616748076590065817294417 4212561057442549362970813)
                    ·
                      refine ⟨1579710396540956011114055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4212561057442549362970813 1579710396540956011114055)
                      ·
                        rfl

theorem cell23_3076475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 3].length) (baseStart_3076475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076475 prefixEnd_3076475 := by exact prefixLift 3076475
  have htrace : WordTrace (prefixWord ++ tailWord_3076475) baseStart_3076475 baseEnd_3076475 := by
    simpa [prefixWord, tailWord_3076475, baseEnd_3076475] using wordTrace_append hprefix tailTrace_3076475
  have hstable : (prefixWord ++ tailWord_3076475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076475).length < 2 ^ (prefixWord ++ tailWord_3076475).sum := by decide
  have hdescent : baseEnd_3076475 < baseStart_3076475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076505 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 5, 1, 3]
def baseStart_3076505 : Nat := 118140960795 + 3076505 * 2 ^ 59
def prefixEnd_3076505 : Nat := 4983230072969 + 3 ^ 40 * 3076505 * 2
def baseEnd_3076505 : Nat := 1579725800960590893738917

theorem tailTrace_3076505 : CollatzResearch.WordTrace tailWord_3076505 prefixEnd_3076505 1579725800960590893738917 := by
  unfold tailWord_3076505
  simp only [CollatzResearch.WordTrace]
  refine ⟨112209355719355285067870969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74806237146236856711913979 112209355719355285067870969)
  ·
    refine ⟨84157016789516463800903227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112209355719355285067870969 84157016789516463800903227)
    ·
      refine ⟨126235525184274695701354841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84157016789516463800903227 126235525184274695701354841)
      ·
        refine ⟨94676643888206021776016131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126235525184274695701354841 94676643888206021776016131)
        ·
          refine ⟨142014965832309032664024197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94676643888206021776016131 142014965832309032664024197)
          ·
            refine ⟨26627806093557943624504537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142014965832309032664024197 26627806093557943624504537)
            ·
              refine ⟨19970854570168457718378403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26627806093557943624504537 19970854570168457718378403)
              ·
                refine ⟨29956281855252686577567605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19970854570168457718378403 29956281855252686577567605)
                ·
                  refine ⟨2808401423929939366646963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29956281855252686577567605 2808401423929939366646963)
                  ·
                    refine ⟨4212602135894909049970445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2808401423929939366646963 4212602135894909049970445)
                    ·
                      refine ⟨1579725800960590893738917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4212602135894909049970445 1579725800960590893738917)
                      ·
                        rfl

theorem cell23_3076505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_3076505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076505 prefixEnd_3076505 := by exact prefixLift 3076505
  have htrace : WordTrace (prefixWord ++ tailWord_3076505) baseStart_3076505 baseEnd_3076505 := by
    simpa [prefixWord, tailWord_3076505, baseEnd_3076505] using wordTrace_append hprefix tailTrace_3076505
  have hstable : (prefixWord ++ tailWord_3076505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076505).length < 2 ^ (prefixWord ++ tailWord_3076505).sum := by decide
  have hdescent : baseEnd_3076505 < baseStart_3076505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076533 : List Nat := [1, 3, 3, 2, 4, 1, 2, 2, 1, 4]
def baseStart_3076533 : Nat := 118140960795 + 3076533 * 2 ^ 59
def prefixEnd_3076533 : Nat := 4983230072969 + 3 ^ 40 * 3076533 * 2
def baseEnd_3076533 : Nat := 526580059472972261396263

theorem tailTrace_3076533 : CollatzResearch.WordTrace tailWord_3076533 prefixEnd_3076533 526580059472972261396263 := by
  unfold tailWord_3076533
  simp only [CollatzResearch.WordTrace]
  refine ⟨112210376963253845849890253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74806917975502563899926835 112210376963253845849890253)
  ·
    refine ⟨42078891361220192193708845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112210376963253845849890253 42078891361220192193708845)
    ·
      refine ⟨15779584260457572072640817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42078891361220192193708845 15779584260457572072640817)
      ·
        refine ⟨11834688195343179054480613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15779584260457572072640817 11834688195343179054480613)
        ·
          refine ⟨2219004036626846072715115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11834688195343179054480613 2219004036626846072715115)
          ·
            refine ⟨3328506054940269109072673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219004036626846072715115 3328506054940269109072673)
            ·
              refine ⟨2496379541205201831804505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3328506054940269109072673 2496379541205201831804505)
              ·
                refine ⟨1872284655903901373853379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496379541205201831804505 1872284655903901373853379)
                ·
                  refine ⟨2808426983855852060780069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872284655903901373853379 2808426983855852060780069)
                  ·
                    refine ⟨526580059472972261396263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2808426983855852060780069 526580059472972261396263)
                    ·
                      rfl

theorem cell23_3076533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_3076533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076533 prefixEnd_3076533 := by exact prefixLift 3076533
  have htrace : WordTrace (prefixWord ++ tailWord_3076533) baseStart_3076533 baseEnd_3076533 := by
    simpa [prefixWord, tailWord_3076533, baseEnd_3076533] using wordTrace_append hprefix tailTrace_3076533
  have hstable : (prefixWord ++ tailWord_3076533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076533).length < 2 ^ (prefixWord ++ tailWord_3076533).sum := by decide
  have hdescent : baseEnd_3076533 < baseStart_3076533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076575 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 4]
def baseStart_3076575 : Nat := 118140960795 + 3076575 * 2 ^ 59
def prefixEnd_3076575 : Nat := 4983230072969 + 3 ^ 40 * 3076575 * 2
def baseEnd_3076575 : Nat := 1579761744606405619863595

theorem tailTrace_3076575 : CollatzResearch.WordTrace tailWord_3076575 prefixEnd_3076575 1579761744606405619863595 := by
  unfold tailWord_3076575
  simp only [CollatzResearch.WordTrace]
  refine ⟨112211908829101687022919179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74807939219401124681946119 112211908829101687022919179)
  ·
    refine ⟨168317863243652530534378769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112211908829101687022919179 168317863243652530534378769)
    ·
      refine ⟨126238397432739397900784077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168317863243652530534378769 126238397432739397900784077)
      ·
        refine ⟨47339399037277274212794029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126238397432739397900784077 47339399037277274212794029)
        ·
          refine ⟨17752274638978977829797761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47339399037277274212794029 17752274638978977829797761)
          ·
            refine ⟨13314205979234233372348321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17752274638978977829797761 13314205979234233372348321)
            ·
              refine ⟨9985654484425675029261241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13314205979234233372348321 9985654484425675029261241)
              ·
                refine ⟨7489240863319256271945931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9985654484425675029261241 7489240863319256271945931)
                ·
                  refine ⟨11233861294978884407918897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7489240863319256271945931 11233861294978884407918897)
                  ·
                    refine ⟨8425395971234163305939173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11233861294978884407918897 8425395971234163305939173)
                    ·
                      refine ⟨1579761744606405619863595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8425395971234163305939173 1579761744606405619863595)
                      ·
                        rfl

theorem cell23_3076575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_3076575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076575 prefixEnd_3076575 := by exact prefixLift 3076575
  have htrace : WordTrace (prefixWord ++ tailWord_3076575) baseStart_3076575 baseEnd_3076575 := by
    simpa [prefixWord, tailWord_3076575, baseEnd_3076575] using wordTrace_append hprefix tailTrace_3076575
  have hstable : (prefixWord ++ tailWord_3076575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076575).length < 2 ^ (prefixWord ++ tailWord_3076575).sum := by decide
  have hdescent : baseEnd_3076575 < baseStart_3076575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076589 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_3076589 : Nat := 118140960795 + 3076589 * 2 ^ 59
def prefixEnd_3076589 : Nat := 4983230072969 + 3 ^ 40 * 3076589 * 2
def baseEnd_3076589 : Nat := 526589644445189521696177

theorem tailTrace_3076589 : CollatzResearch.WordTrace tailWord_3076589 prefixEnd_3076589 526589644445189521696177 := by
  unfold tailWord_3076589
  simp only [CollatzResearch.WordTrace]
  refine ⟨112212419451050967413928821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74808279634033978275952547 112212419451050967413928821)
  ·
    refine ⟨10519914323536028195055827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112212419451050967413928821 10519914323536028195055827)
    ·
      refine ⟨15779871485304042292583741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10519914323536028195055827 15779871485304042292583741)
      ·
        refine ⟨5917451806989015859718903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15779871485304042292583741 5917451806989015859718903)
        ·
          refine ⟨8876177710483523789578355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5917451806989015859718903 8876177710483523789578355)
          ·
            refine ⟨13314266565725285684367533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8876177710483523789578355 13314266565725285684367533)
            ·
              refine ⟨4992849962146982131637825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13314266565725285684367533 4992849962146982131637825)
              ·
                refine ⟨3744637471610236598728369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4992849962146982131637825 3744637471610236598728369)
                ·
                  refine ⟨2808478103707677449046277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3744637471610236598728369 2808478103707677449046277)
                  ·
                    refine ⟨526589644445189521696177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2808478103707677449046277 526589644445189521696177)
                    ·
                      rfl

theorem cell23_3076589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_3076589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076589 prefixEnd_3076589 := by exact prefixLift 3076589
  have htrace : WordTrace (prefixWord ++ tailWord_3076589) baseStart_3076589 baseEnd_3076589 := by
    simpa [prefixWord, tailWord_3076589, baseEnd_3076589] using wordTrace_append hprefix tailTrace_3076589
  have hstable : (prefixWord ++ tailWord_3076589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076589).length < 2 ^ (prefixWord ++ tailWord_3076589).sum := by decide
  have hdescent : baseEnd_3076589 < baseStart_3076589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076608 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_3076608 : Nat := 118140960795 + 3076608 * 2 ^ 59
def prefixEnd_3076608 : Nat := 4983230072969 + 3 ^ 40 * 3076608 * 2
def baseEnd_3076608 : Nat := 1579778689468003990750943

theorem tailTrace_3076608 : CollatzResearch.WordTrace tailWord_3076608 prefixEnd_3076608 1579778689468003990750943 := by
  unfold tailWord_3076608
  simp only [CollatzResearch.WordTrace]
  refine ⟨56106556218991066829435239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74808741625321422439246985 56106556218991066829435239)
  ·
    refine ⟨84159834328486600244152859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56106556218991066829435239 84159834328486600244152859)
    ·
      refine ⟨126239751492729900366229289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84159834328486600244152859 126239751492729900366229289)
      ·
        refine ⟨94679813619547425274671967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126239751492729900366229289 94679813619547425274671967)
        ·
          refine ⟨142019720429321137912007951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94679813619547425274671967 142019720429321137912007951)
          ·
            refine ⟨213029580643981706868011927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142019720429321137912007951 213029580643981706868011927)
            ·
              refine ⟨319544370965972560302017891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213029580643981706868011927 319544370965972560302017891)
              ·
                refine ⟨479316556448958840453026837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319544370965972560302017891 479316556448958840453026837)
                ·
                  refine ⟨22467963583544945646235633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 479316556448958840453026837 22467963583544945646235633)
                  ·
                    refine ⟨16850972687658709234676725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22467963583544945646235633 16850972687658709234676725)
                    ·
                      refine ⟨1579778689468003990750943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16850972687658709234676725 1579778689468003990750943)
                      ·
                        rfl

theorem cell23_3076608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_3076608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076608 prefixEnd_3076608 := by exact prefixLift 3076608
  have htrace : WordTrace (prefixWord ++ tailWord_3076608) baseStart_3076608 baseEnd_3076608 := by
    simpa [prefixWord, tailWord_3076608, baseEnd_3076608] using wordTrace_append hprefix tailTrace_3076608
  have hstable : (prefixWord ++ tailWord_3076608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076608).length < 2 ^ (prefixWord ++ tailWord_3076608).sum := by decide
  have hdescent : baseEnd_3076608 < baseStart_3076608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076647 : List Nat := [1, 1, 7, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3076647 : Nat := 118140960795 + 3076647 * 2 ^ 59
def prefixEnd_3076647 : Nat := 4983230072969 + 3 ^ 40 * 3076647 * 2
def baseEnd_3076647 : Nat := 1579798715213529338163265

theorem tailTrace_3076647 : CollatzResearch.WordTrace tailWord_3076647 prefixEnd_3076647 1579798715213529338163265 := by
  unfold tailWord_3076647
  simp only [CollatzResearch.WordTrace]
  refine ⟨112214534884840843319540195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74809689923227228879693463 112214534884840843319540195)
  ·
    refine ⟨168321802327261264979310293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112214534884840843319540195 168321802327261264979310293)
    ·
      refine ⟨3945042242045185897952585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 168321802327261264979310293 3945042242045185897952585)
      ·
        refine ⟨2958781681533889423464439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3945042242045185897952585 2958781681533889423464439)
        ·
          refine ⟨4438172522300834135196659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958781681533889423464439 4438172522300834135196659)
          ·
            refine ⟨6657258783451251202794989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438172522300834135196659 6657258783451251202794989)
            ·
              refine ⟨2496472043794219201048121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6657258783451251202794989 2496472043794219201048121)
              ·
                refine ⟨1872354032845664400786091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496472043794219201048121 1872354032845664400786091)
                ·
                  refine ⟨2808531049268496601179137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872354032845664400786091 2808531049268496601179137)
                  ·
                    refine ⟨2106398286951372450884353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2808531049268496601179137 2106398286951372450884353)
                    ·
                      refine ⟨1579798715213529338163265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2106398286951372450884353 1579798715213529338163265)
                      ·
                        rfl

theorem cell23_3076647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3076647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076647 prefixEnd_3076647 := by exact prefixLift 3076647
  have htrace : WordTrace (prefixWord ++ tailWord_3076647) baseStart_3076647 baseEnd_3076647 := by
    simpa [prefixWord, tailWord_3076647, baseEnd_3076647] using wordTrace_append hprefix tailTrace_3076647
  have hstable : (prefixWord ++ tailWord_3076647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076647).length < 2 ^ (prefixWord ++ tailWord_3076647).sum := by decide
  have hdescent : baseEnd_3076647 < baseStart_3076647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076665 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3076665 : Nat := 118140960795 + 3076665 * 2 ^ 59
def prefixEnd_3076665 : Nat := 4983230072969 + 3 ^ 40 * 3076665 * 2
def baseEnd_3076665 : Nat := 1579807957865310267738181

theorem tailTrace_3076665 : CollatzResearch.WordTrace tailWord_3076665 prefixEnd_3076665 1579807957865310267738181 := by
  unfold tailWord_3076665
  simp only [CollatzResearch.WordTrace]
  refine ⟨112215191398775632393695449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74810127599183754929130299 112215191398775632393695449)
  ·
    refine ⟨84161393549081724295271587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112215191398775632393695449 84161393549081724295271587)
    ·
      refine ⟨126242090323622586442907381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84161393549081724295271587 126242090323622586442907381)
      ·
        refine ⟨11835195967839617479022567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126242090323622586442907381 11835195967839617479022567)
        ·
          refine ⟨17752793951759426218533851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11835195967839617479022567 17752793951759426218533851)
          ·
            refine ⟨26629190927639139327800777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17752793951759426218533851 26629190927639139327800777)
            ·
              refine ⟨19971893195729354495850583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26629190927639139327800777 19971893195729354495850583)
              ·
                refine ⟨29957839793594031743775875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19971893195729354495850583 29957839793594031743775875)
                ·
                  refine ⟨44936759690391047615663813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29957839793594031743775875 44936759690391047615663813)
                  ·
                    refine ⟨8425642441948321427936965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44936759690391047615663813 8425642441948321427936965)
                    ·
                      refine ⟨1579807957865310267738181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8425642441948321427936965 1579807957865310267738181)
                      ·
                        rfl

theorem cell23_3076665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3076665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076665 prefixEnd_3076665 := by exact prefixLift 3076665
  have htrace : WordTrace (prefixWord ++ tailWord_3076665) baseStart_3076665 baseEnd_3076665 := by
    simpa [prefixWord, tailWord_3076665, baseEnd_3076665] using wordTrace_append hprefix tailTrace_3076665
  have hstable : (prefixWord ++ tailWord_3076665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076665).length < 2 ^ (prefixWord ++ tailWord_3076665).sum := by decide
  have hdescent : baseEnd_3076665 < baseStart_3076665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076709 : List Nat := [1, 3, 1, 3, 4, 1, 1, 4, 5]
def baseStart_3076709 : Nat := 118140960795 + 3076709 * 2 ^ 59
def prefixEnd_3076709 : Nat := 4983230072969 + 3 ^ 40 * 3076709 * 2
def baseEnd_3076709 : Nat := 175536727890456455065331

theorem tailTrace_3076709 : CollatzResearch.WordTrace tailWord_3076709 prefixEnd_3076709 175536727890456455065331 := by
  unfold tailWord_3076709
  simp only [CollatzResearch.WordTrace]
  refine ⟨112216796210616227908297181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74811197473744151938864787 112216796210616227908297181)
  ·
    refine ⟨42081298578981085465611443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112216796210616227908297181 42081298578981085465611443)
    ·
      refine ⟨63121947868471628198417165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42081298578981085465611443 63121947868471628198417165)
      ·
        refine ⟨23670730450676860574406437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63121947868471628198417165 23670730450676860574406437)
        ·
          refine ⟨4438261959501911357701207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23670730450676860574406437 4438261959501911357701207)
          ·
            refine ⟨6657392939252867036551811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438261959501911357701207 6657392939252867036551811)
            ·
              refine ⟨9986089408879300554827717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6657392939252867036551811 9986089408879300554827717)
              ·
                refine ⟨1872391764164868854030197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9986089408879300554827717 1872391764164868854030197)
                ·
                  refine ⟨175536727890456455065331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1872391764164868854030197 175536727890456455065331)
                  ·
                    rfl

theorem cell23_3076709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_3076709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076709 prefixEnd_3076709 := by exact prefixLift 3076709
  have htrace : WordTrace (prefixWord ++ tailWord_3076709) baseStart_3076709 baseEnd_3076709 := by
    simpa [prefixWord, tailWord_3076709, baseEnd_3076709] using wordTrace_append hprefix tailTrace_3076709
  have hstable : (prefixWord ++ tailWord_3076709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076709).length < 2 ^ (prefixWord ++ tailWord_3076709).sum := by decide
  have hdescent : baseEnd_3076709 < baseStart_3076709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076805 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_3076805 : Nat := 118140960795 + 3076805 * 2 ^ 59
def prefixEnd_3076805 : Nat := 4983230072969 + 3 ^ 40 * 3076805 * 2
def baseEnd_3076805 : Nat := 1579879845156939719987537

theorem tailTrace_3076805 : CollatzResearch.WordTrace tailWord_3076805 prefixEnd_3076805 1579879845156939719987537 := by
  unfold tailWord_3076805
  simp only [CollatzResearch.WordTrace]
  refine ⟨112220297618268436303791869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74813531745512290869194579 112220297618268436303791869)
  ·
    refine ⟨42082611606850663613921951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112220297618268436303791869 42082611606850663613921951)
    ·
      refine ⟨63123917410275995420882927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42082611606850663613921951 63123917410275995420882927)
      ·
        refine ⟨94685876115413993131324391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63123917410275995420882927 94685876115413993131324391)
        ·
          refine ⟨142028814173120989696986587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94685876115413993131324391 142028814173120989696986587)
          ·
            refine ⟨213043221259681484545479881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142028814173120989696986587 213043221259681484545479881)
            ·
              refine ⟨159782415944761113409109911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213043221259681484545479881 159782415944761113409109911)
              ·
                refine ⟨239673623917141670113664867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159782415944761113409109911 239673623917141670113664867)
                ·
                  refine ⟨359510435875712505170497301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239673623917141670113664867 359510435875712505170497301)
                  ·
                    refine ⟨16852051681674023679867061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 359510435875712505170497301 16852051681674023679867061)
                    ·
                      refine ⟨1579879845156939719987537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16852051681674023679867061 1579879845156939719987537)
                      ·
                        rfl

theorem cell23_3076805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_3076805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076805 prefixEnd_3076805 := by exact prefixLift 3076805
  have htrace : WordTrace (prefixWord ++ tailWord_3076805) baseStart_3076805 baseEnd_3076805 := by
    simpa [prefixWord, tailWord_3076805, baseEnd_3076805] using wordTrace_append hprefix tailTrace_3076805
  have hstable : (prefixWord ++ tailWord_3076805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076805).length < 2 ^ (prefixWord ++ tailWord_3076805).sum := by decide
  have hdescent : baseEnd_3076805 < baseStart_3076805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076813 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3076813 : Nat := 118140960795 + 3076813 * 2 ^ 59
def prefixEnd_3076813 : Nat := 4983230072969 + 3 ^ 40 * 3076813 * 2
def baseEnd_3076813 : Nat := 1579883953002175688687501

theorem tailTrace_3076813 : CollatzResearch.WordTrace tailWord_3076813 prefixEnd_3076813 1579883953002175688687501 := by
  unfold tailWord_3076813
  simp only [CollatzResearch.WordTrace]
  refine ⟨112220589402239453670083093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74813726268159635780055395 112220589402239453670083093)
  ·
    refine ⟨5260340128229974390785145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112220589402239453670083093 5260340128229974390785145)
    ·
      refine ⟨3945255096172480793088859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5260340128229974390785145 3945255096172480793088859)
      ·
        refine ⟨5917882644258721189633289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945255096172480793088859 5917882644258721189633289)
        ·
          refine ⟨4438411983194040892224967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5917882644258721189633289 4438411983194040892224967)
          ·
            refine ⟨6657617974791061338337451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438411983194040892224967 6657617974791061338337451)
            ·
              refine ⟨9986426962186592007506177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6657617974791061338337451 9986426962186592007506177)
              ·
                refine ⟨7489820221639944005629633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9986426962186592007506177 7489820221639944005629633)
                ·
                  refine ⟨5617365166229958004222225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7489820221639944005629633 5617365166229958004222225)
                  ·
                    refine ⟨4213023874672468503166669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5617365166229958004222225 4213023874672468503166669)
                    ·
                      refine ⟨1579883953002175688687501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213023874672468503166669 1579883953002175688687501)
                      ·
                        rfl

theorem cell23_3076813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3076813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076813 prefixEnd_3076813 := by exact prefixLift 3076813
  have htrace : WordTrace (prefixWord ++ tailWord_3076813) baseStart_3076813 baseEnd_3076813 := by
    simpa [prefixWord, tailWord_3076813, baseEnd_3076813] using wordTrace_append hprefix tailTrace_3076813
  have hstable : (prefixWord ++ tailWord_3076813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076813).length < 2 ^ (prefixWord ++ tailWord_3076813).sum := by decide
  have hdescent : baseEnd_3076813 < baseStart_3076813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076820 : List Nat := [2, 4, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_3076820 : Nat := 118140960795 + 3076820 * 2 ^ 59
def prefixEnd_3076820 : Nat := 4983230072969 + 3 ^ 40 * 3076820 * 2
def baseEnd_3076820 : Nat := 526629182455585720433323

theorem tailTrace_3076820 : CollatzResearch.WordTrace tailWord_3076820 prefixEnd_3076820 526629182455585720433323 := by
  unfold tailWord_3076820
  simp only [CollatzResearch.WordTrace]
  refine ⟨56110422356607046932793957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74813896475476062577058609 56110422356607046932793957)
  ·
    refine ⟨10520704191863821299898867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56110422356607046932793957 10520704191863821299898867)
    ·
      refine ⟨15781056287795731949848301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10520704191863821299898867 15781056287795731949848301)
      ·
        refine ⟨5917896107923399481193113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15781056287795731949848301 5917896107923399481193113)
        ·
          refine ⟨4438422080942549610894835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5917896107923399481193113 4438422080942549610894835)
          ·
            refine ⟨6657633121413824416342253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438422080942549610894835 6657633121413824416342253)
            ·
              refine ⟨2496612420530184156128345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6657633121413824416342253 2496612420530184156128345)
              ·
                refine ⟨1872459315397638117096259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496612420530184156128345 1872459315397638117096259)
                ·
                  refine ⟨2808688973096457175644389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872459315397638117096259 2808688973096457175644389)
                  ·
                    refine ⟨526629182455585720433323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2808688973096457175644389 526629182455585720433323)
                    ·
                      rfl

theorem cell23_3076820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_3076820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076820 prefixEnd_3076820 := by exact prefixLift 3076820
  have htrace : WordTrace (prefixWord ++ tailWord_3076820) baseStart_3076820 baseEnd_3076820 := by
    simpa [prefixWord, tailWord_3076820, baseEnd_3076820] using wordTrace_append hprefix tailTrace_3076820
  have hstable : (prefixWord ++ tailWord_3076820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076820).length < 2 ^ (prefixWord ++ tailWord_3076820).sum := by decide
  have hdescent : baseEnd_3076820 < baseStart_3076820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076832 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 4]
def baseStart_3076832 : Nat := 118140960795 + 3076832 * 2 ^ 59
def prefixEnd_3076832 : Nat := 4983230072969 + 3 ^ 40 * 3076832 * 2
def baseEnd_3076832 : Nat := 1579893709134611114349913

theorem tailTrace_3076832 : CollatzResearch.WordTrace tailWord_3076832 prefixEnd_3076832 1579893709134611114349913 := by
  unfold tailWord_3076832
  simp only [CollatzResearch.WordTrace]
  refine ⟨56110641194585309957512375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74814188259447079943349833 56110641194585309957512375)
  ·
    refine ⟨84165961791877964936268563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56110641194585309957512375 84165961791877964936268563)
    ·
      refine ⟨126248942687816947404402845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84165961791877964936268563 126248942687816947404402845)
      ·
        refine ⟨47343353507931355276651067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126248942687816947404402845 47343353507931355276651067)
        ·
          refine ⟨71015030261897032914976601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47343353507931355276651067 71015030261897032914976601)
          ·
            refine ⟨53261272696422774686232451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71015030261897032914976601 53261272696422774686232451)
            ·
              refine ⟨79891909044634162029348677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53261272696422774686232451 79891909044634162029348677)
              ·
                refine ⟨14979732945868905380502877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79891909044634162029348677 14979732945868905380502877)
                ·
                  refine ⟨5617399854700839517688579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14979732945868905380502877 5617399854700839517688579)
                  ·
                    refine ⟨8426099782051259276532869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5617399854700839517688579 8426099782051259276532869)
                    ·
                      refine ⟨1579893709134611114349913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8426099782051259276532869 1579893709134611114349913)
                      ·
                        rfl

theorem cell23_3076832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_3076832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076832 prefixEnd_3076832 := by exact prefixLift 3076832
  have htrace : WordTrace (prefixWord ++ tailWord_3076832) baseStart_3076832 baseEnd_3076832 := by
    simpa [prefixWord, tailWord_3076832, baseEnd_3076832] using wordTrace_append hprefix tailTrace_3076832
  have hstable : (prefixWord ++ tailWord_3076832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076832).length < 2 ^ (prefixWord ++ tailWord_3076832).sum := by decide
  have hdescent : baseEnd_3076832 < baseStart_3076832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076842 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_3076842 : Nat := 118140960795 + 3076842 * 2 ^ 59
def prefixEnd_3076842 : Nat := 4983230072969 + 3 ^ 40 * 3076842 * 2
def baseEnd_3076842 : Nat := 526632947980385358408289

theorem tailTrace_3076842 : CollatzResearch.WordTrace tailWord_3076842 prefixEnd_3076842 526632947980385358408289 := by
  unfold tailWord_3076842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28055411779783597905722195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74814431412756261081925853 28055411779783597905722195)
  ·
    refine ⟨42083117669675396858583293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28055411779783597905722195 42083117669675396858583293)
    ·
      refine ⟨15781169126128273821968735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42083117669675396858583293 15781169126128273821968735)
      ·
        refine ⟨23671753689192410732953103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15781169126128273821968735 23671753689192410732953103)
        ·
          refine ⟨35507630533788616099429655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23671753689192410732953103 35507630533788616099429655)
          ·
            refine ⟨53261445800682924149144483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35507630533788616099429655 53261445800682924149144483)
            ·
              refine ⟨79892168701024386223716725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53261445800682924149144483 79892168701024386223716725)
              ·
                refine ⟨7489890815721036208473443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79892168701024386223716725 7489890815721036208473443)
                ·
                  refine ⟨11234836223581554312710165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7489890815721036208473443 11234836223581554312710165)
                  ·
                    refine ⟨526632947980385358408289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11234836223581554312710165 526632947980385358408289)
                    ·
                      rfl

theorem cell23_3076842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_3076842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076842 prefixEnd_3076842 := by exact prefixLift 3076842
  have htrace : WordTrace (prefixWord ++ tailWord_3076842) baseStart_3076842 baseEnd_3076842 := by
    simpa [prefixWord, tailWord_3076842, baseEnd_3076842] using wordTrace_append hprefix tailTrace_3076842
  have hstable : (prefixWord ++ tailWord_3076842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076842).length < 2 ^ (prefixWord ++ tailWord_3076842).sum := by decide
  have hdescent : baseEnd_3076842 < baseStart_3076842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076846 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3076846 : Nat := 118140960795 + 3076846 * 2 ^ 59
def prefixEnd_3076846 : Nat := 4983230072969 + 3 ^ 40 * 3076846 * 2
def baseEnd_3076846 : Nat := 526633632621258019858283

theorem tailTrace_3076846 : CollatzResearch.WordTrace tailWord_3076846 prefixEnd_3076846 526633632621258019858283 := by
  unfold tailWord_3076846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14027724126389987538254299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74814528674079933537356261 14027724126389987538254299)
  ·
    refine ⟨21041586189584981307381449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14027724126389987538254299 21041586189584981307381449)
    ·
      refine ⟨15781189642188735980536087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21041586189584981307381449 15781189642188735980536087)
      ·
        refine ⟨23671784463283103970804131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15781189642188735980536087 23671784463283103970804131)
        ·
          refine ⟨35507676694924655956206197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23671784463283103970804131 35507676694924655956206197)
          ·
            refine ⟨3328844690149186495894331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35507676694924655956206197 3328844690149186495894331)
            ·
              refine ⟨4993267035223779743841497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328844690149186495894331 4993267035223779743841497)
              ·
                refine ⟨3744950276417834807881123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4993267035223779743841497 3744950276417834807881123)
                ·
                  refine ⟨5617425414626752211821685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744950276417834807881123 5617425414626752211821685)
                  ·
                    refine ⟨526633632621258019858283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5617425414626752211821685 526633632621258019858283)
                    ·
                      rfl

theorem cell23_3076846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3076846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076846 prefixEnd_3076846 := by exact prefixLift 3076846
  have htrace : WordTrace (prefixWord ++ tailWord_3076846) baseStart_3076846 baseEnd_3076846 := by
    simpa [prefixWord, tailWord_3076846, baseEnd_3076846] using wordTrace_append hprefix tailTrace_3076846
  have hstable : (prefixWord ++ tailWord_3076846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076846).length < 2 ^ (prefixWord ++ tailWord_3076846).sum := by decide
  have hdescent : baseEnd_3076846 < baseStart_3076846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076869 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 1, 2, 3]
def baseStart_3076869 : Nat := 118140960795 + 3076869 * 2 ^ 59
def prefixEnd_3076869 : Nat := 4983230072969 + 3 ^ 40 * 3076869 * 2
def baseEnd_3076869 : Nat := 1579912707918827469587243

theorem tailTrace_3076869 : CollatzResearch.WordTrace tailWord_3076869 prefixEnd_3076869 1579912707918827469587243 := by
  unfold tailWord_3076869
  simp only [CollatzResearch.WordTrace]
  refine ⟨112222631890036575234121661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74815087926691050156081107 112222631890036575234121661)
  ·
    refine ⟨42083486958763715712795623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112222631890036575234121661 42083486958763715712795623)
    ·
      refine ⟨63125230438145573569193435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42083486958763715712795623 63125230438145573569193435)
      ·
        refine ⟨94687845657218360353790153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63125230438145573569193435 94687845657218360353790153)
        ·
          refine ⟨71015884242913770265342615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94687845657218360353790153 71015884242913770265342615)
          ·
            refine ⟨106523826364370655398013923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71015884242913770265342615 106523826364370655398013923)
            ·
              refine ⟨159785739546555983097020885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106523826364370655398013923 159785739546555983097020885)
              ·
                refine ⟨3744978270622405853836427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 159785739546555983097020885 3744978270622405853836427)
                ·
                  refine ⟨5617467405933608780754641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744978270622405853836427 5617467405933608780754641)
                  ·
                    refine ⟨4213100554450206585565981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5617467405933608780754641 4213100554450206585565981)
                    ·
                      refine ⟨1579912707918827469587243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213100554450206585565981 1579912707918827469587243)
                      ·
                        rfl

theorem cell23_3076869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_3076869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076869 prefixEnd_3076869 := by exact prefixLift 3076869
  have htrace : WordTrace (prefixWord ++ tailWord_3076869) baseStart_3076869 baseEnd_3076869 := by
    simpa [prefixWord, tailWord_3076869, baseEnd_3076869] using wordTrace_append hprefix tailTrace_3076869
  have hstable : (prefixWord ++ tailWord_3076869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076869).length < 2 ^ (prefixWord ++ tailWord_3076869).sum := by decide
  have hdescent : baseEnd_3076869 < baseStart_3076869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076883 : List Nat := [1, 1, 1, 2, 1, 3, 5, 4, 1, 2, 2]
def baseStart_3076883 : Nat := 118140960795 + 3076883 * 2 ^ 59
def prefixEnd_3076883 : Nat := 4983230072969 + 3 ^ 40 * 3076883 * 2
def baseEnd_3076883 : Nat := 1579919896647990414812179

theorem tailTrace_3076883 : CollatzResearch.WordTrace tailWord_3076883 prefixEnd_3076883 1579919896647990414812179 := by
  unfold tailWord_3076883
  simp only [CollatzResearch.WordTrace]
  refine ⟨112223142511985855625131303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74815428341323903750087535 112223142511985855625131303)
  ·
    refine ⟨168334713767978783437696955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112223142511985855625131303 168334713767978783437696955)
    ·
      refine ⟨252502070651968175156545433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168334713767978783437696955 252502070651968175156545433)
      ·
        refine ⟨189376552988976131367409075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252502070651968175156545433 189376552988976131367409075)
        ·
          refine ⟨284064829483464197051113613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189376552988976131367409075 284064829483464197051113613)
          ·
            refine ⟨106524311056299073894167605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284064829483464197051113613 106524311056299073894167605)
            ·
              refine ⟨9986654161528038177578213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106524311056299073894167605 9986654161528038177578213)
              ·
                refine ⟨1872497655286507158295915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9986654161528038177578213 1872497655286507158295915)
                ·
                  refine ⟨2808746482929760737443873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872497655286507158295915 2808746482929760737443873)
                  ·
                    refine ⟨2106559862197320553082905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2808746482929760737443873 2106559862197320553082905)
                    ·
                      refine ⟨1579919896647990414812179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2106559862197320553082905 1579919896647990414812179)
                      ·
                        rfl

theorem cell23_3076883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 1, 2, 2].length) (baseStart_3076883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076883 prefixEnd_3076883 := by exact prefixLift 3076883
  have htrace : WordTrace (prefixWord ++ tailWord_3076883) baseStart_3076883 baseEnd_3076883 := by
    simpa [prefixWord, tailWord_3076883, baseEnd_3076883] using wordTrace_append hprefix tailTrace_3076883
  have hstable : (prefixWord ++ tailWord_3076883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076883).length < 2 ^ (prefixWord ++ tailWord_3076883).sum := by decide
  have hdescent : baseEnd_3076883 < baseStart_3076883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076899 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 6, 1, 3]
def baseStart_3076899 : Nat := 118140960795 + 3076899 * 2 ^ 59
def prefixEnd_3076899 : Nat := 4983230072969 + 3 ^ 40 * 3076899 * 2
def baseEnd_3076899 : Nat := 1579928112338462352212105

theorem tailTrace_3076899 : CollatzResearch.WordTrace tailWord_3076899 prefixEnd_3076899 1579928112338462352212105 := by
  unfold tailWord_3076899
  simp only [CollatzResearch.WordTrace]
  refine ⟨112223726079927890357713751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74815817386618593571809167 112223726079927890357713751)
  ·
    refine ⟨168335589119891835536570627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112223726079927890357713751 168335589119891835536570627)
    ·
      refine ⟨252503383679837753304855941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168335589119891835536570627 252503383679837753304855941)
      ·
        refine ⟨47344384439969578744660489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252503383679837753304855941 47344384439969578744660489)
        ·
          refine ⟨35508288329977184058495367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47344384439969578744660489 35508288329977184058495367)
          ·
            refine ⟨53262432494965776087743051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35508288329977184058495367 53262432494965776087743051)
            ·
              refine ⟨79893648742448664131614577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53262432494965776087743051 79893648742448664131614577)
              ·
                refine ⟨59920236556836498098710933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79893648742448664131614577 59920236556836498098710933)
                ·
                  refine ⟨2808761088601710848377075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59920236556836498098710933 2808761088601710848377075)
                  ·
                    refine ⟨4213141632902566272565613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2808761088601710848377075 4213141632902566272565613)
                    ·
                      refine ⟨1579928112338462352212105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213141632902566272565613 1579928112338462352212105)
                      ·
                        rfl

theorem cell23_3076899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_3076899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076899 prefixEnd_3076899 := by exact prefixLift 3076899
  have htrace : WordTrace (prefixWord ++ tailWord_3076899) baseStart_3076899 baseEnd_3076899 := by
    simpa [prefixWord, tailWord_3076899, baseEnd_3076899] using wordTrace_append hprefix tailTrace_3076899
  have hstable : (prefixWord ++ tailWord_3076899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076899).length < 2 ^ (prefixWord ++ tailWord_3076899).sum := by decide
  have hdescent : baseEnd_3076899 < baseStart_3076899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076989 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_3076989 : Nat := 118140960795 + 3076989 * 2 ^ 59
def prefixEnd_3076989 : Nat := 4983230072969 + 3 ^ 40 * 3076989 * 2
def baseEnd_3076989 : Nat := 1579974325597367000086691

theorem tailTrace_3076989 : CollatzResearch.WordTrace tailWord_3076989 prefixEnd_3076989 1579974325597367000086691 := by
  unfold tailWord_3076989
  simp only [CollatzResearch.WordTrace]
  refine ⟨112227008649601835728490021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74818005766401223818993347 112227008649601835728490021)
  ·
    refine ⟨21042564121800344199091879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112227008649601835728490021 21042564121800344199091879)
    ·
      refine ⟨31563846182700516298637819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21042564121800344199091879 31563846182700516298637819)
      ·
        refine ⟨47345769274050774447956729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31563846182700516298637819 47345769274050774447956729)
        ·
          refine ⟨35509326955538080835967547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47345769274050774447956729 35509326955538080835967547)
          ·
            refine ⟨53263990433307121253951321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35509326955538080835967547 53263990433307121253951321)
            ·
              refine ⟨39947992824980340940463491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53263990433307121253951321 39947992824980340940463491)
              ·
                refine ⟨59921989237470511410695237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39947992824980340940463491 59921989237470511410695237)
                ·
                  refine ⟨11235372982025720889505357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59921989237470511410695237 11235372982025720889505357)
                  ·
                    refine ⟨4213264868259645333564509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11235372982025720889505357 4213264868259645333564509)
                    ·
                      refine ⟨1579974325597367000086691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213264868259645333564509 1579974325597367000086691)
                      ·
                        rfl

theorem cell23_3076989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_3076989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076989 prefixEnd_3076989 := by exact prefixLift 3076989
  have htrace : WordTrace (prefixWord ++ tailWord_3076989) baseStart_3076989 baseEnd_3076989 := by
    simpa [prefixWord, tailWord_3076989, baseEnd_3076989] using wordTrace_append hprefix tailTrace_3076989
  have hstable : (prefixWord ++ tailWord_3076989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076989).length < 2 ^ (prefixWord ++ tailWord_3076989).sum := by decide
  have hdescent : baseEnd_3076989 < baseStart_3076989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3076992 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 3, 7]
def baseStart_3076992 : Nat := 118140960795 + 3076992 * 2 ^ 59
def prefixEnd_3076992 : Nat := 4983230072969 + 3 ^ 40 * 3076992 * 2
def baseEnd_3076992 : Nat := 526658622013110162783059

theorem tailTrace_3076992 : CollatzResearch.WordTrace tailWord_3076992 prefixEnd_3076992 526658622013110162783059 := by
  unfold tailWord_3076992
  simp only [CollatzResearch.WordTrace]
  refine ⟨56113559034295483620424615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74818078712393978160566153 56113559034295483620424615)
  ·
    refine ⟨84170338551443225430636923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56113559034295483620424615 84170338551443225430636923)
    ·
      refine ⟨126255507827164838145955385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84170338551443225430636923 126255507827164838145955385)
      ·
        refine ⟨94691630870373628609466539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126255507827164838145955385 94691630870373628609466539)
        ·
          refine ⟨142037446305560442914199809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94691630870373628609466539 142037446305560442914199809)
          ·
            refine ⟨106528084729170332185649857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142037446305560442914199809 106528084729170332185649857)
            ·
              refine ⟨79896063546877749139237393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106528084729170332185649857 79896063546877749139237393)
              ·
                refine ⟨59922047660158311854428045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79896063546877749139237393 59922047660158311854428045)
                ·
                  refine ⟨22470767872559366945410517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59922047660158311854428045 22470767872559366945410517)
                  ·
                    refine ⟨526658622013110162783059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22470767872559366945410517 526658622013110162783059)
                    ·
                      rfl

theorem cell23_3076992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_3076992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3076992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3076992 prefixEnd_3076992 := by exact prefixLift 3076992
  have htrace : WordTrace (prefixWord ++ tailWord_3076992) baseStart_3076992 baseEnd_3076992 := by
    simpa [prefixWord, tailWord_3076992, baseEnd_3076992] using wordTrace_append hprefix tailTrace_3076992
  have hstable : (prefixWord ++ tailWord_3076992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3076992).length < 2 ^ (prefixWord ++ tailWord_3076992).sum := by decide
  have hdescent : baseEnd_3076992 < baseStart_3076992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3076992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077026 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3077026 : Nat := 118140960795 + 3077026 * 2 ^ 59
def prefixEnd_3077026 : Nat := 4983230072969 + 3 ^ 40 * 3077026 * 2
def baseEnd_3077026 : Nat := 526664441460527785108007

theorem tailTrace_3077026 : CollatzResearch.WordTrace tailWord_3077026 prefixEnd_3077026 526664441460527785108007 := by
  unfold tailWord_3077026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28057089537616947761896733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74818905433645194031724621 28057089537616947761896733)
  ·
    refine ⟨10521408576606355410711275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28057089537616947761896733 10521408576606355410711275)
    ·
      refine ⟨15782112864909533116066913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10521408576606355410711275 15782112864909533116066913)
      ·
        refine ⟨11836584648682149837050185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15782112864909533116066913 11836584648682149837050185)
        ·
          refine ⟨8877438486511612377787639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11836584648682149837050185 8877438486511612377787639)
          ·
            refine ⟨13316157729767418566681459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8877438486511612377787639 13316157729767418566681459)
            ·
              refine ⟨19974236594651127850022189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13316157729767418566681459 19974236594651127850022189)
              ·
                refine ⟨7490338722994172943758321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19974236594651127850022189 7490338722994172943758321)
                ·
                  refine ⟨5617754042245629707818741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7490338722994172943758321 5617754042245629707818741)
                  ·
                    refine ⟨526664441460527785108007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5617754042245629707818741 526664441460527785108007)
                    ·
                      rfl

theorem cell23_3077026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3077026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077026 prefixEnd_3077026 := by exact prefixLift 3077026
  have htrace : WordTrace (prefixWord ++ tailWord_3077026) baseStart_3077026 baseEnd_3077026 := by
    simpa [prefixWord, tailWord_3077026, baseEnd_3077026] using wordTrace_append hprefix tailTrace_3077026
  have hstable : (prefixWord ++ tailWord_3077026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077026).length < 2 ^ (prefixWord ++ tailWord_3077026).sum := by decide
  have hdescent : baseEnd_3077026 < baseStart_3077026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077039 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 7, 4]
def baseStart_3077039 : Nat := 118140960795 + 3077039 * 2 ^ 59
def prefixEnd_3077039 : Nat := 4983230072969 + 3 ^ 40 * 3077039 * 2
def baseEnd_3077039 : Nat := 526666666543363934820487

theorem tailTrace_3077039 : CollatzResearch.WordTrace tailWord_3077039 prefixEnd_3077039 526666666543363934820487 := by
  unfold tailWord_3077039
  simp only [CollatzResearch.WordTrace]
  refine ⟨112228832299420694267810171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74819221532947129511873447 112228832299420694267810171)
  ·
    refine ⟨168343248449131041401715257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112228832299420694267810171 168343248449131041401715257)
    ·
      refine ⟨126257436336848281051286443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168343248449131041401715257 126257436336848281051286443)
      ·
        refine ⟨189386154505272421576929665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126257436336848281051286443 189386154505272421576929665)
        ·
          refine ⟨142039615878954316182697249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189386154505272421576929665 142039615878954316182697249)
          ·
            refine ⟨106529711909215737137022937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142039615878954316182697249 106529711909215737137022937)
            ·
              refine ⟨79897283931911802852767203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106529711909215737137022937 79897283931911802852767203)
              ·
                refine ⟨119845925897867704279150805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79897283931911802852767203 119845925897867704279150805)
                ·
                  refine ⟨2808888888231274319042597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119845925897867704279150805 2808888888231274319042597)
                  ·
                    refine ⟨526666666543363934820487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2808888888231274319042597 526666666543363934820487)
                    ·
                      rfl

theorem cell23_3077039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 4].length) (baseStart_3077039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077039 prefixEnd_3077039 := by exact prefixLift 3077039
  have htrace : WordTrace (prefixWord ++ tailWord_3077039) baseStart_3077039 baseEnd_3077039 := by
    simpa [prefixWord, tailWord_3077039, baseEnd_3077039] using wordTrace_append hprefix tailTrace_3077039
  have hstable : (prefixWord ++ tailWord_3077039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077039).length < 2 ^ (prefixWord ++ tailWord_3077039).sum := by decide
  have hdescent : baseEnd_3077039 < baseStart_3077039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077079 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 3]
def baseStart_3077079 : Nat := 118140960795 + 3077079 * 2 ^ 59
def prefixEnd_3077079 : Nat := 4983230072969 + 3 ^ 40 * 3077079 * 2
def baseEnd_3077079 : Nat := 1580020538856271647961277

theorem tailTrace_3077079 : CollatzResearch.WordTrace tailWord_3077079 prefixEnd_3077079 1580020538856271647961277 := by
  unfold tailWord_3077079
  simp only [CollatzResearch.WordTrace]
  refine ⟨112230291219275781099266291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74820194146183854066177527 112230291219275781099266291)
  ·
    refine ⟨168345436828913671648899437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112230291219275781099266291 168345436828913671648899437)
    ·
      refine ⟨63129538810842626868337289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168345436828913671648899437 63129538810842626868337289)
      ·
        refine ⟨47347154108131970151252967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63129538810842626868337289 47347154108131970151252967)
        ·
          refine ⟨71020731162197955226879451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47347154108131970151252967 71020731162197955226879451)
          ·
            refine ⟨106531096743296932840319177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71020731162197955226879451 106531096743296932840319177)
            ·
              refine ⟨79898322557472699630239383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106531096743296932840319177 79898322557472699630239383)
              ·
                refine ⟨119847483836209049445359075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79898322557472699630239383 119847483836209049445359075)
                ·
                  refine ⟨179771225754313574168038613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119847483836209049445359075 179771225754313574168038613)
                  ·
                    refine ⟨4213388103616724394563405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 179771225754313574168038613 4213388103616724394563405)
                    ·
                      refine ⟨1580020538856271647961277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213388103616724394563405 1580020538856271647961277)
                      ·
                        rfl

theorem cell23_3077079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_3077079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077079 prefixEnd_3077079 := by exact prefixLift 3077079
  have htrace : WordTrace (prefixWord ++ tailWord_3077079) baseStart_3077079 baseEnd_3077079 := by
    simpa [prefixWord, tailWord_3077079, baseEnd_3077079] using wordTrace_append hprefix tailTrace_3077079
  have hstable : (prefixWord ++ tailWord_3077079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077079).length < 2 ^ (prefixWord ++ tailWord_3077079).sum := by decide
  have hdescent : baseEnd_3077079 < baseStart_3077079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077113 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 3, 1, 3]
def baseStart_3077113 : Nat := 118140960795 + 3077113 * 2 ^ 59
def prefixEnd_3077113 : Nat := 4983230072969 + 3 ^ 40 * 3077113 * 2
def baseEnd_3077113 : Nat := 1580037997198524514936121

theorem tailTrace_3077113 : CollatzResearch.WordTrace tailWord_3077113 prefixEnd_3077113 1580037997198524514936121 := by
  unfold tailWord_3077113
  simp only [CollatzResearch.WordTrace]
  refine ⟨112231531301152604906003993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74821020867435069937335995 112231531301152604906003993)
  ·
    refine ⟨84173648475864453679502995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112231531301152604906003993 84173648475864453679502995)
    ·
      refine ⟨126260472713796680519254493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84173648475864453679502995 126260472713796680519254493)
      ·
        refine ⟨47347677267673755194720435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126260472713796680519254493 47347677267673755194720435)
        ·
          refine ⟨71021515901510632792080653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47347677267673755194720435 71021515901510632792080653)
          ·
            refine ⟨26633068463066487297030245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71021515901510632792080653 26633068463066487297030245)
            ·
              refine ⟨4993700336824966368193171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26633068463066487297030245 4993700336824966368193171)
              ·
                refine ⟨7490550505237449552289757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4993700336824966368193171 7490550505237449552289757)
                ·
                  refine ⟨2808956439464043582108659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7490550505237449552289757 2808956439464043582108659)
                  ·
                    refine ⟨4213434659196065373162989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2808956439464043582108659 4213434659196065373162989)
                    ·
                      refine ⟨1580037997198524514936121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213434659196065373162989 1580037997198524514936121)
                      ·
                        rfl

theorem cell23_3077113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_3077113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077113 prefixEnd_3077113 := by exact prefixLift 3077113
  have htrace : WordTrace (prefixWord ++ tailWord_3077113) baseStart_3077113 baseEnd_3077113 := by
    simpa [prefixWord, tailWord_3077113, baseEnd_3077113] using wordTrace_append hprefix tailTrace_3077113
  have hstable : (prefixWord ++ tailWord_3077113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077113).length < 2 ^ (prefixWord ++ tailWord_3077113).sum := by decide
  have hdescent : baseEnd_3077113 < baseStart_3077113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077139 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 5]
def baseStart_3077139 : Nat := 118140960795 + 3077139 * 2 ^ 59
def prefixEnd_3077139 : Nat := 4983230072969 + 3 ^ 40 * 3077139 * 2
def baseEnd_3077139 : Nat := 1580051347695541413211001

theorem tailTrace_3077139 : CollatzResearch.WordTrace tailWord_3077139 prefixEnd_3077139 1580051347695541413211001 := by
  unfold tailWord_3077139
  simp only [CollatzResearch.WordTrace]
  refine ⟨112232479599058411346450471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74821653066038940897633647 112232479599058411346450471)
  ·
    refine ⟨168348719398587617019675707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112232479599058411346450471 168348719398587617019675707)
    ·
      refine ⟨252523079097881425529513561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168348719398587617019675707 252523079097881425529513561)
      ·
        refine ⟨189392309323411069147135171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252523079097881425529513561 189392309323411069147135171)
        ·
          refine ⟨284088463985116603720702757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189392309323411069147135171 284088463985116603720702757)
          ·
            refine ⟨53266586997209363197631767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284088463985116603720702757 53266586997209363197631767)
            ·
              refine ⟨79899880495814044796447651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53266586997209363197631767 79899880495814044796447651)
              ·
                refine ⟨119849820743721067194671477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79899880495814044796447651 119849820743721067194671477)
                ·
                  refine ⟨11235920694723850049500451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119849820743721067194671477 11235920694723850049500451)
                  ·
                    refine ⟨16853881042085775074250677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11235920694723850049500451 16853881042085775074250677)
                    ·
                      refine ⟨1580051347695541413211001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16853881042085775074250677 1580051347695541413211001)
                      ·
                        rfl

theorem cell23_3077139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_3077139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077139 prefixEnd_3077139 := by exact prefixLift 3077139
  have htrace : WordTrace (prefixWord ++ tailWord_3077139) baseStart_3077139 baseEnd_3077139 := by
    simpa [prefixWord, tailWord_3077139, baseEnd_3077139] using wordTrace_append hprefix tailTrace_3077139
  have hstable : (prefixWord ++ tailWord_3077139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077139).length < 2 ^ (prefixWord ++ tailWord_3077139).sum := by decide
  have hdescent : baseEnd_3077139 < baseStart_3077139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077146 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_3077146 : Nat := 118140960795 + 3077146 * 2 ^ 59
def prefixEnd_3077146 : Nat := 4983230072969 + 3 ^ 40 * 3077146 * 2
def baseEnd_3077146 : Nat := 526684980686707628607823

theorem tailTrace_3077146 : CollatzResearch.WordTrace tailWord_3077146 prefixEnd_3077146 526684980686707628607823 := by
  unfold tailWord_3077146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28058183727508262885488823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74821823273355367694636861 28058183727508262885488823)
  ·
    refine ⟨42087275591262394328233235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28058183727508262885488823 42087275591262394328233235)
    ·
      refine ⟨63130913386893591492349853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42087275591262394328233235 63130913386893591492349853)
      ·
        refine ⟨23674092520085096809631195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63130913386893591492349853 23674092520085096809631195)
        ·
          refine ⟨35511138780127645214446793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23674092520085096809631195 35511138780127645214446793)
          ·
            refine ⟨26633354085095733910835095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35511138780127645214446793 26633354085095733910835095)
            ·
              refine ⟨39950031127643600866252643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26633354085095733910835095 39950031127643600866252643)
              ·
                refine ⟨59925046691465401299378965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39950031127643600866252643 59925046691465401299378965)
                ·
                  refine ⟨2808986563662440685908389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59925046691465401299378965 2808986563662440685908389)
                  ·
                    refine ⟨526684980686707628607823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2808986563662440685908389 526684980686707628607823)
                    ·
                      rfl

theorem cell23_3077146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_3077146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077146 prefixEnd_3077146 := by exact prefixLift 3077146
  have htrace : WordTrace (prefixWord ++ tailWord_3077146) baseStart_3077146 baseEnd_3077146 := by
    simpa [prefixWord, tailWord_3077146, baseEnd_3077146] using wordTrace_append hprefix tailTrace_3077146
  have hstable : (prefixWord ++ tailWord_3077146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077146).length < 2 ^ (prefixWord ++ tailWord_3077146).sum := by decide
  have hdescent : baseEnd_3077146 < baseStart_3077146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077153 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_3077153 : Nat := 118140960795 + 3077153 * 2 ^ 59
def prefixEnd_3077153 : Nat := 4983230072969 + 3 ^ 40 * 3077153 * 2
def baseEnd_3077153 : Nat := 1580058536424704358435937

theorem tailTrace_3077153 : CollatzResearch.WordTrace tailWord_3077153 prefixEnd_3077153 1580058536424704358435937 := by
  unfold tailWord_3077153
  simp only [CollatzResearch.WordTrace]
  refine ⟨112232990221007691737460113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74821993480671794491640075 112232990221007691737460113)
  ·
    refine ⟨84174742665755768803095085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112232990221007691737460113 84174742665755768803095085)
    ·
      refine ⟨31565528499658413301160657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84174742665755768803095085 31565528499658413301160657)
      ·
        refine ⟨23674146374743809975870493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31565528499658413301160657 23674146374743809975870493)
        ·
          refine ⟨8877804890528928740951435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23674146374743809975870493 8877804890528928740951435)
          ·
            refine ⟨13316707335793393111427153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8877804890528928740951435 13316707335793393111427153)
            ·
              refine ⟨9987530501845044833570365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13316707335793393111427153 9987530501845044833570365)
              ·
                refine ⟨3745323938191891812588887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9987530501845044833570365 3745323938191891812588887)
                ·
                  refine ⟨5617985907287837718883331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3745323938191891812588887 5617985907287837718883331)
                  ·
                    refine ⟨8426978860931756578324997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5617985907287837718883331 8426978860931756578324997)
                    ·
                      refine ⟨1580058536424704358435937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8426978860931756578324997 1580058536424704358435937)
                      ·
                        rfl

theorem cell23_3077153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_3077153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077153 prefixEnd_3077153 := by exact prefixLift 3077153
  have htrace : WordTrace (prefixWord ++ tailWord_3077153) baseStart_3077153 baseEnd_3077153 := by
    simpa [prefixWord, tailWord_3077153, baseEnd_3077153] using wordTrace_append hprefix tailTrace_3077153
  have hstable : (prefixWord ++ tailWord_3077153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077153).length < 2 ^ (prefixWord ++ tailWord_3077153).sum := by decide
  have hdescent : baseEnd_3077153 < baseStart_3077153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077166 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3077166 : Nat := 118140960795 + 3077166 * 2 ^ 59
def prefixEnd_3077166 : Nat := 4983230072969 + 3 ^ 40 * 3077166 * 2
def baseEnd_3077166 : Nat := 1580065211673212807573377

theorem tailTrace_3077166 : CollatzResearch.WordTrace tailWord_3077166 prefixEnd_3077166 1580065211673212807573377 := by
  unfold tailWord_3077166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14029183046245074369710419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74822309579973729971788901 14029183046245074369710419)
  ·
    refine ⟨21043774569367611554565629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14029183046245074369710419 21043774569367611554565629)
    ·
      refine ⟨7891415463512854332962111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21043774569367611554565629 7891415463512854332962111)
      ·
        refine ⟨11837123195269281499443167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7891415463512854332962111 11837123195269281499443167)
        ·
          refine ⟨17755684792903922249164751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11837123195269281499443167 17755684792903922249164751)
          ·
            refine ⟨26633527189355883373747127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17755684792903922249164751 26633527189355883373747127)
            ·
              refine ⟨39950290784033825060620691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26633527189355883373747127 39950290784033825060620691)
              ·
                refine ⟨59925436176050737590931037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39950290784033825060620691 59925436176050737590931037)
                ·
                  refine ⟨22472038566019026596599139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59925436176050737590931037 22472038566019026596599139)
                  ·
                    refine ⟨33708057849028539894898709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22472038566019026596599139 33708057849028539894898709)
                    ·
                      refine ⟨1580065211673212807573377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33708057849028539894898709 1580065211673212807573377)
                      ·
                        rfl

theorem cell23_3077166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3077166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077166 prefixEnd_3077166 := by exact prefixLift 3077166
  have htrace : WordTrace (prefixWord ++ tailWord_3077166) baseStart_3077166 baseEnd_3077166 := by
    simpa [prefixWord, tailWord_3077166, baseEnd_3077166] using wordTrace_append hprefix tailTrace_3077166
  have hstable : (prefixWord ++ tailWord_3077166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077166).length < 2 ^ (prefixWord ++ tailWord_3077166).sum := by decide
  have hdescent : baseEnd_3077166 < baseStart_3077166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077176 : List Nat := [2, 1, 2, 1, 5, 2, 2, 8]
def baseStart_3077176 : Nat := 118140960795 + 3077176 * 2 ^ 59
def prefixEnd_3077176 : Nat := 4983230072969 + 3 ^ 40 * 3077176 * 2
def baseEnd_3077176 : Nat := 58521123943694732164753

theorem tailTrace_3077176 : CollatzResearch.WordTrace tailWord_3077176 prefixEnd_3077176 58521123943694732164753 := by
  unfold tailWord_3077176
  simp only [CollatzResearch.WordTrace]
  refine ⟨56116914549962183332773691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74822552733282911110364921 56116914549962183332773691)
  ·
    refine ⟨84175371824943274999160537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56116914549962183332773691 84175371824943274999160537)
    ·
      refine ⟨63131528868707456249370403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84175371824943274999160537 63131528868707456249370403)
      ·
        refine ⟨94697293303061184374055605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63131528868707456249370403 94697293303061184374055605)
        ·
          refine ⟨8877871247161986035067713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94697293303061184374055605 8877871247161986035067713)
          ·
            refine ⟨6658403435371489526300785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8877871247161986035067713 6658403435371489526300785)
            ·
              refine ⟨4993802576528617144725589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6658403435371489526300785 4993802576528617144725589)
              ·
                refine ⟨58521123943694732164753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4993802576528617144725589 58521123943694732164753)
                ·
                  rfl

theorem cell23_3077176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 8].length) (baseStart_3077176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077176 prefixEnd_3077176 := by exact prefixLift 3077176
  have htrace : WordTrace (prefixWord ++ tailWord_3077176) baseStart_3077176 baseEnd_3077176 := by
    simpa [prefixWord, tailWord_3077176, baseEnd_3077176] using wordTrace_append hprefix tailTrace_3077176
  have hstable : (prefixWord ++ tailWord_3077176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077176).length < 2 ^ (prefixWord ++ tailWord_3077176).sum := by decide
  have hdescent : baseEnd_3077176 < baseStart_3077176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077180 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 2, 4]
def baseStart_3077180 : Nat := 118140960795 + 3077180 * 2 ^ 59
def prefixEnd_3077180 : Nat := 4983230072969 + 3 ^ 40 * 3077180 * 2
def baseEnd_3077180 : Nat := 526690800134125250932771

theorem tailTrace_3077180 : CollatzResearch.WordTrace tailWord_3077180 prefixEnd_3077180 526690800134125250932771 := by
  unfold tailWord_3077180
  simp only [CollatzResearch.WordTrace]
  refine ⟨56116987495954937674346497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74822649994606583565795329 56116987495954937674346497)
  ·
    refine ⟨42087740621966203255759873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56116987495954937674346497 42087740621966203255759873)
    ·
      refine ⟨31565805466474652441819905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42087740621966203255759873 31565805466474652441819905)
      ·
        refine ⟨23674354099855989331364929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31565805466474652441819905 23674354099855989331364929)
        ·
          refine ⟨17755765574891991998523697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23674354099855989331364929 17755765574891991998523697)
          ·
            refine ⟨13316824181168993998892773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17755765574891991998523697 13316824181168993998892773)
            ·
              refine ⟨2496904533969186374792395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13316824181168993998892773 2496904533969186374792395)
              ·
                refine ⟨3745356800953779562188593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496904533969186374792395 3745356800953779562188593)
                ·
                  refine ⟨2809017600715334671641445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3745356800953779562188593 2809017600715334671641445)
                  ·
                    refine ⟨526690800134125250932771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2809017600715334671641445 526690800134125250932771)
                    ·
                      rfl

theorem cell23_3077180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_3077180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077180 prefixEnd_3077180 := by exact prefixLift 3077180
  have htrace : WordTrace (prefixWord ++ tailWord_3077180) baseStart_3077180 baseEnd_3077180 := by
    simpa [prefixWord, tailWord_3077180, baseEnd_3077180] using wordTrace_append hprefix tailTrace_3077180
  have hstable : (prefixWord ++ tailWord_3077180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077180).length < 2 ^ (prefixWord ++ tailWord_3077180).sum := by decide
  have hdescent : baseEnd_3077180 < baseStart_3077180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077214 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3077214 : Nat := 118140960795 + 3077214 * 2 ^ 59
def prefixEnd_3077214 : Nat := 4983230072969 + 3 ^ 40 * 3077214 * 2
def baseEnd_3077214 : Nat := 526696619581542873257719

theorem tailTrace_3077214 : CollatzResearch.WordTrace tailWord_3077214 prefixEnd_3077214 526696619581542873257719 := by
  unfold tailWord_3077214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14029401884223337394428837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74823476715857799436953797 14029401884223337394428837)
  ·
    refine ⟨2630512853291875761455407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14029401884223337394428837 2630512853291875761455407)
    ·
      refine ⟨3945769279937813642183111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2630512853291875761455407 3945769279937813642183111)
      ·
        refine ⟨5918653919906720463274667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945769279937813642183111 5918653919906720463274667)
        ·
          refine ⟨8877980879860080694912001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5918653919906720463274667 8877980879860080694912001)
          ·
            refine ⟨6658485659895060521184001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8877980879860080694912001 6658485659895060521184001)
            ·
              refine ⟨4993864244921295390888001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6658485659895060521184001 4993864244921295390888001)
              ·
                refine ⟨3745398183690971543166001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4993864244921295390888001 3745398183690971543166001)
                ·
                  refine ⟨2809048637768228657374501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3745398183690971543166001 2809048637768228657374501)
                  ·
                    refine ⟨526696619581542873257719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2809048637768228657374501 526696619581542873257719)
                    ·
                      rfl

theorem cell23_3077214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3077214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077214 prefixEnd_3077214 := by exact prefixLift 3077214
  have htrace : WordTrace (prefixWord ++ tailWord_3077214) baseStart_3077214 baseEnd_3077214 := by
    simpa [prefixWord, tailWord_3077214, baseEnd_3077214] using wordTrace_append hprefix tailTrace_3077214
  have hstable : (prefixWord ++ tailWord_3077214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077214).length < 2 ^ (prefixWord ++ tailWord_3077214).sum := by decide
  have hdescent : baseEnd_3077214 < baseStart_3077214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077230 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_3077230 : Nat := 118140960795 + 3077230 * 2 ^ 59
def prefixEnd_3077230 : Nat := 4983230072969 + 3 ^ 40 * 3077230 * 2
def baseEnd_3077230 : Nat := 1580098074435100557173083

theorem tailTrace_3077230 : CollatzResearch.WordTrace tailWord_3077230 prefixEnd_3077230 1580098074435100557173083 := by
  unfold tailWord_3077230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14029474830216091736001643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74823865761152489258675429 14029474830216091736001643)
  ·
    refine ⟨21044212245324137604002465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14029474830216091736001643 21044212245324137604002465)
    ·
      refine ⟨15783159183993103203001849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21044212245324137604002465 15783159183993103203001849)
      ·
        refine ⟨11837369387994827402251387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15783159183993103203001849 11837369387994827402251387)
        ·
          refine ⟨17756054081992241103377081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11837369387994827402251387 17756054081992241103377081)
          ·
            refine ⟨13317040561494180827532811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17756054081992241103377081 13317040561494180827532811)
            ·
              refine ⟨19975560842241271241299217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13317040561494180827532811 19975560842241271241299217)
              ·
                refine ⟨14981670631680953430974413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19975560842241271241299217 14981670631680953430974413)
                ·
                  refine ⟨5618126486880357536615405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14981670631680953430974413 5618126486880357536615405)
                  ·
                    refine ⟨2106797432580134076230777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5618126486880357536615405 2106797432580134076230777)
                    ·
                      refine ⟨1580098074435100557173083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2106797432580134076230777 1580098074435100557173083)
                      ·
                        rfl

theorem cell23_3077230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_3077230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077230 prefixEnd_3077230 := by exact prefixLift 3077230
  have htrace : WordTrace (prefixWord ++ tailWord_3077230) baseStart_3077230 baseEnd_3077230 := by
    simpa [prefixWord, tailWord_3077230, baseEnd_3077230] using wordTrace_append hprefix tailTrace_3077230
  have hstable : (prefixWord ++ tailWord_3077230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077230).length < 2 ^ (prefixWord ++ tailWord_3077230).sum := by decide
  have hdescent : baseEnd_3077230 < baseStart_3077230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077237 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3077237 : Nat := 118140960795 + 3077237 * 2 ^ 59
def prefixEnd_3077237 : Nat := 4983230072969 + 3 ^ 40 * 3077237 * 2
def baseEnd_3077237 : Nat := 1580101668799682029785551

theorem tailTrace_3077237 : CollatzResearch.WordTrace tailWord_3077237 prefixEnd_3077237 1580101668799682029785551 := by
  unfold tailWord_3077237
  simp only [CollatzResearch.WordTrace]
  refine ⟨112236053952703374083517965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74824035968468916055678643 112236053952703374083517965)
  ·
    refine ⟨42088520232263765281319237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112236053952703374083517965 42088520232263765281319237)
    ·
      refine ⟨7891597543549455990247357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42088520232263765281319237 7891597543549455990247357)
      ·
        refine ⟨2959349078831045996342759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7891597543549455990247357 2959349078831045996342759)
        ·
          refine ⟨4439023618246568994514139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2959349078831045996342759 4439023618246568994514139)
          ·
            refine ⟨6658535427369853491771209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4439023618246568994514139 6658535427369853491771209)
            ·
              refine ⟨4993901570527390118828407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6658535427369853491771209 4993901570527390118828407)
              ·
                refine ⟨7490852355791085178242611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4993901570527390118828407 7490852355791085178242611)
                ·
                  refine ⟨11236278533686627767363917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7490852355791085178242611 11236278533686627767363917)
                  ·
                    refine ⟨4213604450132485412761469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11236278533686627767363917 4213604450132485412761469)
                    ·
                      refine ⟨1580101668799682029785551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213604450132485412761469 1580101668799682029785551)
                      ·
                        rfl

theorem cell23_3077237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3077237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077237 prefixEnd_3077237 := by exact prefixLift 3077237
  have htrace : WordTrace (prefixWord ++ tailWord_3077237) baseStart_3077237 baseEnd_3077237 := by
    simpa [prefixWord, tailWord_3077237, baseEnd_3077237] using wordTrace_append hprefix tailTrace_3077237
  have hstable : (prefixWord ++ tailWord_3077237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077237).length < 2 ^ (prefixWord ++ tailWord_3077237).sum := by decide
  have hdescent : baseEnd_3077237 < baseStart_3077237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077290 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3077290 : Nat := 118140960795 + 3077290 * 2 ^ 59
def prefixEnd_3077290 : Nat := 4983230072969 + 3 ^ 40 * 3077290 * 2
def baseEnd_3077290 : Nat := 1580128883274370322422807

theorem tailTrace_3077290 : CollatzResearch.WordTrace tailWord_3077290 prefixEnd_3077290 1580128883274370322422807 := by
  unfold tailWord_3077290
  simp only [CollatzResearch.WordTrace]
  refine ⟨28059496755377841033799331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74825324681007576090131549 28059496755377841033799331)
  ·
    refine ⟨42089245133066761550698997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28059496755377841033799331 42089245133066761550698997)
    ·
      refine ⟨3945866731225008895378031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42089245133066761550698997 3945866731225008895378031)
      ·
        refine ⟨5918800096837513343067047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945866731225008895378031 5918800096837513343067047)
        ·
          refine ⟨8878200145256270014600571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5918800096837513343067047 8878200145256270014600571)
          ·
            refine ⟨13317300217884405021900857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8878200145256270014600571 13317300217884405021900857)
            ·
              refine ⟨9987975163413303766425643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13317300217884405021900857 9987975163413303766425643)
              ·
                refine ⟨14981962745119955649638465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9987975163413303766425643 14981962745119955649638465)
                ·
                  refine ⟨11236472058839966737228849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14981962745119955649638465 11236472058839966737228849)
                  ·
                    refine ⟨8427354044129975052921637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11236472058839966737228849 8427354044129975052921637)
                    ·
                      refine ⟨1580128883274370322422807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8427354044129975052921637 1580128883274370322422807)
                      ·
                        rfl

theorem cell23_3077290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3077290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077290 prefixEnd_3077290 := by exact prefixLift 3077290
  have htrace : WordTrace (prefixWord ++ tailWord_3077290) baseStart_3077290 baseEnd_3077290 := by
    simpa [prefixWord, tailWord_3077290, baseEnd_3077290] using wordTrace_append hprefix tailTrace_3077290
  have hstable : (prefixWord ++ tailWord_3077290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077290).length < 2 ^ (prefixWord ++ tailWord_3077290).sum := by decide
  have hdescent : baseEnd_3077290 < baseStart_3077290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077296 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 4, 5]
def baseStart_3077296 : Nat := 118140960795 + 3077296 * 2 ^ 59
def prefixEnd_3077296 : Nat := 4983230072969 + 3 ^ 40 * 3077296 * 2
def baseEnd_3077296 : Nat := 526710654719432432982593

theorem tailTrace_3077296 : CollatzResearch.WordTrace tailWord_3077296 prefixEnd_3077296 526710654719432432982593 := by
  unfold tailWord_3077296
  simp only [CollatzResearch.WordTrace]
  refine ⟨56119102929744813579957871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74825470572993084773277161 56119102929744813579957871)
  ·
    refine ⟨84178654394617220369936807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56119102929744813579957871 84178654394617220369936807)
    ·
      refine ⟨126267981591925830554905211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84178654394617220369936807 126267981591925830554905211)
      ·
        refine ⟨189401972387888745832357817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126267981591925830554905211 189401972387888745832357817)
        ·
          refine ⟨142051479290916559374268363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189401972387888745832357817 142051479290916559374268363)
          ·
            refine ⟨213077218936374839061402545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142051479290916559374268363 213077218936374839061402545)
            ·
              refine ⟨159807914202281129296051909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213077218936374839061402545 159807914202281129296051909)
              ·
                refine ⟨29963983912927711743009733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159807914202281129296051909 29963983912927711743009733)
                ·
                  refine ⟨5618246983673945951814325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29963983912927711743009733 5618246983673945951814325)
                  ·
                    refine ⟨526710654719432432982593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5618246983673945951814325 526710654719432432982593)
                    ·
                      rfl

theorem cell23_3077296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_3077296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077296 prefixEnd_3077296 := by exact prefixLift 3077296
  have htrace : WordTrace (prefixWord ++ tailWord_3077296) baseStart_3077296 baseEnd_3077296 := by
    simpa [prefixWord, tailWord_3077296, baseEnd_3077296] using wordTrace_append hprefix tailTrace_3077296
  have hstable : (prefixWord ++ tailWord_3077296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077296).length < 2 ^ (prefixWord ++ tailWord_3077296).sum := by decide
  have hdescent : baseEnd_3077296 < baseStart_3077296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077306 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_3077306 : Nat := 118140960795 + 3077306 * 2 ^ 59
def prefixEnd_3077306 : Nat := 4983230072969 + 3 ^ 40 * 3077306 * 2
def baseEnd_3077306 : Nat := 1580137098964842259822733

theorem tailTrace_3077306 : CollatzResearch.WordTrace tailWord_3077306 prefixEnd_3077306 1580137098964842259822733 := by
  unfold tailWord_3077306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28059642647363349716944943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74825713726302265911853181 28059642647363349716944943)
  ·
    refine ⟨42089463971045024575417415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28059642647363349716944943 42089463971045024575417415)
    ·
      refine ⟨63134195956567536863126123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42089463971045024575417415 63134195956567536863126123)
      ·
        refine ⟨94701293934851305294689185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63134195956567536863126123 94701293934851305294689185)
        ·
          refine ⟨71025970451138478971016889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94701293934851305294689185 71025970451138478971016889)
          ·
            refine ⟨53269477838353859228262667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71025970451138478971016889 53269477838353859228262667)
            ·
              refine ⟨79904216757530788842394001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53269477838353859228262667 79904216757530788842394001)
              ·
                refine ⟨59928162568148091631795501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79904216757530788842394001 59928162568148091631795501)
                ·
                  refine ⟨22473060963055534361923313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59928162568148091631795501 22473060963055534361923313)
                  ·
                    refine ⟨16854795722291650771442485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22473060963055534361923313 16854795722291650771442485)
                    ·
                      refine ⟨1580137098964842259822733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16854795722291650771442485 1580137098964842259822733)
                      ·
                        rfl

theorem cell23_3077306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_3077306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077306 prefixEnd_3077306 := by exact prefixLift 3077306
  have htrace : WordTrace (prefixWord ++ tailWord_3077306) baseStart_3077306 baseEnd_3077306 := by
    simpa [prefixWord, tailWord_3077306, baseEnd_3077306] using wordTrace_append hprefix tailTrace_3077306
  have hstable : (prefixWord ++ tailWord_3077306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077306).length < 2 ^ (prefixWord ++ tailWord_3077306).sum := by decide
  have hdescent : baseEnd_3077306 < baseStart_3077306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077334 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_3077334 : Nat := 118140960795 + 3077334 * 2 ^ 59
def prefixEnd_3077334 : Nat := 4983230072969 + 3 ^ 40 * 3077334 * 2
def baseEnd_3077334 : Nat := 175572386269240905585845

theorem tailTrace_3077334 : CollatzResearch.WordTrace tailWord_3077334 prefixEnd_3077334 175572386269240905585845 := by
  unfold tailWord_3077334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7014974489584497478112441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74826394555567973099866037 7014974489584497478112441)
  ·
    refine ⟨5261230867188373108584331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7014974489584497478112441 5261230867188373108584331)
    ·
      refine ⟨7891846300782559662876497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5261230867188373108584331 7891846300782559662876497)
      ·
        refine ⟨5918884725586919747157373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7891846300782559662876497 5918884725586919747157373)
        ·
          refine ⟨2219581772095094905184015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5918884725586919747157373 2219581772095094905184015)
          ·
            refine ⟨3329372658142642357776023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219581772095094905184015 3329372658142642357776023)
            ·
              refine ⟨4994058987213963536664035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3329372658142642357776023 4994058987213963536664035)
              ·
                refine ⟨7491088480820945304996053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4994058987213963536664035 7491088480820945304996053)
                ·
                  refine ⟨175572386269240905585845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7491088480820945304996053 175572386269240905585845)
                  ·
                    rfl

theorem cell23_3077334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_3077334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077334 prefixEnd_3077334 := by exact prefixLift 3077334
  have htrace : WordTrace (prefixWord ++ tailWord_3077334) baseStart_3077334 baseEnd_3077334 := by
    simpa [prefixWord, tailWord_3077334, baseEnd_3077334] using wordTrace_append hprefix tailTrace_3077334
  have hstable : (prefixWord ++ tailWord_3077334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077334).length < 2 ^ (prefixWord ++ tailWord_3077334).sum := by decide
  have hdescent : baseEnd_3077334 < baseStart_3077334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077370 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3]
def baseStart_3077370 : Nat := 118140960795 + 3077370 * 2 ^ 59
def prefixEnd_3077370 : Nat := 4983230072969 + 3 ^ 40 * 3077370 * 2
def baseEnd_3077370 : Nat := 1580169961726730009422439

theorem tailTrace_3077370 : CollatzResearch.WordTrace tailWord_3077370 prefixEnd_3077370 1580169961726730009422439 := by
  unfold tailWord_3077370
  simp only [CollatzResearch.WordTrace]
  refine ⟨28060226215305384449527391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74827269907481025198739709 28060226215305384449527391)
  ·
    refine ⟨42090339322958076674291087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28060226215305384449527391 42090339322958076674291087)
    ·
      refine ⟨63135508984437115011436631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42090339322958076674291087 63135508984437115011436631)
      ·
        refine ⟨94703263476655672517154947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63135508984437115011436631 94703263476655672517154947)
        ·
          refine ⟨142054895214983508775732421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94703263476655672517154947 142054895214983508775732421)
          ·
            refine ⟨26635292852809407895449829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142054895214983508775732421 26635292852809407895449829)
            ·
              refine ⟨4994117409901763980396843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26635292852809407895449829 4994117409901763980396843)
              ·
                refine ⟨7491176114852645970595265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4994117409901763980396843 7491176114852645970595265)
                ·
                  refine ⟨5618382086139484477946449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7491176114852645970595265 5618382086139484477946449)
                  ·
                    refine ⟨4213786564604613358459837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5618382086139484477946449 4213786564604613358459837)
                    ·
                      refine ⟨1580169961726730009422439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213786564604613358459837 1580169961726730009422439)
                      ·
                        rfl

theorem cell23_3077370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_3077370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077370 prefixEnd_3077370 := by exact prefixLift 3077370
  have htrace : WordTrace (prefixWord ++ tailWord_3077370) baseStart_3077370 baseEnd_3077370 := by
    simpa [prefixWord, tailWord_3077370, baseEnd_3077370] using wordTrace_append hprefix tailTrace_3077370
  have hstable : (prefixWord ++ tailWord_3077370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077370).length < 2 ^ (prefixWord ++ tailWord_3077370).sum := by decide
  have hdescent : baseEnd_3077370 < baseStart_3077370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077376 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_3077376 : Nat := 118140960795 + 3077376 * 2 ^ 59
def prefixEnd_3077376 : Nat := 4983230072969 + 3 ^ 40 * 3077376 * 2
def baseEnd_3077376 : Nat := 1580173042610656985947411

theorem tailTrace_3077376 : CollatzResearch.WordTrace tailWord_3077376 prefixEnd_3077376 1580173042610656985947411 := by
  unfold tailWord_3077376
  simp only [CollatzResearch.WordTrace]
  refine ⟨56120561849599900411413991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74827415799466533881885321 56120561849599900411413991)
  ·
    refine ⟨84180842774399850617120987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56120561849599900411413991 84180842774399850617120987)
    ·
      refine ⟨126271264161599775925681481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84180842774399850617120987 126271264161599775925681481)
      ·
        refine ⟨94703448121199831944261111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126271264161599775925681481 94703448121199831944261111)
        ·
          refine ⟨142055172181799747916391667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94703448121199831944261111 142055172181799747916391667)
          ·
            refine ⟨213082758272699621874587501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142055172181799747916391667 213082758272699621874587501)
            ·
              refine ⟨79906034352262358202970313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213082758272699621874587501 79906034352262358202970313)
              ·
                refine ⟨59929525764196768652227735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79906034352262358202970313 59929525764196768652227735)
                ·
                  refine ⟨89894288646295152978341603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59929525764196768652227735 89894288646295152978341603)
                  ·
                    refine ⟨134841432969442729467512405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89894288646295152978341603 134841432969442729467512405)
                    ·
                      refine ⟨1580173042610656985947411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 134841432969442729467512405 1580173042610656985947411)
                      ·
                        rfl

theorem cell23_3077376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_3077376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077376 prefixEnd_3077376 := by exact prefixLift 3077376
  have htrace : WordTrace (prefixWord ++ tailWord_3077376) baseStart_3077376 baseEnd_3077376 := by
    simpa [prefixWord, tailWord_3077376, baseEnd_3077376] using wordTrace_append hprefix tailTrace_3077376
  have hstable : (prefixWord ++ tailWord_3077376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077376).length < 2 ^ (prefixWord ++ tailWord_3077376).sum := by decide
  have hdescent : baseEnd_3077376 < baseStart_3077376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077390 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_3077390 : Nat := 118140960795 + 3077390 * 2 ^ 59
def prefixEnd_3077390 : Nat := 4983230072969 + 3 ^ 40 * 3077390 * 2
def baseEnd_3077390 : Nat := 175575581259979992352483

theorem tailTrace_3077390 : CollatzResearch.WordTrace tailWord_3077390 prefixEnd_3077390 175575581259979992352483 := by
  unfold tailWord_3077390
  simp only [CollatzResearch.WordTrace]
  refine ⟨14030204290143635151729703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74827756214099387475891749 14030204290143635151729703)
  ·
    refine ⟨21045306435215452727594555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14030204290143635151729703 21045306435215452727594555)
    ·
      refine ⟨31567959652823179091391833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21045306435215452727594555 31567959652823179091391833)
      ·
        refine ⟨23675969739617384318543875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31567959652823179091391833 23675969739617384318543875)
        ·
          refine ⟨35513954609426076477815813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23675969739617384318543875 35513954609426076477815813)
          ·
            refine ⟨6658866489267389339590465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35513954609426076477815813 6658866489267389339590465)
            ·
              refine ⟨4994149866950542004692849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6658866489267389339590465 4994149866950542004692849)
              ·
                refine ⟨3745612400212906503519637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4994149866950542004692849 3745612400212906503519637)
                ·
                  refine ⟨175575581259979992352483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3745612400212906503519637 175575581259979992352483)
                  ·
                    rfl

theorem cell23_3077390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_3077390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077390 prefixEnd_3077390 := by exact prefixLift 3077390
  have htrace : WordTrace (prefixWord ++ tailWord_3077390) baseStart_3077390 baseEnd_3077390 := by
    simpa [prefixWord, tailWord_3077390, baseEnd_3077390] using wordTrace_append hprefix tailTrace_3077390
  have hstable : (prefixWord ++ tailWord_3077390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077390).length < 2 ^ (prefixWord ++ tailWord_3077390).sum := by decide
  have hdescent : baseEnd_3077390 < baseStart_3077390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077427 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 2, 3, 2]
def baseStart_3077427 : Nat := 118140960795 + 3077427 * 2 ^ 59
def prefixEnd_3077427 : Nat := 4983230072969 + 3 ^ 40 * 3077427 * 2
def baseEnd_3077427 : Nat := 1580199230124036286409677

theorem tailTrace_3077427 : CollatzResearch.WordTrace tailWord_3077427 prefixEnd_3077427 1580199230124036286409677 := by
  unfold tailWord_3077427
  simp only [CollatzResearch.WordTrace]
  refine ⟨112242983822015036532934535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74828655881343357688623023 112242983822015036532934535)
  ·
    refine ⟨168364475733022554799401803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112242983822015036532934535 168364475733022554799401803)
    ·
      refine ⟨252546713599533832199102705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168364475733022554799401803 252546713599533832199102705)
      ·
        refine ⟨189410035199650374149327029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252546713599533832199102705 189410035199650374149327029)
        ·
          refine ⟨17757190799967222576499409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189410035199650374149327029 17757190799967222576499409)
          ·
            refine ⟨13317893099975416932374557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17757190799967222576499409 13317893099975416932374557)
            ·
              refine ⟨4994209912490781349640459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13317893099975416932374557 4994209912490781349640459)
              ·
                refine ⟨7491314868736172024460689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4994209912490781349640459 7491314868736172024460689)
                ·
                  refine ⟨5618486151552129018345517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7491314868736172024460689 5618486151552129018345517)
                  ·
                    refine ⟨2106932306832048381879569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5618486151552129018345517 2106932306832048381879569)
                    ·
                      refine ⟨1580199230124036286409677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2106932306832048381879569 1580199230124036286409677)
                      ·
                        rfl

theorem cell23_3077427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 3, 2].length) (baseStart_3077427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077427 prefixEnd_3077427 := by exact prefixLift 3077427
  have htrace : WordTrace (prefixWord ++ tailWord_3077427) baseStart_3077427 baseEnd_3077427 := by
    simpa [prefixWord, tailWord_3077427, baseEnd_3077427] using wordTrace_append hprefix tailTrace_3077427
  have hstable : (prefixWord ++ tailWord_3077427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077427).length < 2 ^ (prefixWord ++ tailWord_3077427).sum := by decide
  have hdescent : baseEnd_3077427 < baseStart_3077427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077434 : List Nat := [3, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3]
def baseStart_3077434 : Nat := 118140960795 + 3077434 * 2 ^ 59
def prefixEnd_3077434 : Nat := 4983230072969 + 3 ^ 40 * 3077434 * 2
def baseEnd_3077434 : Nat := 1580202824488617759022145

theorem tailTrace_3077434 : CollatzResearch.WordTrace tailWord_3077434 prefixEnd_3077434 1580202824488617759022145 := by
  unfold tailWord_3077434
  simp only [CollatzResearch.WordTrace]
  refine ⟨28060809783247419182109839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74828826088659784485626237 28060809783247419182109839)
  ·
    refine ⟨42091214674871128773164759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28060809783247419182109839 42091214674871128773164759)
    ·
      refine ⟨63136822012306693159747139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42091214674871128773164759 63136822012306693159747139)
      ·
        refine ⟨94705233018460039739620709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63136822012306693159747139 94705233018460039739620709)
        ·
          refine ⟨17757231190961257451178883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94705233018460039739620709 17757231190961257451178883)
          ·
            refine ⟨26635846786441886176768325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17757231190961257451178883 26635846786441886176768325)
            ·
              refine ⟨4994221272457853658144061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26635846786441886176768325 4994221272457853658144061)
              ·
                refine ⟨1872832977171695121804023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4994221272457853658144061 1872832977171695121804023)
                ·
                  refine ⟨2809249465757542682706035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872832977171695121804023 2809249465757542682706035)
                  ·
                    refine ⟨4213874198636314024059053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2809249465757542682706035 4213874198636314024059053)
                    ·
                      refine ⟨1580202824488617759022145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213874198636314024059053 1580202824488617759022145)
                      ·
                        rfl

theorem cell23_3077434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3].length) (baseStart_3077434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077434 prefixEnd_3077434 := by exact prefixLift 3077434
  have htrace : WordTrace (prefixWord ++ tailWord_3077434) baseStart_3077434 baseEnd_3077434 := by
    simpa [prefixWord, tailWord_3077434, baseEnd_3077434] using wordTrace_append hprefix tailTrace_3077434
  have hstable : (prefixWord ++ tailWord_3077434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077434).length < 2 ^ (prefixWord ++ tailWord_3077434).sum := by decide
  have hdescent : baseEnd_3077434 < baseStart_3077434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077440 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 4]
def baseStart_3077440 : Nat := 118140960795 + 3077440 * 2 ^ 59
def prefixEnd_3077440 : Nat := 4983230072969 + 3 ^ 40 * 3077440 * 2
def baseEnd_3077440 : Nat := 1580205905372544735547117

theorem tailTrace_3077440 : CollatzResearch.WordTrace tailWord_3077440 prefixEnd_3077440 1580205905372544735547117 := by
  unfold tailWord_3077440
  simp only [CollatzResearch.WordTrace]
  refine ⟨56121728985483969876578887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74828971980645293168771849 56121728985483969876578887)
  ·
    refine ⟨84182593478225954814868331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56121728985483969876578887 84182593478225954814868331)
    ·
      refine ⟨126273890217338932222302497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84182593478225954814868331 126273890217338932222302497)
      ·
        refine ⟨94705417663004199166726873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126273890217338932222302497 94705417663004199166726873)
        ·
          refine ⟨71029063247253149375045155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94705417663004199166726873 71029063247253149375045155)
          ·
            refine ⟨106543594870879724062567733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71029063247253149375045155 106543594870879724062567733)
            ·
              refine ⟨9988462019144974130865725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106543594870879724062567733 9988462019144974130865725)
              ·
                refine ⟨3745673257179365299074647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9988462019144974130865725 3745673257179365299074647)
                ·
                  refine ⟨5618509885769047948611971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3745673257179365299074647 5618509885769047948611971)
                  ·
                    refine ⟨8427764828653571922917957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5618509885769047948611971 8427764828653571922917957)
                    ·
                      refine ⟨1580205905372544735547117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8427764828653571922917957 1580205905372544735547117)
                      ·
                        rfl

theorem cell23_3077440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_3077440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077440 prefixEnd_3077440 := by exact prefixLift 3077440
  have htrace : WordTrace (prefixWord ++ tailWord_3077440) baseStart_3077440 baseEnd_3077440 := by
    simpa [prefixWord, tailWord_3077440, baseEnd_3077440] using wordTrace_append hprefix tailTrace_3077440
  have hstable : (prefixWord ++ tailWord_3077440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077440).length < 2 ^ (prefixWord ++ tailWord_3077440).sum := by decide
  have hdescent : baseEnd_3077440 < baseStart_3077440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077443 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 5]
def baseStart_3077443 : Nat := 118140960795 + 3077443 * 2 ^ 59
def prefixEnd_3077443 : Nat := 4983230072969 + 3 ^ 40 * 3077443 * 2
def baseEnd_3077443 : Nat := 1580207445814508223809603

theorem tailTrace_3077443 : CollatzResearch.WordTrace tailWord_3077443 prefixEnd_3077443 1580207445814508223809603 := by
  unfold tailWord_3077443
  simp only [CollatzResearch.WordTrace]
  refine ⟨112243567389957071265516983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74829044926638047510344655 112243567389957071265516983)
  ·
    refine ⟨168365351084935606898275475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112243567389957071265516983 168365351084935606898275475)
    ·
      refine ⟨252548026627403410347413213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168365351084935606898275475 252548026627403410347413213)
      ·
        refine ⟨94705509985276278880279955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252548026627403410347413213 94705509985276278880279955)
        ·
          refine ⟨142058264977914418320419933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94705509985276278880279955 142058264977914418320419933)
          ·
            refine ⟨53271849366717906870157475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142058264977914418320419933 53271849366717906870157475)
            ·
              refine ⟨79907774050076860305236213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53271849366717906870157475 79907774050076860305236213)
              ·
                refine ⟨7491353817194705653615895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79907774050076860305236213 7491353817194705653615895)
                ·
                  refine ⟨11237030725792058480423843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7491353817194705653615895 11237030725792058480423843)
                  ·
                    refine ⟨16855546088688087720635765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11237030725792058480423843 16855546088688087720635765)
                    ·
                      refine ⟨1580207445814508223809603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16855546088688087720635765 1580207445814508223809603)
                      ·
                        rfl

theorem cell23_3077443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_3077443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077443 prefixEnd_3077443 := by exact prefixLift 3077443
  have htrace : WordTrace (prefixWord ++ tailWord_3077443) baseStart_3077443 baseEnd_3077443 := by
    simpa [prefixWord, tailWord_3077443, baseEnd_3077443] using wordTrace_append hprefix tailTrace_3077443
  have hstable : (prefixWord ++ tailWord_3077443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077443).length < 2 ^ (prefixWord ++ tailWord_3077443).sum := by decide
  have hdescent : baseEnd_3077443 < baseStart_3077443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077460 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_3077460 : Nat := 118140960795 + 3077460 * 2 ^ 59
def prefixEnd_3077460 : Nat := 4983230072969 + 3 ^ 40 * 3077460 * 2
def baseEnd_3077460 : Nat := 1580216174985634657297025

theorem tailTrace_3077460 : CollatzResearch.WordTrace tailWord_3077460 prefixEnd_3077460 1580216174985634657297025 := by
  unfold tailWord_3077460
  simp only [CollatzResearch.WordTrace]
  refine ⟨56122093715447741584442917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74829458287263655445923889 56122093715447741584442917)
  ·
    refine ⟨10522892571646451547083047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56122093715447741584442917 10522892571646451547083047)
    ·
      refine ⟨15784338857469677320624571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10522892571646451547083047 15784338857469677320624571)
      ·
        refine ⟨23676508286204515980936857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15784338857469677320624571 23676508286204515980936857)
        ·
          refine ⟨17757381214653386985702643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23676508286204515980936857 17757381214653386985702643)
          ·
            refine ⟨26636071821980080478553965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17757381214653386985702643 26636071821980080478553965)
            ·
              refine ⟨9988526933242530179457737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26636071821980080478553965 9988526933242530179457737)
              ·
                refine ⟨7491395199931897634593303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9988526933242530179457737 7491395199931897634593303)
                ·
                  refine ⟨11237092799897846451889955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7491395199931897634593303 11237092799897846451889955)
                  ·
                    refine ⟨16855639199846769677834933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11237092799897846451889955 16855639199846769677834933)
                    ·
                      refine ⟨1580216174985634657297025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16855639199846769677834933 1580216174985634657297025)
                      ·
                        rfl

theorem cell23_3077460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_3077460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077460 prefixEnd_3077460 := by exact prefixLift 3077460
  have htrace : WordTrace (prefixWord ++ tailWord_3077460) baseStart_3077460 baseEnd_3077460 := by
    simpa [prefixWord, tailWord_3077460, baseEnd_3077460] using wordTrace_append hprefix tailTrace_3077460
  have hstable : (prefixWord ++ tailWord_3077460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077460).length < 2 ^ (prefixWord ++ tailWord_3077460).sum := by decide
  have hdescent : baseEnd_3077460 < baseStart_3077460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077474 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_3077474 : Nat := 118140960795 + 3077474 * 2 ^ 59
def prefixEnd_3077474 : Nat := 4983230072969 + 3 ^ 40 * 3077474 * 2
def baseEnd_3077474 : Nat := 1580223363714797602521961

theorem tailTrace_3077474 : CollatzResearch.WordTrace tailWord_3077474 prefixEnd_3077474 1580223363714797602521961 := by
  unfold tailWord_3077474
  simp only [CollatzResearch.WordTrace]
  refine ⟨28061174513211190889973869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74829798701896509039930317 28061174513211190889973869)
  ·
    refine ⟨10522940442454196583740201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28061174513211190889973869 10522940442454196583740201)
    ·
      refine ⟨7892205331840647437805151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10522940442454196583740201 7892205331840647437805151)
      ·
        refine ⟨11838307997760971156707727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7892205331840647437805151 11838307997760971156707727)
        ·
          refine ⟨17757461996641456735061591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11838307997760971156707727 17757461996641456735061591)
          ·
            refine ⟨26636192994962185102592387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17757461996641456735061591 26636192994962185102592387)
            ·
              refine ⟨39954289492443277653888581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26636192994962185102592387 39954289492443277653888581)
              ·
                refine ⟨7491429279833114560104109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39954289492443277653888581 7491429279833114560104109)
                ·
                  refine ⟨2809285979937417960039041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7491429279833114560104109 2809285979937417960039041)
                  ·
                    refine ⟨2106964484953063470029281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2809285979937417960039041 2106964484953063470029281)
                    ·
                      refine ⟨1580223363714797602521961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2106964484953063470029281 1580223363714797602521961)
                      ·
                        rfl

theorem cell23_3077474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_3077474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077474 prefixEnd_3077474 := by exact prefixLift 3077474
  have htrace : WordTrace (prefixWord ++ tailWord_3077474) baseStart_3077474 baseEnd_3077474 := by
    simpa [prefixWord, tailWord_3077474, baseEnd_3077474] using wordTrace_append hprefix tailTrace_3077474
  have hstable : (prefixWord ++ tailWord_3077474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077474).length < 2 ^ (prefixWord ++ tailWord_3077474).sum := by decide
  have hdescent : baseEnd_3077474 < baseStart_3077474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077477 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 1, 2, 3]
def baseStart_3077477 : Nat := 118140960795 + 3077477 * 2 ^ 59
def prefixEnd_3077477 : Nat := 4983230072969 + 3 ^ 40 * 3077477 * 2
def baseEnd_3077477 : Nat := 1580224904156761090784447

theorem tailTrace_3077477 : CollatzResearch.WordTrace tailWord_3077477 prefixEnd_3077477 1580224904156761090784447 := by
  unfold tailWord_3077477
  simp only [CollatzResearch.WordTrace]
  refine ⟨112244807471833895072254685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74829871647889263381503123 112244807471833895072254685)
  ·
    refine ⟨42091802801937710652095507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112244807471833895072254685 42091802801937710652095507)
    ·
      refine ⟨63137704202906565978143261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42091802801937710652095507 63137704202906565978143261)
      ·
        refine ⟨23676639076089962241803723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63137704202906565978143261 23676639076089962241803723)
        ·
          refine ⟨35514958614134943362705585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23676639076089962241803723 35514958614134943362705585)
          ·
            refine ⟨26636218960601207522029189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35514958614134943362705585 26636218960601207522029189)
            ·
              refine ⟨4994291055112726410380473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26636218960601207522029189 4994291055112726410380473)
              ·
                refine ⟨3745718291334544807785355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4994291055112726410380473 3745718291334544807785355)
                ·
                  refine ⟨5618577437001817211678033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3745718291334544807785355 5618577437001817211678033)
                  ·
                    refine ⟨4213933077751362908758525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5618577437001817211678033 4213933077751362908758525)
                    ·
                      refine ⟨1580224904156761090784447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213933077751362908758525 1580224904156761090784447)
                      ·
                        rfl

theorem cell23_3077477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_3077477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077477 prefixEnd_3077477 := by exact prefixLift 3077477
  have htrace : WordTrace (prefixWord ++ tailWord_3077477) baseStart_3077477 baseEnd_3077477 := by
    simpa [prefixWord, tailWord_3077477, baseEnd_3077477] using wordTrace_append hprefix tailTrace_3077477
  have hstable : (prefixWord ++ tailWord_3077477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077477).length < 2 ^ (prefixWord ++ tailWord_3077477).sum := by decide
  have hdescent : baseEnd_3077477 < baseStart_3077477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077480 : List Nat := [2, 1, 4, 2, 3, 1, 1, 9]
def baseStart_3077480 : Nat := 118140960795 + 3077480 * 2 ^ 59
def prefixEnd_3077480 : Nat := 4983230072969 + 3 ^ 40 * 3077480 * 2
def baseEnd_3077480 : Nat := 58526905355508317742479

theorem tailTrace_3077480 : CollatzResearch.WordTrace tailWord_3077480 prefixEnd_3077480 58526905355508317742479 := by
  unfold tailWord_3077480
  simp only [CollatzResearch.WordTrace]
  refine ⟨56122458445411513292306947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74829944593882017723075929 56122458445411513292306947)
  ·
    refine ⟨84183687668117269938460421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56122458445411513292306947 84183687668117269938460421)
    ·
      refine ⟨15784441437771988113461329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84183687668117269938460421 15784441437771988113461329)
      ·
        refine ⟨11838331078328991085095997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15784441437771988113461329 11838331078328991085095997)
        ·
          refine ⟨4439374154373371656910999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11838331078328991085095997 4439374154373371656910999)
          ·
            refine ⟨6659061231560057485366499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4439374154373371656910999 6659061231560057485366499)
            ·
              refine ⟨9988591847340086228049749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6659061231560057485366499 9988591847340086228049749)
              ·
                refine ⟨58526905355508317742479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9988591847340086228049749 58526905355508317742479)
                ·
                  rfl

theorem cell23_3077480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 9].length) (baseStart_3077480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077480 prefixEnd_3077480 := by exact prefixLift 3077480
  have htrace : WordTrace (prefixWord ++ tailWord_3077480) baseStart_3077480 baseEnd_3077480 := by
    simpa [prefixWord, tailWord_3077480, baseEnd_3077480] using wordTrace_append hprefix tailTrace_3077480
  have hstable : (prefixWord ++ tailWord_3077480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077480).length < 2 ^ (prefixWord ++ tailWord_3077480).sum := by decide
  have hdescent : baseEnd_3077480 < baseStart_3077480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077490 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3077490 : Nat := 118140960795 + 3077490 * 2 ^ 59
def prefixEnd_3077490 : Nat := 4983230072969 + 3 ^ 40 * 3077490 * 2
def baseEnd_3077490 : Nat := 1580231579405269539921887

theorem tailTrace_3077490 : CollatzResearch.WordTrace tailWord_3077490 prefixEnd_3077490 1580231579405269539921887 := by
  unfold tailWord_3077490
  simp only [CollatzResearch.WordTrace]
  refine ⟨28061320405196699573119481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74830187747191198861651949 28061320405196699573119481)
  ·
    refine ⟨21045990303897524679839611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28061320405196699573119481 21045990303897524679839611)
    ·
      refine ⟨31568985455846287019759417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21045990303897524679839611 31568985455846287019759417)
      ·
        refine ⟨23676739091884715264819563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31568985455846287019759417 23676739091884715264819563)
        ·
          refine ⟨35515108637827072897229345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23676739091884715264819563 35515108637827072897229345)
          ·
            refine ⟨26636331478370304672922009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35515108637827072897229345 26636331478370304672922009)
            ·
              refine ⟨19977248608777728504691507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26636331478370304672922009 19977248608777728504691507)
              ·
                refine ⟨29965872913166592757037261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19977248608777728504691507 29965872913166592757037261)
                ·
                  refine ⟨11237202342437472283888973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29965872913166592757037261 11237202342437472283888973)
                  ·
                    refine ⟨4213950878414052106458365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11237202342437472283888973 4213950878414052106458365)
                    ·
                      refine ⟨1580231579405269539921887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213950878414052106458365 1580231579405269539921887)
                      ·
                        rfl

theorem cell23_3077490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3077490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077490 prefixEnd_3077490 := by exact prefixLift 3077490
  have htrace : WordTrace (prefixWord ++ tailWord_3077490) baseStart_3077490 baseEnd_3077490 := by
    simpa [prefixWord, tailWord_3077490, baseEnd_3077490] using wordTrace_append hprefix tailTrace_3077490
  have hstable : (prefixWord ++ tailWord_3077490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077490).length < 2 ^ (prefixWord ++ tailWord_3077490).sum := by decide
  have hdescent : baseEnd_3077490 < baseStart_3077490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077507 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 4, 1, 3]
def baseStart_3077507 : Nat := 118140960795 + 3077507 * 2 ^ 59
def prefixEnd_3077507 : Nat := 4983230072969 + 3 ^ 40 * 3077507 * 2
def baseEnd_3077507 : Nat := 1580240308576395973409309

theorem tailTrace_3077507 : CollatzResearch.WordTrace tailWord_3077507 prefixEnd_3077507 1580240308576395973409309 := by
  unfold tailWord_3077507
  simp only [CollatzResearch.WordTrace]
  refine ⟨112245901661725210195846775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74830601107816806797231183 112245901661725210195846775)
  ·
    refine ⟨168368852492587815293770163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112245901661725210195846775 168368852492587815293770163)
    ·
      refine ⟨252553278738881722940655245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168368852492587815293770163 252553278738881722940655245)
      ·
        refine ⟨94707479527080646102745717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252553278738881722940655245 94707479527080646102745717)
        ·
          refine ⟨8878826205663810572132411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94707479527080646102745717 8878826205663810572132411)
          ·
            refine ⟨13318239308495715858198617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8878826205663810572132411 13318239308495715858198617)
            ·
              refine ⟨9988679481371786893648963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13318239308495715858198617 9988679481371786893648963)
              ·
                refine ⟨14983019222057680340473445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9988679481371786893648963 14983019222057680340473445)
                ·
                  refine ⟨2809316104135815063838771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14983019222057680340473445 2809316104135815063838771)
                  ·
                    refine ⟨4213974156203722595758157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2809316104135815063838771 4213974156203722595758157)
                    ·
                      refine ⟨1580240308576395973409309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4213974156203722595758157 1580240308576395973409309)
                      ·
                        rfl

theorem cell23_3077507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_3077507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077507 prefixEnd_3077507 := by exact prefixLift 3077507
  have htrace : WordTrace (prefixWord ++ tailWord_3077507) baseStart_3077507 baseEnd_3077507 := by
    simpa [prefixWord, tailWord_3077507, baseEnd_3077507] using wordTrace_append hprefix tailTrace_3077507
  have hstable : (prefixWord ++ tailWord_3077507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077507).length < 2 ^ (prefixWord ++ tailWord_3077507).sum := by decide
  have hdescent : baseEnd_3077507 < baseStart_3077507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077508 : List Nat := [2, 3, 2, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_3077508 : Nat := 118140960795 + 3077508 * 2 ^ 59
def prefixEnd_3077508 : Nat := 4983230072969 + 3 ^ 40 * 3077508 * 2
def baseEnd_3077508 : Nat := 1580240822057050469496805

theorem tailTrace_3077508 : CollatzResearch.WordTrace tailWord_3077508 prefixEnd_3077508 1580240822057050469496805 := by
  unfold tailWord_3077508
  simp only [CollatzResearch.WordTrace]
  refine ⟨56122969067360793683316589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74830625423147724911088785 56122969067360793683316589)
  ·
    refine ⟨21046113400260297631243721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56122969067360793683316589 21046113400260297631243721)
    ·
      refine ⟨15784585050195223223432791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21046113400260297631243721 15784585050195223223432791)
      ·
        refine ⟨23676877575292834835149187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15784585050195223223432791 23676877575292834835149187)
        ·
          refine ⟨35515316362939252252723781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23676877575292834835149187 35515316362939252252723781)
          ·
            refine ⟨6659121818051109797385709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35515316362939252252723781 6659121818051109797385709)
            ·
              refine ⟨2497170681769166174019641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6659121818051109797385709 2497170681769166174019641)
              ·
                refine ⟨1872878011326874630514731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2497170681769166174019641 1872878011326874630514731)
                ·
                  refine ⟨2809317016990311945772097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872878011326874630514731 2809317016990311945772097)
                  ·
                    refine ⟨2106987762742733959329073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2809317016990311945772097 2106987762742733959329073)
                    ·
                      refine ⟨1580240822057050469496805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2106987762742733959329073 1580240822057050469496805)
                      ·
                        rfl

theorem cell23_3077508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_3077508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077508 prefixEnd_3077508 := by exact prefixLift 3077508
  have htrace : WordTrace (prefixWord ++ tailWord_3077508) baseStart_3077508 baseEnd_3077508 := by
    simpa [prefixWord, tailWord_3077508, baseEnd_3077508] using wordTrace_append hprefix tailTrace_3077508
  have hstable : (prefixWord ++ tailWord_3077508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077508).length < 2 ^ (prefixWord ++ tailWord_3077508).sum := by decide
  have hdescent : baseEnd_3077508 < baseStart_3077508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077518 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_3077518 : Nat := 118140960795 + 3077518 * 2 ^ 59
def prefixEnd_3077518 : Nat := 4983230072969 + 3 ^ 40 * 3077518 * 2
def baseEnd_3077518 : Nat := 526748652287865143457253

theorem tailTrace_3077518 : CollatzResearch.WordTrace tailWord_3077518 prefixEnd_3077518 526748652287865143457253 := by
  unfold tailWord_3077518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14030787858085669884312151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74830868576456906049664805 14030787858085669884312151)
  ·
    refine ⟨21046181787128504826468227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14030787858085669884312151 21046181787128504826468227)
    ·
      refine ⟨31569272680692757239702341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21046181787128504826468227 31569272680692757239702341)
      ·
        refine ⟨5919238627629891982444189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31569272680692757239702341 5919238627629891982444189)
        ·
          refine ⟨2219714485361209493416571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5919238627629891982444189 2219714485361209493416571)
          ·
            refine ⟨3329571728041814240124857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219714485361209493416571 3329571728041814240124857)
            ·
              refine ⟨2497178796031360680093643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3329571728041814240124857 2497178796031360680093643)
              ·
                refine ⟨3745768194047041020140465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497178796031360680093643 3745768194047041020140465)
                ·
                  refine ⟨2809326145535280765105349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3745768194047041020140465 2809326145535280765105349)
                  ·
                    refine ⟨526748652287865143457253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2809326145535280765105349 526748652287865143457253)
                    ·
                      rfl

theorem cell23_3077518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_3077518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077518 prefixEnd_3077518 := by exact prefixLift 3077518
  have htrace : WordTrace (prefixWord ++ tailWord_3077518) baseStart_3077518 baseEnd_3077518 := by
    simpa [prefixWord, tailWord_3077518, baseEnd_3077518] using wordTrace_append hprefix tailTrace_3077518
  have hstable : (prefixWord ++ tailWord_3077518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077518).length < 2 ^ (prefixWord ++ tailWord_3077518).sum := by decide
  have hdescent : baseEnd_3077518 < baseStart_3077518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077600 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 2, 5]
def baseStart_3077600 : Nat := 118140960795 + 3077600 * 2 ^ 59
def prefixEnd_3077600 : Nat := 4983230072969 + 3 ^ 40 * 3077600 * 2
def baseEnd_3077600 : Nat := 526762687425754703182127

theorem tailTrace_3077600 : CollatzResearch.WordTrace tailWord_3077600 prefixEnd_3077600 526762687425754703182127 := by
  unfold tailWord_3077600
  simp only [CollatzResearch.WordTrace]
  refine ⟨56124646825194143539491127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74832862433592191385988169 56124646825194143539491127)
  ·
    refine ⟨84186970237791215309236691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56124646825194143539491127 84186970237791215309236691)
    ·
      refine ⟨126280455356686822963855037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84186970237791215309236691 126280455356686822963855037)
      ·
        refine ⟨47355170758757558611445639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126280455356686822963855037 47355170758757558611445639)
        ·
          refine ⟨71032756138136337917168459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47355170758757558611445639 71032756138136337917168459)
          ·
            refine ⟨106549134207204506875752689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71032756138136337917168459 106549134207204506875752689)
            ·
              refine ⟨79911850655403380156814517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106549134207204506875752689 79911850655403380156814517)
              ·
                refine ⟨7491735998944066889701361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79911850655403380156814517 7491735998944066889701361)
                ·
                  refine ⟨5618801999208050167276021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7491735998944066889701361 5618801999208050167276021)
                  ·
                    refine ⟨526762687425754703182127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5618801999208050167276021 526762687425754703182127)
                    ·
                      rfl

theorem cell23_3077600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_3077600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077600 prefixEnd_3077600 := by exact prefixLift 3077600
  have htrace : WordTrace (prefixWord ++ tailWord_3077600) baseStart_3077600 baseEnd_3077600 := by
    simpa [prefixWord, tailWord_3077600, baseEnd_3077600] using wordTrace_append hprefix tailTrace_3077600
  have hstable : (prefixWord ++ tailWord_3077600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077600).length < 2 ^ (prefixWord ++ tailWord_3077600).sum := by decide
  have hdescent : baseEnd_3077600 < baseStart_3077600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077660 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 10]
def baseStart_3077660 : Nat := 118140960795 + 3077660 * 2 ^ 59
def prefixEnd_3077660 : Nat := 4983230072969 + 3 ^ 40 * 3077660 * 2
def baseEnd_3077660 : Nat := 175590985679614874977345

theorem tailTrace_3077660 : CollatzResearch.WordTrace tailWord_3077660 prefixEnd_3077660 175590985679614874977345 := by
  unfold tailWord_3077660
  simp only [CollatzResearch.WordTrace]
  refine ⟨56125741015085458663083217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74834321353447278217444289 56125741015085458663083217)
  ·
    refine ⟨42094305761314093997312413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56125741015085458663083217 42094305761314093997312413)
    ·
      refine ⟨15785364660492785248992155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42094305761314093997312413 15785364660492785248992155)
      ·
        refine ⟨23678046990739177873488233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15785364660492785248992155 23678046990739177873488233)
        ·
          refine ⟨17758535243054383405116175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23678046990739177873488233 17758535243054383405116175)
          ·
            refine ⟨26637802864581575107674263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17758535243054383405116175 26637802864581575107674263)
            ·
              refine ⟨39956704296872362661511395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26637802864581575107674263 39956704296872362661511395)
              ·
                refine ⟨59935056445308543992267093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39956704296872362661511395 59935056445308543992267093)
                ·
                  refine ⟨175590985679614874977345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 59935056445308543992267093 175590985679614874977345)
                  ·
                    rfl

theorem cell23_3077660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_3077660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077660 prefixEnd_3077660 := by exact prefixLift 3077660
  have htrace : WordTrace (prefixWord ++ tailWord_3077660) baseStart_3077660 baseEnd_3077660 := by
    simpa [prefixWord, tailWord_3077660, baseEnd_3077660] using wordTrace_append hprefix tailTrace_3077660
  have hstable : (prefixWord ++ tailWord_3077660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077660).length < 2 ^ (prefixWord ++ tailWord_3077660).sum := by decide
  have hdescent : baseEnd_3077660 < baseStart_3077660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077674 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_3077674 : Nat := 118140960795 + 3077674 * 2 ^ 59
def prefixEnd_3077674 : Nat := 4983230072969 + 3 ^ 40 * 3077674 * 2
def baseEnd_3077674 : Nat := 1580326059845696820021041

theorem tailTrace_3077674 : CollatzResearch.WordTrace tailWord_3077674 prefixEnd_3077674 1580326059845696820021041 := by
  unfold tailWord_3077674
  simp only [CollatzResearch.WordTrace]
  refine ⟨28062998163030049429294019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74834661768080131811450717 28062998163030049429294019)
  ·
    refine ⟨42094497244545074143941029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28062998163030049429294019 42094497244545074143941029)
    ·
      refine ⟨7892718233352201401988943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42094497244545074143941029 7892718233352201401988943)
      ·
        refine ⟨11839077350028302102983415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7892718233352201401988943 11839077350028302102983415)
        ·
          refine ⟨17758616025042453154475123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11839077350028302102983415 17758616025042453154475123)
          ·
            refine ⟨26637924037563679731712685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17758616025042453154475123 26637924037563679731712685)
            ·
              refine ⟨9989221514086379899392257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26637924037563679731712685 9989221514086379899392257)
              ·
                refine ⟨7491916135564784924544193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9989221514086379899392257 7491916135564784924544193)
                ·
                  refine ⟨5618937101673588693408145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7491916135564784924544193 5618937101673588693408145)
                  ·
                    refine ⟨4214202826255191520056109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5618937101673588693408145 4214202826255191520056109)
                    ·
                      refine ⟨1580326059845696820021041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4214202826255191520056109 1580326059845696820021041)
                      ·
                        rfl

theorem cell23_3077674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_3077674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077674 prefixEnd_3077674 := by exact prefixLift 3077674
  have htrace : WordTrace (prefixWord ++ tailWord_3077674) baseStart_3077674 baseEnd_3077674 := by
    simpa [prefixWord, tailWord_3077674, baseEnd_3077674] using wordTrace_append hprefix tailTrace_3077674
  have hstable : (prefixWord ++ tailWord_3077674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077674).length < 2 ^ (prefixWord ++ tailWord_3077674).sum := by decide
  have hdescent : baseEnd_3077674 < baseStart_3077674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077737 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 4, 4]
def baseStart_3077737 : Nat := 118140960795 + 3077737 * 2 ^ 59
def prefixEnd_3077737 : Nat := 4983230072969 + 3 ^ 40 * 3077737 * 2
def baseEnd_3077737 : Nat := 526786136375643357844417

theorem tailTrace_3077737 : CollatzResearch.WordTrace tailWord_3077737 prefixEnd_3077737 526786136375643357844417 := by
  unfold tailWord_3077737
  simp only [CollatzResearch.WordTrace]
  refine ⟨112254290450891959476719465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74836193633927972984479643 112254290450891959476719465)
  ·
    refine ⟨84190717838168969607539599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112254290450891959476719465 84190717838168969607539599)
    ·
      refine ⟨126286076757253454411309399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84190717838168969607539599 126286076757253454411309399)
      ·
        refine ⟨189429115135880181616964099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126286076757253454411309399 189429115135880181616964099)
        ·
          refine ⟨284143672703820272425446149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189429115135880181616964099 284143672703820272425446149)
          ·
            refine ⟨53276938631966301079771153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284143672703820272425446149 53276938631966301079771153)
            ·
              refine ⟨39957703973974725809828365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53276938631966301079771153 39957703973974725809828365)
              ·
                refine ⟨14984138990240522178685637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39957703973974725809828365 14984138990240522178685637)
                ·
                  refine ⟨2809526060670097908503557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14984138990240522178685637 2809526060670097908503557)
                  ·
                    refine ⟨526786136375643357844417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2809526060670097908503557 526786136375643357844417)
                    ·
                      rfl

theorem cell23_3077737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 4].length) (baseStart_3077737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077737 prefixEnd_3077737 := by exact prefixLift 3077737
  have htrace : WordTrace (prefixWord ++ tailWord_3077737) baseStart_3077737 baseEnd_3077737 := by
    simpa [prefixWord, tailWord_3077737, baseEnd_3077737] using wordTrace_append hprefix tailTrace_3077737
  have hstable : (prefixWord ++ tailWord_3077737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077737).length < 2 ^ (prefixWord ++ tailWord_3077737).sum := by decide
  have hdescent : baseEnd_3077737 < baseStart_3077737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077738 : List Nat := [3, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_3077738 : Nat := 118140960795 + 3077738 * 2 ^ 59
def prefixEnd_3077738 : Nat := 4983230072969 + 3 ^ 40 * 3077738 * 2
def baseEnd_3077738 : Nat := 1580358922607584569620747

theorem tailTrace_3077738 : CollatzResearch.WordTrace tailWord_3077738 prefixEnd_3077738 1580358922607584569620747 := by
  unfold tailWord_3077738
  simp only [CollatzResearch.WordTrace]
  refine ⟨28063581730972084161876467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74836217949258891098337245 28063581730972084161876467)
  ·
    refine ⟨42095372596458126242814701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28063581730972084161876467 42095372596458126242814701)
    ·
      refine ⟨15785764723671797341055513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42095372596458126242814701 15785764723671797341055513)
      ·
        refine ⟨11839323542753848005791635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15785764723671797341055513 11839323542753848005791635)
        ·
          refine ⟨17758985314130772008687453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11839323542753848005791635 17758985314130772008687453)
          ·
            refine ⟨6659619492799039503257795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17758985314130772008687453 6659619492799039503257795)
            ·
              refine ⟨9989429239198559254886693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6659619492799039503257795 9989429239198559254886693)
              ·
                refine ⟨1873017982349729860291255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9989429239198559254886693 1873017982349729860291255)
                ·
                  refine ⟨2809526973524594790436883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873017982349729860291255 2809526973524594790436883)
                  ·
                    refine ⟨4214290460286892185655325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2809526973524594790436883 4214290460286892185655325)
                    ·
                      refine ⟨1580358922607584569620747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4214290460286892185655325 1580358922607584569620747)
                      ·
                        rfl

theorem cell23_3077738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_3077738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077738 prefixEnd_3077738 := by exact prefixLift 3077738
  have htrace : WordTrace (prefixWord ++ tailWord_3077738) baseStart_3077738 baseEnd_3077738 := by
    simpa [prefixWord, tailWord_3077738, baseEnd_3077738] using wordTrace_append hprefix tailTrace_3077738
  have hstable : (prefixWord ++ tailWord_3077738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077738).length < 2 ^ (prefixWord ++ tailWord_3077738).sum := by decide
  have hdescent : baseEnd_3077738 < baseStart_3077738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077761 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_3077761 : Nat := 118140960795 + 3077761 * 2 ^ 59
def prefixEnd_3077761 : Nat := 4983230072969 + 3 ^ 40 * 3077761 * 2
def baseEnd_3077761 : Nat := 1580370732662637979633141

theorem tailTrace_3077761 : CollatzResearch.WordTrace tailWord_3077761 prefixEnd_3077761 1580370732662637979633141 := by
  unfold tailWord_3077761
  simp only [CollatzResearch.WordTrace]
  refine ⟨112255165802805011575593137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74836777201870007717062091 112255165802805011575593137)
  ·
    refine ⟨84191374352103758681694853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112255165802805011575593137 84191374352103758681694853)
    ·
      refine ⟨15785882691019454752817785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84191374352103758681694853 15785882691019454752817785)
      ·
        refine ⟨11839412018264591064613339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15785882691019454752817785 11839412018264591064613339)
        ·
          refine ⟨17759118027396886596920009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11839412018264591064613339 17759118027396886596920009)
          ·
            refine ⟨13319338520547664947690007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17759118027396886596920009 13319338520547664947690007)
            ·
              refine ⟨19979007780821497421535011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13319338520547664947690007 19979007780821497421535011)
              ·
                refine ⟨29968511671232246132302517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19979007780821497421535011 29968511671232246132302517)
                ·
                  refine ⟨2809547969178023074903361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29968511671232246132302517 2809547969178023074903361)
                  ·
                    refine ⟨2107160976883517306177521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2809547969178023074903361 2107160976883517306177521)
                    ·
                      refine ⟨1580370732662637979633141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2107160976883517306177521 1580370732662637979633141)
                      ·
                        rfl

theorem cell23_3077761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_3077761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077761 prefixEnd_3077761 := by exact prefixLift 3077761
  have htrace : WordTrace (prefixWord ++ tailWord_3077761) baseStart_3077761 baseEnd_3077761 := by
    simpa [prefixWord, tailWord_3077761, baseEnd_3077761] using wordTrace_append hprefix tailTrace_3077761
  have hstable : (prefixWord ++ tailWord_3077761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077761).length < 2 ^ (prefixWord ++ tailWord_3077761).sum := by decide
  have hdescent : baseEnd_3077761 < baseStart_3077761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077774 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3077774 : Nat := 118140960795 + 3077774 * 2 ^ 59
def prefixEnd_3077774 : Nat := 4983230072969 + 3 ^ 40 * 3077774 * 2
def baseEnd_3077774 : Nat := 1580377407911146428770581

theorem tailTrace_3077774 : CollatzResearch.WordTrace tailWord_3077774 prefixEnd_3077774 1580377407911146428770581 := by
  unfold tailWord_3077774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14031954993969739349477047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74837093301171943197210917 14031954993969739349477047)
  ·
    refine ⟨21047932490954609024215571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14031954993969739349477047 21047932490954609024215571)
    ·
      refine ⟨31571898736431913536323357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21047932490954609024215571 31571898736431913536323357)
      ·
        refine ⟨11839462026161967576121259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31571898736431913536323357 11839462026161967576121259)
        ·
          refine ⟨17759193039242951364181889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11839462026161967576121259 17759193039242951364181889)
          ·
            refine ⟨13319394779432213523136417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17759193039242951364181889 13319394779432213523136417)
            ·
              refine ⟨9989546084574160142352313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13319394779432213523136417 9989546084574160142352313)
              ·
                refine ⟨7492159563430620106764235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9989546084574160142352313 7492159563430620106764235)
                ·
                  refine ⟨11238239345145930160146353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7492159563430620106764235 11238239345145930160146353)
                  ·
                    refine ⟨8428679508859447620109765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11238239345145930160146353 8428679508859447620109765)
                    ·
                      refine ⟨1580377407911146428770581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8428679508859447620109765 1580377407911146428770581)
                      ·
                        rfl

theorem cell23_3077774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3077774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077774 prefixEnd_3077774 := by exact prefixLift 3077774
  have htrace : WordTrace (prefixWord ++ tailWord_3077774) baseStart_3077774 baseEnd_3077774 := by
    simpa [prefixWord, tailWord_3077774, baseEnd_3077774] using wordTrace_append hprefix tailTrace_3077774
  have hstable : (prefixWord ++ tailWord_3077774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077774).length < 2 ^ (prefixWord ++ tailWord_3077774).sum := by decide
  have hdescent : baseEnd_3077774 < baseStart_3077774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077777 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 3]
def baseStart_3077777 : Nat := 118140960795 + 3077777 * 2 ^ 59
def prefixEnd_3077777 : Nat := 4983230072969 + 3 ^ 40 * 3077777 * 2
def baseEnd_3077777 : Nat := 1580378948353109917033067

theorem tailTrace_3077777 : CollatzResearch.WordTrace tailWord_3077777 prefixEnd_3077777 1580378948353109917033067 := by
  unfold tailWord_3077777
  simp only [CollatzResearch.WordTrace]
  refine ⟨112255749370747046308175585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74837166247164697538783723 112255749370747046308175585)
  ·
    refine ⟨84191812028060284731131689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112255749370747046308175585 84191812028060284731131689)
    ·
      refine ⟨63143859021045213548348767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84191812028060284731131689 63143859021045213548348767)
      ·
        refine ⟨94715788531567820322523151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63143859021045213548348767 94715788531567820322523151)
        ·
          refine ⟨142073682797351730483784727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94715788531567820322523151 142073682797351730483784727)
          ·
            refine ⟨213110524196027595725677091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142073682797351730483784727 213110524196027595725677091)
            ·
              refine ⟨319665786294041393588515637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213110524196027595725677091 319665786294041393588515637)
              ·
                refine ⟨29968667465066380648923341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 319665786294041393588515637 29968667465066380648923341)
                ·
                  refine ⟨11238250299399892743346253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29968667465066380648923341 11238250299399892743346253)
                  ·
                    refine ⟨4214343862274959778754845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11238250299399892743346253 4214343862274959778754845)
                    ·
                      refine ⟨1580378948353109917033067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4214343862274959778754845 1580378948353109917033067)
                      ·
                        rfl

theorem cell23_3077777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_3077777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077777 prefixEnd_3077777 := by exact prefixLift 3077777
  have htrace : WordTrace (prefixWord ++ tailWord_3077777) baseStart_3077777 baseEnd_3077777 := by
    simpa [prefixWord, tailWord_3077777, baseEnd_3077777] using wordTrace_append hprefix tailTrace_3077777
  have hstable : (prefixWord ++ tailWord_3077777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077777).length < 2 ^ (prefixWord ++ tailWord_3077777).sum := by decide
  have hdescent : baseEnd_3077777 < baseStart_3077777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077788 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_3077788 : Nat := 118140960795 + 3077788 * 2 ^ 59
def prefixEnd_3077788 : Nat := 4983230072969 + 3 ^ 40 * 3077788 * 2
def baseEnd_3077788 : Nat := 526794865546769791331839

theorem tailTrace_3077788 : CollatzResearch.WordTrace tailWord_3077788 prefixEnd_3077788 526794865546769791331839 := by
  unfold tailWord_3077788
  simp only [CollatzResearch.WordTrace]
  refine ⟨56128075286853597593413009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74837433715804796791217345 56128075286853597593413009)
  ·
    refine ⟨42096056465140198195059757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56128075286853597593413009 42096056465140198195059757)
    ·
      refine ⟨15786021174427574323147409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42096056465140198195059757 15786021174427574323147409)
      ·
        refine ⟨11839515880820680742360557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15786021174427574323147409 11839515880820680742360557)
        ·
          refine ⟨4439818455307755278385209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11839515880820680742360557 4439818455307755278385209)
          ·
            refine ⟨3329863841480816458788907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4439818455307755278385209 3329863841480816458788907)
            ·
              refine ⟨4994795762221224688183361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3329863841480816458788907 4994795762221224688183361)
              ·
                refine ⟨3746096821665918516137521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4994795762221224688183361 3746096821665918516137521)
                ·
                  refine ⟨2809572616249438887103141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3746096821665918516137521 2809572616249438887103141)
                  ·
                    refine ⟨526794865546769791331839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2809572616249438887103141 526794865546769791331839)
                    ·
                      rfl

theorem cell23_3077788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_3077788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077788 prefixEnd_3077788 := by exact prefixLift 3077788
  have htrace : WordTrace (prefixWord ++ tailWord_3077788) baseStart_3077788 baseEnd_3077788 := by
    simpa [prefixWord, tailWord_3077788, baseEnd_3077788] using wordTrace_append hprefix tailTrace_3077788
  have hstable : (prefixWord ++ tailWord_3077788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077788).length < 2 ^ (prefixWord ++ tailWord_3077788).sum := by decide
  have hdescent : baseEnd_3077788 < baseStart_3077788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077817 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3077817 : Nat := 118140960795 + 3077817 * 2 ^ 59
def prefixEnd_3077817 : Nat := 4983230072969 + 3 ^ 40 * 3077817 * 2
def baseEnd_3077817 : Nat := 1580399487579289760532883

theorem tailTrace_3077817 : CollatzResearch.WordTrace tailWord_3077817 prefixEnd_3077817 1580399487579289760532883 := by
  unfold tailWord_3077817
  simp only [CollatzResearch.WordTrace]
  refine ⟨112257208290602133139631705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74838138860401422093087803 112257208290602133139631705)
  ·
    refine ⟨84192906217951599854723779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112257208290602133139631705 84192906217951599854723779)
    ·
      refine ⟨126289359326927399782085669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84192906217951599854723779 126289359326927399782085669)
      ·
        refine ⟨23679254873798887459141063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126289359326927399782085669 23679254873798887459141063)
        ·
          refine ⟨35518882310698331188711595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23679254873798887459141063 35518882310698331188711595)
          ·
            refine ⟨53278323466047496783067393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35518882310698331188711595 53278323466047496783067393)
            ·
              refine ⟨39958742599535622587300545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53278323466047496783067393 39958742599535622587300545)
              ·
                refine ⟨29969056949651716940475409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39958742599535622587300545 29969056949651716940475409)
                ·
                  refine ⟨22476792712238787705356557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29969056949651716940475409 22476792712238787705356557)
                  ·
                    refine ⟨8428797267089545389508709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22476792712238787705356557 8428797267089545389508709)
                    ·
                      refine ⟨1580399487579289760532883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8428797267089545389508709 1580399487579289760532883)
                      ·
                        rfl

theorem cell23_3077817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3077817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077817 prefixEnd_3077817 := by exact prefixLift 3077817
  have htrace : WordTrace (prefixWord ++ tailWord_3077817) baseStart_3077817 baseEnd_3077817 := by
    simpa [prefixWord, tailWord_3077817, baseEnd_3077817] using wordTrace_append hprefix tailTrace_3077817
  have hstable : (prefixWord ++ tailWord_3077817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077817).length < 2 ^ (prefixWord ++ tailWord_3077817).sum := by decide
  have hdescent : baseEnd_3077817 < baseStart_3077817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077846 : List Nat := [5, 2, 1, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3077846 : Nat := 118140960795 + 3077846 * 2 ^ 59
def prefixEnd_3077846 : Nat := 4983230072969 + 3 ^ 40 * 3077846 * 2
def baseEnd_3077846 : Nat := 1580414378518270147070251

theorem tailTrace_3077846 : CollatzResearch.WordTrace tailWord_3077846 prefixEnd_3077846 1580414378518270147070251 := by
  unfold tailWord_3077846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7016141625468566943277337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74838844004998047394958261 7016141625468566943277337)
  ·
    refine ⟨5262106219101425207458003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7016141625468566943277337 5262106219101425207458003)
    ·
      refine ⟨7893159328652137811187005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5262106219101425207458003 7893159328652137811187005)
      ·
        refine ⟨2959934748244551679195127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7893159328652137811187005 2959934748244551679195127)
        ·
          refine ⟨4439902122366827518792691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2959934748244551679195127 4439902122366827518792691)
          ·
            refine ⟨6659853183550241278189037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4439902122366827518792691 6659853183550241278189037)
            ·
              refine ⟨2497444943831340479320889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6659853183550241278189037 2497444943831340479320889)
              ·
                refine ⟨1873083707873505359490667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2497444943831340479320889 1873083707873505359490667)
                ·
                  refine ⟨2809625561810258039236001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873083707873505359490667 2809625561810258039236001)
                  ·
                    refine ⟨2107219171357693529427001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2809625561810258039236001 2107219171357693529427001)
                    ·
                      refine ⟨1580414378518270147070251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2107219171357693529427001 1580414378518270147070251)
                      ·
                        rfl

theorem cell23_3077846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3077846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077846 prefixEnd_3077846 := by exact prefixLift 3077846
  have htrace : WordTrace (prefixWord ++ tailWord_3077846) baseStart_3077846 baseEnd_3077846 := by
    simpa [prefixWord, tailWord_3077846, baseEnd_3077846] using wordTrace_append hprefix tailTrace_3077846
  have hstable : (prefixWord ++ tailWord_3077846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077846).length < 2 ^ (prefixWord ++ tailWord_3077846).sum := by decide
  have hdescent : baseEnd_3077846 < baseStart_3077846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077887 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 1, 7]
def baseStart_3077887 : Nat := 118140960795 + 3077887 * 2 ^ 59
def prefixEnd_3077887 : Nat := 4983230072969 + 3 ^ 40 * 3077887 * 2
def baseEnd_3077887 : Nat := 526811810408368162219187

theorem tailTrace_3077887 : CollatzResearch.WordTrace tailWord_3077887 prefixEnd_3077887 526811810408368162219187 := by
  unfold tailWord_3077887
  simp only [CollatzResearch.WordTrace]
  refine ⟨112259761400348535094679915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74839840933565690063119943 112259761400348535094679915)
  ·
    refine ⟨168389642100522802642019873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112259761400348535094679915 168389642100522802642019873)
    ·
      refine ⟨126292231575392101981514905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168389642100522802642019873 126292231575392101981514905)
      ·
        refine ⟨94719173681544076486136179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126292231575392101981514905 94719173681544076486136179)
        ·
          refine ⟨142078760522316114729204269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94719173681544076486136179 142078760522316114729204269)
          ·
            refine ⟨53279535195868543023451601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142078760522316114729204269 53279535195868543023451601)
            ·
              refine ⟨39959651396901407267588701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53279535195868543023451601 39959651396901407267588701)
              ·
                refine ⟨14984869273838027725345763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39959651396901407267588701 14984869273838027725345763)
                ·
                  refine ⟨22477303910757041588018645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14984869273838027725345763 22477303910757041588018645)
                  ·
                    refine ⟨526811810408368162219187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22477303910757041588018645 526811810408368162219187)
                    ·
                      rfl

theorem cell23_3077887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_3077887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077887 prefixEnd_3077887 := by exact prefixLift 3077887
  have htrace : WordTrace (prefixWord ++ tailWord_3077887) baseStart_3077887 baseEnd_3077887 := by
    simpa [prefixWord, tailWord_3077887, baseEnd_3077887] using wordTrace_append hprefix tailTrace_3077887
  have hstable : (prefixWord ++ tailWord_3077887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077887).length < 2 ^ (prefixWord ++ tailWord_3077887).sum := by decide
  have hdescent : baseEnd_3077887 < baseStart_3077887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077911 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 2, 5, 2]
def baseStart_3077911 : Nat := 118140960795 + 3077911 * 2 ^ 59
def prefixEnd_3077911 : Nat := 4983230072969 + 3 ^ 40 * 3077911 * 2
def baseEnd_3077911 : Nat := 1580447754760812392757451

theorem tailTrace_3077911 : CollatzResearch.WordTrace tailWord_3077911 prefixEnd_3077911 1580447754760812392757451 := by
  unfold tailWord_3077911
  simp only [CollatzResearch.WordTrace]
  refine ⟨112260636752261587193553587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74840424501507724795702391 112260636752261587193553587)
  ·
    refine ⟨168390955128392380790330381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112260636752261587193553587 168390955128392380790330381)
    ·
      refine ⟨63146608173147142796373893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168390955128392380790330381 63146608173147142796373893)
      ·
        refine ⟨11839989032465089274320105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63146608173147142796373893 11839989032465089274320105)
        ·
          refine ⟨8879991774348816955740079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11839989032465089274320105 8879991774348816955740079)
          ·
            refine ⟨13319987661523225433610119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8879991774348816955740079 13319987661523225433610119)
            ·
              refine ⟨19979981492284838150415179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13319987661523225433610119 19979981492284838150415179)
              ·
                refine ⟨29969972238427257225622769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19979981492284838150415179 29969972238427257225622769)
                ·
                  refine ⟨22477479178820442919217077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29969972238427257225622769 22477479178820442919217077)
                  ·
                    refine ⟨2107263673014416523676601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22477479178820442919217077 2107263673014416523676601)
                    ·
                      refine ⟨1580447754760812392757451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2107263673014416523676601 1580447754760812392757451)
                      ·
                        rfl

theorem cell23_3077911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_3077911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077911 prefixEnd_3077911 := by exact prefixLift 3077911
  have htrace : WordTrace (prefixWord ++ tailWord_3077911) baseStart_3077911 baseEnd_3077911 := by
    simpa [prefixWord, tailWord_3077911, baseEnd_3077911] using wordTrace_append hprefix tailTrace_3077911
  have hstable : (prefixWord ++ tailWord_3077911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077911).length < 2 ^ (prefixWord ++ tailWord_3077911).sum := by decide
  have hdescent : baseEnd_3077911 < baseStart_3077911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077914 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_3077914 : Nat := 118140960795 + 3077914 * 2 ^ 59
def prefixEnd_3077914 : Nat := 4983230072969 + 3 ^ 40 * 3077914 * 2
def baseEnd_3077914 : Nat := 1580449295202775881019937

theorem tailTrace_3077914 : CollatzResearch.WordTrace tailWord_3077914 prefixEnd_3077914 1580449295202775881019937 := by
  unfold tailWord_3077914
  simp only [CollatzResearch.WordTrace]
  refine ⟨28065186542812679676478199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74840497447500479137275197 28065186542812679676478199)
  ·
    refine ⟨42097779814219019514717299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28065186542812679676478199 42097779814219019514717299)
    ·
      refine ⟨63146669721328529272075949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42097779814219019514717299 63146669721328529272075949)
      ·
        refine ⟨23680001145498198477028481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63146669721328529272075949 23680001145498198477028481)
        ·
          refine ⟨17760000859123648857771361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23680001145498198477028481 17760000859123648857771361)
          ·
            refine ⟨13320000644342736643328521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17760000859123648857771361 13320000644342736643328521)
            ·
              refine ⟨9990000483257052482496391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13320000644342736643328521 9990000483257052482496391)
              ·
                refine ⟨14985000724885578723744587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9990000483257052482496391 14985000724885578723744587)
                ·
                  refine ⟨22477501087328368085616881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14985000724885578723744587 22477501087328368085616881)
                  ·
                    refine ⟨16858125815496276064212661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22477501087328368085616881 16858125815496276064212661)
                    ·
                      refine ⟨1580449295202775881019937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16858125815496276064212661 1580449295202775881019937)
                      ·
                        rfl

theorem cell23_3077914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_3077914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077914 prefixEnd_3077914 := by exact prefixLift 3077914
  have htrace : WordTrace (prefixWord ++ tailWord_3077914) baseStart_3077914 baseEnd_3077914 := by
    simpa [prefixWord, tailWord_3077914, baseEnd_3077914] using wordTrace_append hprefix tailTrace_3077914
  have hstable : (prefixWord ++ tailWord_3077914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077914).length < 2 ^ (prefixWord ++ tailWord_3077914).sum := by decide
  have hdescent : baseEnd_3077914 < baseStart_3077914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3077941 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_3077941 : Nat := 118140960795 + 3077941 * 2 ^ 59
def prefixEnd_3077941 : Nat := 4983230072969 + 3 ^ 40 * 3077941 * 2
def baseEnd_3077941 : Nat := 1580463159180447275382313

theorem tailTrace_3077941 : CollatzResearch.WordTrace tailWord_3077941 prefixEnd_3077941 1580463159180447275382313 := by
  unfold tailWord_3077941
  simp only [CollatzResearch.WordTrace]
  refine ⟨112261730942152902317145677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74841153961435268211430451 112261730942152902317145677)
  ·
    refine ⟨42098149103307338368929629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112261730942152902317145677 42098149103307338368929629)
    ·
      refine ⟨15786805913740251888348611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42098149103307338368929629 15786805913740251888348611)
      ·
        refine ⟨23680208870610377832522917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15786805913740251888348611 23680208870610377832522917)
        ·
          refine ⟨4440039163239445843598047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23680208870610377832522917 4440039163239445843598047)
          ·
            refine ⟨6660058744859168765397071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4440039163239445843598047 6660058744859168765397071)
            ·
              refine ⟨9990088117288753148095607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6660058744859168765397071 9990088117288753148095607)
              ·
                refine ⟨14985132175933129722143411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9990088117288753148095607 14985132175933129722143411)
                ·
                  refine ⟨22477698263899694583215117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14985132175933129722143411 22477698263899694583215117)
                  ·
                    refine ⟨8429136848962385468705669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22477698263899694583215117 8429136848962385468705669)
                    ·
                      refine ⟨1580463159180447275382313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8429136848962385468705669 1580463159180447275382313)
                      ·
                        rfl

theorem cell23_3077941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_3077941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3077941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3077941 prefixEnd_3077941 := by exact prefixLift 3077941
  have htrace : WordTrace (prefixWord ++ tailWord_3077941) baseStart_3077941 baseEnd_3077941 := by
    simpa [prefixWord, tailWord_3077941, baseEnd_3077941] using wordTrace_append hprefix tailTrace_3077941
  have hstable : (prefixWord ++ tailWord_3077941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3077941).length < 2 ^ (prefixWord ++ tailWord_3077941).sum := by decide
  have hdescent : baseEnd_3077941 < baseStart_3077941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3077941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078001 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 1, 5, 2]
def baseStart_3078001 : Nat := 118140960795 + 3078001 * 2 ^ 59
def prefixEnd_3078001 : Nat := 4983230072969 + 3 ^ 40 * 3078001 * 2
def baseEnd_3078001 : Nat := 1580493968019717040632037

theorem tailTrace_3078001 : CollatzResearch.WordTrace tailWord_3078001 prefixEnd_3078001 1580493968019717040632037 := by
  unfold tailWord_3078001
  simp only [CollatzResearch.WordTrace]
  refine ⟨112263919321935532564329857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74842612881290355042886571 112263919321935532564329857)
  ·
    refine ⟨84197939491451649423247393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112263919321935532564329857 84197939491451649423247393)
    ·
      refine ⟨63148454618588737067435545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84197939491451649423247393 63148454618588737067435545)
      ·
        refine ⟨47361340963941552800576659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63148454618588737067435545 47361340963941552800576659)
        ·
          refine ⟨71042011445912329200864989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47361340963941552800576659 71042011445912329200864989)
          ·
            refine ⟨26640754292217123450324371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71042011445912329200864989 26640754292217123450324371)
            ·
              refine ⟨39961131438325685175486557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26640754292217123450324371 39961131438325685175486557)
              ·
                refine ⟨14985424289372131940807459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39961131438325685175486557 14985424289372131940807459)
                ·
                  refine ⟨22478136434058197911211189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14985424289372131940807459 22478136434058197911211189)
                  ·
                    refine ⟨2107325290692956054176049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22478136434058197911211189 2107325290692956054176049)
                    ·
                      refine ⟨1580493968019717040632037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2107325290692956054176049 1580493968019717040632037)
                      ·
                        rfl

theorem cell23_3078001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_3078001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078001 prefixEnd_3078001 := by exact prefixLift 3078001
  have htrace : WordTrace (prefixWord ++ tailWord_3078001) baseStart_3078001 baseEnd_3078001 := by
    simpa [prefixWord, tailWord_3078001, baseEnd_3078001] using wordTrace_append hprefix tailTrace_3078001
  have hstable : (prefixWord ++ tailWord_3078001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078001).length < 2 ^ (prefixWord ++ tailWord_3078001).sum := by decide
  have hdescent : baseEnd_3078001 < baseStart_3078001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078048 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 5, 2, 2]
def baseStart_3078048 : Nat := 118140960795 + 3078048 * 2 ^ 59
def prefixEnd_3078048 : Nat := 4983230072969 + 3 ^ 40 * 3078048 * 2
def baseEnd_3078048 : Nat := 1580518101610478356744321

theorem tailTrace_3078048 : CollatzResearch.WordTrace tailWord_3078048 prefixEnd_3078048 1580518101610478356744321 := by
  unfold tailWord_3078048
  simp only [CollatzResearch.WordTrace]
  refine ⟨56132816776382629795645399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74843755701843506394193865 56132816776382629795645399)
  ·
    refine ⟨84199225164573944693468099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56132816776382629795645399 84199225164573944693468099)
    ·
      refine ⟨126298837746860917040202149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84199225164573944693468099 126298837746860917040202149)
      ·
        refine ⟨23681032077536421945037903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126298837746860917040202149 23681032077536421945037903)
        ·
          refine ⟨35521548116304632917556855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23681032077536421945037903 35521548116304632917556855)
          ·
            refine ⟨53282322174456949376335283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35521548116304632917556855 53282322174456949376335283)
            ·
              refine ⟨79923483261685424064502925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53282322174456949376335283 79923483261685424064502925)
              ·
                refine ⟨29971306223132034024188597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79923483261685424064502925 29971306223132034024188597)
                ·
                  refine ⟨2809809958418628189767681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29971306223132034024188597 2809809958418628189767681)
                  ·
                    refine ⟨2107357468813971142325761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2809809958418628189767681 2107357468813971142325761)
                    ·
                      refine ⟨1580518101610478356744321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2107357468813971142325761 1580518101610478356744321)
                      ·
                        rfl

theorem cell23_3078048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_3078048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078048 prefixEnd_3078048 := by exact prefixLift 3078048
  have htrace : WordTrace (prefixWord ++ tailWord_3078048) baseStart_3078048 baseEnd_3078048 := by
    simpa [prefixWord, tailWord_3078048, baseEnd_3078048] using wordTrace_append hprefix tailTrace_3078048
  have hstable : (prefixWord ++ tailWord_3078048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078048).length < 2 ^ (prefixWord ++ tailWord_3078048).sum := by decide
  have hdescent : baseEnd_3078048 < baseStart_3078048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078065 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 1, 1, 4]
def baseStart_3078065 : Nat := 118140960795 + 3078065 * 2 ^ 59
def prefixEnd_3078065 : Nat := 4983230072969 + 3 ^ 40 * 3078065 * 2
def baseEnd_3078065 : Nat := 1580526830781604790231743

theorem tailTrace_3078065 : CollatzResearch.WordTrace tailWord_3078065 prefixEnd_3078065 1580526830781604790231743 := by
  unfold tailWord_3078065
  simp only [CollatzResearch.WordTrace]
  refine ⟨112266253593703671494659649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74844169062469114329773099 112266253593703671494659649)
  ·
    refine ⟨84199690195277753620994737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112266253593703671494659649 84199690195277753620994737)
    ·
      refine ⟨63149767646458315215746053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84199690195277753620994737 63149767646458315215746053)
      ·
        refine ⟨11840581433710934102952385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63149767646458315215746053 11840581433710934102952385)
        ·
          refine ⟨8880436075283200577214289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11840581433710934102952385 8880436075283200577214289)
          ·
            refine ⟨6660327056462400432910717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8880436075283200577214289 6660327056462400432910717)
            ·
              refine ⟨2497622646173400162341519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6660327056462400432910717 2497622646173400162341519)
              ·
                refine ⟨3746433969260100243512279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497622646173400162341519 3746433969260100243512279)
                ·
                  refine ⟨5619650953890150365268419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3746433969260100243512279 5619650953890150365268419)
                  ·
                    refine ⟨8429476430835225547902629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5619650953890150365268419 8429476430835225547902629)
                    ·
                      refine ⟨1580526830781604790231743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8429476430835225547902629 1580526830781604790231743)
                      ·
                        rfl

theorem cell23_3078065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_3078065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078065 prefixEnd_3078065 := by exact prefixLift 3078065
  have htrace : WordTrace (prefixWord ++ tailWord_3078065) baseStart_3078065 baseEnd_3078065 := by
    simpa [prefixWord, tailWord_3078065, baseEnd_3078065] using wordTrace_append hprefix tailTrace_3078065
  have hstable : (prefixWord ++ tailWord_3078065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078065).length < 2 ^ (prefixWord ++ tailWord_3078065).sum := by decide
  have hdescent : baseEnd_3078065 < baseStart_3078065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078074 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_3078074 : Nat := 118140960795 + 3078074 * 2 ^ 59
def prefixEnd_3078074 : Nat := 4983230072969 + 3 ^ 40 * 3078074 * 2
def baseEnd_3078074 : Nat := 1580531452107495255019201

theorem tailTrace_3078074 : CollatzResearch.WordTrace tailWord_3078074 prefixEnd_3078074 1580531452107495255019201 := by
  unfold tailWord_3078074
  simp only [CollatzResearch.WordTrace]
  refine ⟨28066645462667766507934319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74844387900447377354491517 28066645462667766507934319)
  ·
    refine ⟨42099968194001649761901479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28066645462667766507934319 42099968194001649761901479)
    ·
      refine ⟨63149952291002474642852219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42099968194001649761901479 63149952291002474642852219)
      ·
        refine ⟨94724928436503711964278329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63149952291002474642852219 94724928436503711964278329)
        ·
          refine ⟨71043696327377783973208747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94724928436503711964278329 71043696327377783973208747)
          ·
            refine ⟨106565544491066675959813121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71043696327377783973208747 106565544491066675959813121)
            ·
              refine ⟨79924158368300006969859841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106565544491066675959813121 79924158368300006969859841)
              ·
                refine ⟨59943118776225005227394881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79924158368300006969859841 59943118776225005227394881)
                ·
                  refine ⟨44957339082168753920546161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59943118776225005227394881 44957339082168753920546161)
                  ·
                    refine ⟨33718004311626565440409621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44957339082168753920546161 33718004311626565440409621)
                    ·
                      refine ⟨1580531452107495255019201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33718004311626565440409621 1580531452107495255019201)
                      ·
                        rfl

theorem cell23_3078074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_3078074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078074 prefixEnd_3078074 := by exact prefixLift 3078074
  have htrace : WordTrace (prefixWord ++ tailWord_3078074) baseStart_3078074 baseEnd_3078074 := by
    simpa [prefixWord, tailWord_3078074, baseEnd_3078074] using wordTrace_append hprefix tailTrace_3078074
  have hstable : (prefixWord ++ tailWord_3078074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078074).length < 2 ^ (prefixWord ++ tailWord_3078074).sum := by decide
  have hdescent : baseEnd_3078074 < baseStart_3078074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078076 : List Nat := [2, 2, 2, 5, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3078076 : Nat := 118140960795 + 3078076 * 2 ^ 59
def prefixEnd_3078076 : Nat := 4983230072969 + 3 ^ 40 * 3078076 * 2
def baseEnd_3078076 : Nat := 1580532479068804247194193

theorem tailTrace_3078076 : CollatzResearch.WordTrace tailWord_3078076 prefixEnd_3078076 1580532479068804247194193 := by
  unfold tailWord_3078076
  simp only [CollatzResearch.WordTrace]
  refine ⟨56133327398331910186655041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74844436531109213582206721 56133327398331910186655041)
  ·
    refine ⟨42099995548748932639991281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56133327398331910186655041 42099995548748932639991281)
    ·
      refine ⟨31574996661561699479993461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42099995548748932639991281 31574996661561699479993461)
      ·
        refine ⟨2960155937021409326249387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31574996661561699479993461 2960155937021409326249387)
        ·
          refine ⟨4440233905532113989374081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2960155937021409326249387 4440233905532113989374081)
          ·
            refine ⟨3330175429149085492030561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4440233905532113989374081 3330175429149085492030561)
            ·
              refine ⟨2497631571861814119022921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330175429149085492030561 2497631571861814119022921)
              ·
                refine ⟨1873223678896360589267191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2497631571861814119022921 1873223678896360589267191)
                ·
                  refine ⟨2809835518344540883900787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873223678896360589267191 2809835518344540883900787)
                  ·
                    refine ⟨4214753277516811325851181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2809835518344540883900787 4214753277516811325851181)
                    ·
                      refine ⟨1580532479068804247194193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4214753277516811325851181 1580532479068804247194193)
                      ·
                        rfl

theorem cell23_3078076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3078076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078076 prefixEnd_3078076 := by exact prefixLift 3078076
  have htrace : WordTrace (prefixWord ++ tailWord_3078076) baseStart_3078076 baseEnd_3078076 := by
    simpa [prefixWord, tailWord_3078076, baseEnd_3078076] using wordTrace_append hprefix tailTrace_3078076
  have hstable : (prefixWord ++ tailWord_3078076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078076).length < 2 ^ (prefixWord ++ tailWord_3078076).sum := by decide
  have hdescent : baseEnd_3078076 < baseStart_3078076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078119 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_3078119 : Nat := 118140960795 + 3078119 * 2 ^ 59
def prefixEnd_3078119 : Nat := 4983230072969 + 3 ^ 40 * 3078119 * 2
def baseEnd_3078119 : Nat := 1580554558736947578956495

theorem tailTrace_3078119 : CollatzResearch.WordTrace tailWord_3078119 prefixEnd_3078119 1580554558736947578956495 := by
  unfold tailWord_3078119
  simp only [CollatzResearch.WordTrace]
  refine ⟨112268223135508038717125411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74845482090338692478083607 112268223135508038717125411)
  ·
    refine ⟨168402334703262058075688117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112268223135508038717125411 168402334703262058075688117)
    ·
      refine ⟨15787718878430817944595761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168402334703262058075688117 15787718878430817944595761)
      ·
        refine ⟨11840789158823113458446821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15787718878430817944595761 11840789158823113458446821)
        ·
          refine ⟨2220147967279333773458779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11840789158823113458446821 2220147967279333773458779)
          ·
            refine ⟨3330221950919000660188169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220147967279333773458779 3330221950919000660188169)
            ·
              refine ⟨2497666463189250495141127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330221950919000660188169 2497666463189250495141127)
              ·
                refine ⟨3746499694783875742711691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497666463189250495141127 3746499694783875742711691)
                ·
                  refine ⟨5619749542175813614067537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3746499694783875742711691 5619749542175813614067537)
                  ·
                    refine ⟨4214812156631860210550653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5619749542175813614067537 4214812156631860210550653)
                    ·
                      refine ⟨1580554558736947578956495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4214812156631860210550653 1580554558736947578956495)
                      ·
                        rfl

theorem cell23_3078119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_3078119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078119 prefixEnd_3078119 := by exact prefixLift 3078119
  have htrace : WordTrace (prefixWord ++ tailWord_3078119) baseStart_3078119 baseEnd_3078119 := by
    simpa [prefixWord, tailWord_3078119, baseEnd_3078119] using wordTrace_append hprefix tailTrace_3078119
  have hstable : (prefixWord ++ tailWord_3078119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078119).length < 2 ^ (prefixWord ++ tailWord_3078119).sum := by decide
  have hdescent : baseEnd_3078119 < baseStart_3078119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078141 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_3078141 : Nat := 118140960795 + 3078141 * 2 ^ 59
def prefixEnd_3078141 : Nat := 4983230072969 + 3 ^ 40 * 3078141 * 2
def baseEnd_3078141 : Nat := 1580565855311346492881393

theorem tailTrace_3078141 : CollatzResearch.WordTrace tailWord_3078141 prefixEnd_3078141 1580565855311346492881393 := by
  unfold tailWord_3078141
  simp only [CollatzResearch.WordTrace]
  refine ⟨112269025541428336474426277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74846017027618890982950851 112269025541428336474426277)
  ·
    refine ⟨21050442289017813088954927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112269025541428336474426277 21050442289017813088954927)
    ·
      refine ⟨31575663433526719633432391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21050442289017813088954927 31575663433526719633432391)
      ·
        refine ⟨47363495150290079450148587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31575663433526719633432391 47363495150290079450148587)
        ·
          refine ⟨71045242725435119175222881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47363495150290079450148587 71045242725435119175222881)
          ·
            refine ⟨53283932044076339381417161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71045242725435119175222881 53283932044076339381417161)
            ·
              refine ⟨39962949033057254536062871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53283932044076339381417161 39962949033057254536062871)
              ·
                refine ⟨59944423549585881804094307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39962949033057254536062871 59944423549585881804094307)
                ·
                  refine ⟨89916635324378822706141461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59944423549585881804094307 89916635324378822706141461)
                  ·
                    refine ⟨4214842280830257314350381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89916635324378822706141461 4214842280830257314350381)
                    ·
                      refine ⟨1580565855311346492881393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4214842280830257314350381 1580565855311346492881393)
                      ·
                        rfl

theorem cell23_3078141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_3078141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078141 prefixEnd_3078141 := by exact prefixLift 3078141
  have htrace : WordTrace (prefixWord ++ tailWord_3078141) baseStart_3078141 baseEnd_3078141 := by
    simpa [prefixWord, tailWord_3078141, baseEnd_3078141] using wordTrace_append hprefix tailTrace_3078141
  have hstable : (prefixWord ++ tailWord_3078141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078141).length < 2 ^ (prefixWord ++ tailWord_3078141).sum := by decide
  have hdescent : baseEnd_3078141 < baseStart_3078141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078171 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 3]
def baseStart_3078171 : Nat := 118140960795 + 3078171 * 2 ^ 59
def prefixEnd_3078171 : Nat := 4983230072969 + 3 ^ 40 * 3078171 * 2
def baseEnd_3078171 : Nat := 1580581259730981375506255

theorem tailTrace_3078171 : CollatzResearch.WordTrace tailWord_3078171 prefixEnd_3078171 1580581259730981375506255 := by
  unfold tailWord_3078171
  simp only [CollatzResearch.WordTrace]
  refine ⟨112270119731319651598018367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74846746487546434398678911 112270119731319651598018367)
  ·
    refine ⟨168405179596979477397027551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112270119731319651598018367 168405179596979477397027551)
    ·
      refine ⟨252607769395469216095541327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168405179596979477397027551 252607769395469216095541327)
      ·
        refine ⟨378911654093203824143311991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252607769395469216095541327 378911654093203824143311991)
        ·
          refine ⟨568367481139805736214967987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378911654093203824143311991 568367481139805736214967987)
          ·
            refine ⟨852551221709708604322451981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568367481139805736214967987 852551221709708604322451981)
            ·
              refine ⟨319706708141140726620919493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 852551221709708604322451981 319706708141140726620919493)
              ·
                refine ⟨59945007776463886241422405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319706708141140726620919493 59945007776463886241422405)
                ·
                  refine ⟨11239688958086978670266701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59945007776463886241422405 11239688958086978670266701)
                  ·
                    refine ⟨4214883359282617001350013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11239688958086978670266701 4214883359282617001350013)
                    ·
                      refine ⟨1580581259730981375506255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4214883359282617001350013 1580581259730981375506255)
                      ·
                        rfl

theorem cell23_3078171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 3].length) (baseStart_3078171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078171 prefixEnd_3078171 := by exact prefixLift 3078171
  have htrace : WordTrace (prefixWord ++ tailWord_3078171) baseStart_3078171 baseEnd_3078171 := by
    simpa [prefixWord, tailWord_3078171, baseEnd_3078171] using wordTrace_append hprefix tailTrace_3078171
  have hstable : (prefixWord ++ tailWord_3078171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078171).length < 2 ^ (prefixWord ++ tailWord_3078171).sum := by decide
  have hdescent : baseEnd_3078171 < baseStart_3078171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078211 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 4]
def baseStart_3078211 : Nat := 118140960795 + 3078211 * 2 ^ 59
def prefixEnd_3078211 : Nat := 4983230072969 + 3 ^ 40 * 3078211 * 2
def baseEnd_3078211 : Nat := 1580601798957161219006071

theorem tailTrace_3078211 : CollatzResearch.WordTrace tailWord_3078211 prefixEnd_3078211 1580601798957161219006071 := by
  unfold tailWord_3078211
  simp only [CollatzResearch.WordTrace]
  refine ⟨112271578651174738429474487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74847719100783158952982991 112271578651174738429474487)
  ·
    refine ⟨168407367976762107644211731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112271578651174738429474487 168407367976762107644211731)
    ·
      refine ⟨252611051965143161466317597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168407367976762107644211731 252611051965143161466317597)
      ·
        refine ⟨94729144486928685549869099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252611051965143161466317597 94729144486928685549869099)
        ·
          refine ⟨142093716730393028324803649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94729144486928685549869099 142093716730393028324803649)
          ·
            refine ⟨106570287547794771243602737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142093716730393028324803649 106570287547794771243602737)
            ·
              refine ⟨79927715660846078432702053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106570287547794771243602737 79927715660846078432702053)
              ·
                refine ⟨14986446686408639706131635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79927715660846078432702053 14986446686408639706131635)
                ·
                  refine ⟨22479670029612959559197453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14986446686408639706131635 22479670029612959559197453)
                  ·
                    refine ⟨8429876261104859834699045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22479670029612959559197453 8429876261104859834699045)
                    ·
                      refine ⟨1580601798957161219006071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8429876261104859834699045 1580601798957161219006071)
                      ·
                        rfl

theorem cell23_3078211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_3078211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078211 prefixEnd_3078211 := by exact prefixLift 3078211
  have htrace : WordTrace (prefixWord ++ tailWord_3078211) baseStart_3078211 baseEnd_3078211 := by
    simpa [prefixWord, tailWord_3078211, baseEnd_3078211] using wordTrace_append hprefix tailTrace_3078211
  have hstable : (prefixWord ++ tailWord_3078211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078211).length < 2 ^ (prefixWord ++ tailWord_3078211).sum := by decide
  have hdescent : baseEnd_3078211 < baseStart_3078211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078241 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_3078241 : Nat := 118140960795 + 3078241 * 2 ^ 59
def prefixEnd_3078241 : Nat := 4983230072969 + 3 ^ 40 * 3078241 * 2
def baseEnd_3078241 : Nat := 1580617203376796101630933

theorem tailTrace_3078241 : CollatzResearch.WordTrace tailWord_3078241 prefixEnd_3078241 1580617203376796101630933 := by
  unfold tailWord_3078241
  simp only [CollatzResearch.WordTrace]
  refine ⟨112272672841066053553066577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74848448560710702368711051 112272672841066053553066577)
  ·
    refine ⟨84204504630799540164799933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112272672841066053553066577 84204504630799540164799933)
    ·
      refine ⟨31576689236549827561799975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84204504630799540164799933 31576689236549827561799975)
      ·
        refine ⟨47365033854824741342699963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31576689236549827561799975 47365033854824741342699963)
        ·
          refine ⟨71047550782237112014049945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47365033854824741342699963 71047550782237112014049945)
          ·
            refine ⟨53285663086677834010537459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71047550782237112014049945 53285663086677834010537459)
            ·
              refine ⟨79928494630016751015806189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53285663086677834010537459 79928494630016751015806189)
              ·
                refine ⟨29973185486256281630927321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79928494630016751015806189 29973185486256281630927321)
                ·
                  refine ⟨22479889114692211223195491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29973185486256281630927321 22479889114692211223195491)
                  ·
                    refine ⟨33719833672038316834793237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22479889114692211223195491 33719833672038316834793237)
                    ·
                      refine ⟨1580617203376796101630933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33719833672038316834793237 1580617203376796101630933)
                      ·
                        rfl

theorem cell23_3078241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_3078241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078241 prefixEnd_3078241 := by exact prefixLift 3078241
  have htrace : WordTrace (prefixWord ++ tailWord_3078241) baseStart_3078241 baseEnd_3078241 := by
    simpa [prefixWord, tailWord_3078241, baseEnd_3078241] using wordTrace_append hprefix tailTrace_3078241
  have hstable : (prefixWord ++ tailWord_3078241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078241).length < 2 ^ (prefixWord ++ tailWord_3078241).sum := by decide
  have hdescent : baseEnd_3078241 < baseStart_3078241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078262 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_3078262 : Nat := 118140960795 + 3078262 * 2 ^ 59
def prefixEnd_3078262 : Nat := 4983230072969 + 3 ^ 40 * 3078262 * 2
def baseEnd_3078262 : Nat := 1580627986470540519468337

theorem tailTrace_3078262 : CollatzResearch.WordTrace tailWord_3078262 prefixEnd_3078262 1580627986470540519468337 := by
  unfold tailWord_3078262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017089923374373383723815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74848959182659982759720693 7017089923374373383723815)
  ·
    refine ⟨10525634885061560075585723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7017089923374373383723815 10525634885061560075585723)
    ·
      refine ⟨15788452327592340113378585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10525634885061560075585723 15788452327592340113378585)
      ·
        refine ⟨11841339245694255085033939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15788452327592340113378585 11841339245694255085033939)
        ·
          refine ⟨17762008868541382627550909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11841339245694255085033939 17762008868541382627550909)
          ·
            refine ⟨6660753325703018485331591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17762008868541382627550909 6660753325703018485331591)
            ·
              refine ⟨9991129988554527727997387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6660753325703018485331591 9991129988554527727997387)
              ·
                refine ⟨14986694982831791591996081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9991129988554527727997387 14986694982831791591996081)
                ·
                  refine ⟨11240021237123843693997061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14986694982831791591996081 11240021237123843693997061)
                  ·
                    refine ⟨2107503981960720692624449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11240021237123843693997061 2107503981960720692624449)
                    ·
                      refine ⟨1580627986470540519468337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2107503981960720692624449 1580627986470540519468337)
                      ·
                        rfl

theorem cell23_3078262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_3078262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078262 prefixEnd_3078262 := by exact prefixLift 3078262
  have htrace : WordTrace (prefixWord ++ tailWord_3078262) baseStart_3078262 baseEnd_3078262 := by
    simpa [prefixWord, tailWord_3078262, baseEnd_3078262] using wordTrace_append hprefix tailTrace_3078262
  have hstable : (prefixWord ++ tailWord_3078262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078262).length < 2 ^ (prefixWord ++ tailWord_3078262).sum := by decide
  have hdescent : baseEnd_3078262 < baseStart_3078262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078268 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 6]
def baseStart_3078268 : Nat := 118140960795 + 3078268 * 2 ^ 59
def prefixEnd_3078268 : Nat := 4983230072969 + 3 ^ 40 * 3078268 * 2
def baseEnd_3078268 : Nat := 175625674150496388443701

theorem tailTrace_3078268 : CollatzResearch.WordTrace tailWord_3078268 prefixEnd_3078268 175625674150496388443701 := by
  unfold tailWord_3078268
  simp only [CollatzResearch.WordTrace]
  refine ⟨56136828805984118582149729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74849105074645491442866305 56136828805984118582149729)
  ·
    refine ⟨42102621604488088936612297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56136828805984118582149729 42102621604488088936612297)
    ·
      refine ⟨31576966203366066702459223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42102621604488088936612297 31576966203366066702459223)
      ·
        refine ⟨47365449305049100053688835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31576966203366066702459223 47365449305049100053688835)
        ·
          refine ⟨71048173957573650080533253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47365449305049100053688835 71048173957573650080533253)
          ·
            refine ⟨13321532617045059390099985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71048173957573650080533253 13321532617045059390099985)
            ·
              refine ⟨9991149462783794542574989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13321532617045059390099985 9991149462783794542574989)
              ·
                refine ⟨3746681048543922953465621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9991149462783794542574989 3746681048543922953465621)
                ·
                  refine ⟨175625674150496388443701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3746681048543922953465621 175625674150496388443701)
                  ·
                    rfl

theorem cell23_3078268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_3078268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078268 prefixEnd_3078268 := by exact prefixLift 3078268
  have htrace : WordTrace (prefixWord ++ tailWord_3078268) baseStart_3078268 baseEnd_3078268 := by
    simpa [prefixWord, tailWord_3078268, baseEnd_3078268] using wordTrace_append hprefix tailTrace_3078268
  have hstable : (prefixWord ++ tailWord_3078268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078268).length < 2 ^ (prefixWord ++ tailWord_3078268).sum := by decide
  have hdescent : baseEnd_3078268 < baseStart_3078268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078282 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3078282 : Nat := 118140960795 + 3078282 * 2 ^ 59
def prefixEnd_3078282 : Nat := 4983230072969 + 3 ^ 40 * 3078282 * 2
def baseEnd_3078282 : Nat := 1580638256083630441218245

theorem tailTrace_3078282 : CollatzResearch.WordTrace tailWord_3078282 prefixEnd_3078282 1580638256083630441218245 := by
  unfold tailWord_3078282
  simp only [CollatzResearch.WordTrace]
  refine ⟨28068542058479379388827275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74849445489278345036872733 28068542058479379388827275)
  ·
    refine ⟨42102813087719069083240913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28068542058479379388827275 42102813087719069083240913)
    ·
      refine ⟨31577109815789301812430685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42102813087719069083240913 31577109815789301812430685)
      ·
        refine ⟨11841416180920988179661507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31577109815789301812430685 11841416180920988179661507)
        ·
          refine ⟨17762124271381482269492261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11841416180920988179661507 17762124271381482269492261)
          ·
            refine ⟨3330398300884027925529799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17762124271381482269492261 3330398300884027925529799)
            ·
              refine ⟨4995597451326041888294699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330398300884027925529799 4995597451326041888294699)
              ·
                refine ⟨7493396176989062832442049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4995597451326041888294699 7493396176989062832442049)
                ·
                  refine ⟨5620047132741797124331537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7493396176989062832442049 5620047132741797124331537)
                  ·
                    refine ⟨4215035349556347843248653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5620047132741797124331537 4215035349556347843248653)
                    ·
                      refine ⟨1580638256083630441218245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4215035349556347843248653 1580638256083630441218245)
                      ·
                        rfl

theorem cell23_3078282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3078282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078282 prefixEnd_3078282 := by exact prefixLift 3078282
  have htrace : WordTrace (prefixWord ++ tailWord_3078282) baseStart_3078282 baseEnd_3078282 := by
    simpa [prefixWord, tailWord_3078282, baseEnd_3078282] using wordTrace_append hprefix tailTrace_3078282
  have hstable : (prefixWord ++ tailWord_3078282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078282).length < 2 ^ (prefixWord ++ tailWord_3078282).sum := by decide
  have hdescent : baseEnd_3078282 < baseStart_3078282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078291 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 5]
def baseStart_3078291 : Nat := 118140960795 + 3078291 * 2 ^ 59
def prefixEnd_3078291 : Nat := 4983230072969 + 3 ^ 40 * 3078291 * 2
def baseEnd_3078291 : Nat := 1580642877409520906005703

theorem tailTrace_3078291 : CollatzResearch.WordTrace tailWord_3078291 prefixEnd_3078291 1580642877409520906005703 := by
  unfold tailWord_3078291
  simp only [CollatzResearch.WordTrace]
  refine ⟨112274496490884912092386727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74849664327256608061591151 112274496490884912092386727)
  ·
    refine ⟨168411744736327368138580091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112274496490884912092386727 168411744736327368138580091)
    ·
      refine ⟨252617617104491052207870137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168411744736327368138580091 252617617104491052207870137)
      ·
        refine ⟨189463212828368289155902603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252617617104491052207870137 189463212828368289155902603)
        ·
          refine ⟨284194819242552433733853905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189463212828368289155902603 284194819242552433733853905)
          ·
            refine ⟨213146114431914325300390429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284194819242552433733853905 213146114431914325300390429)
            ·
              refine ⟨79929792911967871987646411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213146114431914325300390429 79929792911967871987646411)
              ·
                refine ⟨119894689367951807981469617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79929792911967871987646411 119894689367951807981469617)
                ·
                  refine ⟨89921017025963855986102213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119894689367951807981469617 89921017025963855986102213)
                  ·
                    refine ⟨16860190692368222997394165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89921017025963855986102213 16860190692368222997394165)
                    ·
                      refine ⟨1580642877409520906005703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16860190692368222997394165 1580642877409520906005703)
                      ·
                        rfl

theorem cell23_3078291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_3078291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078291 prefixEnd_3078291 := by exact prefixLift 3078291
  have htrace : WordTrace (prefixWord ++ tailWord_3078291) baseStart_3078291 baseEnd_3078291 := by
    simpa [prefixWord, tailWord_3078291, baseEnd_3078291] using wordTrace_append hprefix tailTrace_3078291
  have hstable : (prefixWord ++ tailWord_3078291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078291).length < 2 ^ (prefixWord ++ tailWord_3078291).sum := by decide
  have hdescent : baseEnd_3078291 < baseStart_3078291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078332 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_3078332 : Nat := 118140960795 + 3078332 * 2 ^ 59
def prefixEnd_3078332 : Nat := 4983230072969 + 3 ^ 40 * 3078332 * 2
def baseEnd_3078332 : Nat := 526887976705451748531005

theorem tailTrace_3078332 : CollatzResearch.WordTrace tailWord_3078332 prefixEnd_3078332 526887976705451748531005 := by
  unfold tailWord_3078332
  simp only [CollatzResearch.WordTrace]
  refine ⟨56137995941868188047314625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74850661255824250729752833 56137995941868188047314625)
  ·
    refine ⟨42103496956401141035485969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56137995941868188047314625 42103496956401141035485969)
    ·
      refine ⟨31577622717300855776614477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42103496956401141035485969 31577622717300855776614477)
      ·
        refine ⟨11841608518987820916230429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31577622717300855776614477 11841608518987820916230429)
        ·
          refine ⟨4440603194620432843586411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11841608518987820916230429 4440603194620432843586411)
          ·
            refine ⟨6660904791930649265379617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4440603194620432843586411 6660904791930649265379617)
            ·
              refine ⟨4995678593947986949034713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6660904791930649265379617 4995678593947986949034713)
              ·
                refine ⟨3746758945460990211776035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4995678593947986949034713 3746758945460990211776035)
                ·
                  refine ⟨5620138418191485317664053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3746758945460990211776035 5620138418191485317664053)
                  ·
                    refine ⟨526887976705451748531005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5620138418191485317664053 526887976705451748531005)
                    ·
                      rfl

theorem cell23_3078332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_3078332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078332 prefixEnd_3078332 := by exact prefixLift 3078332
  have htrace : WordTrace (prefixWord ++ tailWord_3078332) baseStart_3078332 baseEnd_3078332 := by
    simpa [prefixWord, tailWord_3078332, baseEnd_3078332] using wordTrace_append hprefix tailTrace_3078332
  have hstable : (prefixWord ++ tailWord_3078332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078332).length < 2 ^ (prefixWord ++ tailWord_3078332).sum := by decide
  have hdescent : baseEnd_3078332 < baseStart_3078332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078365 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3078365 : Nat := 118140960795 + 3078365 * 2 ^ 59
def prefixEnd_3078365 : Nat := 4983230072969 + 3 ^ 40 * 3078365 * 2
def baseEnd_3078365 : Nat := 1580680874977953616480363

theorem tailTrace_3078365 : CollatzResearch.WordTrace tailWord_3078365 prefixEnd_3078365 1580680874977953616480363 := by
  unfold tailWord_3078365
  simp only [CollatzResearch.WordTrace]
  refine ⟨112277195492616822730580549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74851463661744548487053699 112277195492616822730580549)
  ·
    refine ⟨21051974154865654261983853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112277195492616822730580549 21051974154865654261983853)
    ·
      refine ⟨7894490308074620348243945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21051974154865654261983853 7894490308074620348243945)
      ·
        refine ⟨5920867731055965261182959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7894490308074620348243945 5920867731055965261182959)
        ·
          refine ⟨8881301596583947891774439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5920867731055965261182959 8881301596583947891774439)
          ·
            refine ⟨13321952394875921837661659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8881301596583947891774439 13321952394875921837661659)
            ·
              refine ⟨19982928592313882756492489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13321952394875921837661659 19982928592313882756492489)
              ·
                refine ⟨14987196444235412067369367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19982928592313882756492489 14987196444235412067369367)
                ·
                  refine ⟨22480794666353118101054051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14987196444235412067369367 22480794666353118101054051)
                  ·
                    refine ⟨33721191999529677151581077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22480794666353118101054051 33721191999529677151581077)
                    ·
                      refine ⟨1580680874977953616480363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33721191999529677151581077 1580680874977953616480363)
                      ·
                        rfl

theorem cell23_3078365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3078365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078365 prefixEnd_3078365 := by exact prefixLift 3078365
  have htrace : WordTrace (prefixWord ++ tailWord_3078365) baseStart_3078365 baseEnd_3078365 := by
    simpa [prefixWord, tailWord_3078365, baseEnd_3078365] using wordTrace_append hprefix tailTrace_3078365
  have hstable : (prefixWord ++ tailWord_3078365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078365).length < 2 ^ (prefixWord ++ tailWord_3078365).sum := by decide
  have hdescent : baseEnd_3078365 < baseStart_3078365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078375 : List Nat := [1, 1, 5, 3, 1, 2, 2, 8]
def baseStart_3078375 : Nat := 118140960795 + 3078375 * 2 ^ 59
def prefixEnd_3078375 : Nat := 4983230072969 + 3 ^ 40 * 3078375 * 2
def baseEnd_3078375 : Nat := 58543926288314762124271

theorem tailTrace_3078375 : CollatzResearch.WordTrace tailWord_3078375 prefixEnd_3078375 58543926288314762124271 := by
  unfold tailWord_3078375
  simp only [CollatzResearch.WordTrace]
  refine ⟨112277560222580594438444579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74851706815053729625629719 112277560222580594438444579)
  ·
    refine ⟨168416340333870891657666869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112277560222580594438444579 168416340333870891657666869)
    ·
      refine ⟨15789031906300396092906269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168416340333870891657666869 15789031906300396092906269)
      ·
        refine ⟨5920886964862648534839851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15789031906300396092906269 5920886964862648534839851)
        ·
          refine ⟨8881330447293972802259777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5920886964862648534839851 8881330447293972802259777)
          ·
            refine ⟨6660997835470479601694833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8881330447293972802259777 6660997835470479601694833)
            ·
              refine ⟨4995748376602859701271125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6660997835470479601694833 4995748376602859701271125)
              ·
                refine ⟨58543926288314762124271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4995748376602859701271125 58543926288314762124271)
                ·
                  rfl

theorem cell23_3078375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 8].length) (baseStart_3078375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078375 prefixEnd_3078375 := by exact prefixLift 3078375
  have htrace : WordTrace (prefixWord ++ tailWord_3078375) baseStart_3078375 baseEnd_3078375 := by
    simpa [prefixWord, tailWord_3078375, baseEnd_3078375] using wordTrace_append hprefix tailTrace_3078375
  have hstable : (prefixWord ++ tailWord_3078375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078375).length < 2 ^ (prefixWord ++ tailWord_3078375).sum := by decide
  have hdescent : baseEnd_3078375 < baseStart_3078375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078378 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3078378 : Nat := 118140960795 + 3078378 * 2 ^ 59
def prefixEnd_3078378 : Nat := 4983230072969 + 3 ^ 40 * 3078378 * 2
def baseEnd_3078378 : Nat := 1580687550226462065617803

theorem tailTrace_3078378 : CollatzResearch.WordTrace tailWord_3078378 prefixEnd_3078378 1580687550226462065617803 := by
  unfold tailWord_3078378
  simp only [CollatzResearch.WordTrace]
  refine ⟨28069417410392431487700947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74851779761046483967202525 28069417410392431487700947)
  ·
    refine ⟨42104126115588647231551421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28069417410392431487700947 42104126115588647231551421)
    ·
      refine ⟨15789047293345742711831783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42104126115588647231551421 15789047293345742711831783)
      ·
        refine ⟨23683570940018614067747675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15789047293345742711831783 23683570940018614067747675)
        ·
          refine ⟨35525356410027921101621513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23683570940018614067747675 35525356410027921101621513)
          ·
            refine ⟨26644017307520940826216135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35525356410027921101621513 26644017307520940826216135)
            ·
              refine ⟨39966025961281411239324203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26644017307520940826216135 39966025961281411239324203)
              ·
                refine ⟨59949038941922116858986305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39966025961281411239324203 59949038941922116858986305)
                ·
                  refine ⟨44961779206441587644239729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59949038941922116858986305 44961779206441587644239729)
                  ·
                    refine ⟨33721334404831190733179797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44961779206441587644239729 33721334404831190733179797)
                    ·
                      refine ⟨1580687550226462065617803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33721334404831190733179797 1580687550226462065617803)
                      ·
                        rfl

theorem cell23_3078378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3078378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078378 prefixEnd_3078378 := by exact prefixLift 3078378
  have htrace : WordTrace (prefixWord ++ tailWord_3078378) baseStart_3078378 baseEnd_3078378 := by
    simpa [prefixWord, tailWord_3078378, baseEnd_3078378] using wordTrace_append hprefix tailTrace_3078378
  have hstable : (prefixWord ++ tailWord_3078378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078378).length < 2 ^ (prefixWord ++ tailWord_3078378).sum := by decide
  have hdescent : baseEnd_3078378 < baseStart_3078378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078402 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3078402 : Nat := 118140960795 + 3078402 * 2 ^ 59
def prefixEnd_3078402 : Nat := 4983230072969 + 3 ^ 40 * 3078402 * 2
def baseEnd_3078402 : Nat := 1580699873762169971717693

theorem tailTrace_3078402 : CollatzResearch.WordTrace tailWord_3078402 prefixEnd_3078402 1580699873762169971717693 := by
  unfold tailWord_3078402
  simp only [CollatzResearch.WordTrace]
  refine ⟨28069636248370694512419365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74852363328988518699784973 28069636248370694512419365)
  ·
    refine ⟨5263056796569505221078631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28069636248370694512419365 5263056796569505221078631)
    ·
      refine ⟨7894585194854257831617947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5263056796569505221078631 7894585194854257831617947)
      ·
        refine ⟨11841877792281386747426921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7894585194854257831617947 11841877792281386747426921)
        ·
          refine ⟨8881408344211040060570191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11841877792281386747426921 8881408344211040060570191)
          ·
            refine ⟨13322112516316560090855287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8881408344211040060570191 13322112516316560090855287)
            ·
              refine ⟨19983168774474840136282931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13322112516316560090855287 19983168774474840136282931)
              ·
                refine ⟨29974753161712260204424397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19983168774474840136282931 29974753161712260204424397)
                ·
                  refine ⟨11240532435642097576659149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29974753161712260204424397 11240532435642097576659149)
                  ·
                    refine ⟨4215199663365786591247181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11240532435642097576659149 4215199663365786591247181)
                    ·
                      refine ⟨1580699873762169971717693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4215199663365786591247181 1580699873762169971717693)
                      ·
                        rfl

theorem cell23_3078402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3078402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078402 prefixEnd_3078402 := by exact prefixLift 3078402
  have htrace : WordTrace (prefixWord ++ tailWord_3078402) baseStart_3078402 baseEnd_3078402 := by
    simpa [prefixWord, tailWord_3078402, baseEnd_3078402] using wordTrace_append hprefix tailTrace_3078402
  have hstable : (prefixWord ++ tailWord_3078402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078402).length < 2 ^ (prefixWord ++ tailWord_3078402).sum := by decide
  have hdescent : baseEnd_3078402 < baseStart_3078402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078482 : List Nat := [3, 2, 2, 1, 1, 1, 4, 4, 5]
def baseStart_3078482 : Nat := 118140960795 + 3078482 * 2 ^ 59
def prefixEnd_3078482 : Nat := 4983230072969 + 3 ^ 40 * 3078482 * 2
def baseEnd_3078482 : Nat := 175637883579392184301925

theorem tailTrace_3078482 : CollatzResearch.WordTrace tailWord_3078482 prefixEnd_3078482 175637883579392184301925 := by
  unfold tailWord_3078482
  simp only [CollatzResearch.WordTrace]
  refine ⟨28070365708298237928147425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74854308555461967808393133 28070365708298237928147425)
  ·
    refine ⟨21052774281223678446110569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28070365708298237928147425 21052774281223678446110569)
    ·
      refine ⟨15789580710917758834582927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21052774281223678446110569 15789580710917758834582927)
      ·
        refine ⟨23684371066376638251874391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15789580710917758834582927 23684371066376638251874391)
        ·
          refine ⟨35526556599564957377811587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23684371066376638251874391 35526556599564957377811587)
          ·
            refine ⟨53289834899347436066717381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35526556599564957377811587 53289834899347436066717381)
            ·
              refine ⟨9991844043627644262509509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53289834899347436066717381 9991844043627644262509509)
              ·
                refine ⟨1873470758180183299220533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9991844043627644262509509 1873470758180183299220533)
                ·
                  refine ⟨175637883579392184301925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1873470758180183299220533 175637883579392184301925)
                  ·
                    rfl

theorem cell23_3078482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_3078482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078482 prefixEnd_3078482 := by exact prefixLift 3078482
  have htrace : WordTrace (prefixWord ++ tailWord_3078482) baseStart_3078482 baseEnd_3078482 := by
    simpa [prefixWord, tailWord_3078482, baseEnd_3078482] using wordTrace_append hprefix tailTrace_3078482
  have hstable : (prefixWord ++ tailWord_3078482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078482).length < 2 ^ (prefixWord ++ tailWord_3078482).sum := by decide
  have hdescent : baseEnd_3078482 < baseStart_3078482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078532 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_3078532 : Nat := 118140960795 + 3078532 * 2 ^ 59
def prefixEnd_3078532 : Nat := 4983230072969 + 3 ^ 40 * 3078532 * 2
def baseEnd_3078532 : Nat := 1580766626247254463092095

theorem tailTrace_3078532 : CollatzResearch.WordTrace tailWord_3078532 prefixEnd_3078532 1580766626247254463092095 := by
  unfold tailWord_3078532
  simp only [CollatzResearch.WordTrace]
  refine ⟨56141643241505905125954925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74855524322007873501273233 56141643241505905125954925)
  ·
    refine ⟨21053116215564714422233097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56141643241505905125954925 21053116215564714422233097)
    ·
      refine ⟨15789837161673535816674823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21053116215564714422233097 15789837161673535816674823)
      ·
        refine ⟨23684755742510303725012235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15789837161673535816674823 23684755742510303725012235)
        ·
          refine ⟨35527133613765455587518353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23684755742510303725012235 35527133613765455587518353)
          ·
            refine ⟨26645350210324091690638765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35527133613765455587518353 26645350210324091690638765)
            ·
              refine ⟨9992006328871534383989537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26645350210324091690638765 9992006328871534383989537)
              ·
                refine ⟨7494004746653650787992153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9992006328871534383989537 7494004746653650787992153)
                ·
                  refine ⟨5620503559990238090994115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7494004746653650787992153 5620503559990238090994115)
                  ·
                    refine ⟨8430755339985357136491173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5620503559990238090994115 8430755339985357136491173)
                    ·
                      refine ⟨1580766626247254463092095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8430755339985357136491173 1580766626247254463092095)
                      ·
                        rfl

theorem cell23_3078532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_3078532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078532 prefixEnd_3078532 := by exact prefixLift 3078532
  have htrace : WordTrace (prefixWord ++ tailWord_3078532) baseStart_3078532 baseEnd_3078532 := by
    simpa [prefixWord, tailWord_3078532, baseEnd_3078532] using wordTrace_append hprefix tailTrace_3078532
  have hstable : (prefixWord ++ tailWord_3078532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078532).length < 2 ^ (prefixWord ++ tailWord_3078532).sum := by decide
  have hdescent : baseEnd_3078532 < baseStart_3078532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078592 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 3, 5, 2]
def baseStart_3078592 : Nat := 118140960795 + 3078592 * 2 ^ 59
def prefixEnd_3078592 : Nat := 4983230072969 + 3 ^ 40 * 3078592 * 2
def baseEnd_3078592 : Nat := 1580797435086524228341819

theorem tailTrace_3078592 : CollatzResearch.WordTrace tailWord_3078592 prefixEnd_3078592 1580797435086524228341819 := by
  unfold tailWord_3078592
  simp only [CollatzResearch.WordTrace]
  refine ⟨56142737431397220249547015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74856983241862960332729353 56142737431397220249547015)
  ·
    refine ⟨84214106147095830374320523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56142737431397220249547015 84214106147095830374320523)
    ·
      refine ⟨126321159220643745561480785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84214106147095830374320523 126321159220643745561480785)
      ·
        refine ⟨94740869415482809171110589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126321159220643745561480785 94740869415482809171110589)
        ·
          refine ⟨35527826030806053439166471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94740869415482809171110589 35527826030806053439166471)
          ·
            refine ⟨53291739046209080158749707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35527826030806053439166471 53291739046209080158749707)
            ·
              refine ⟨79937608569313620238124561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53291739046209080158749707 79937608569313620238124561)
              ·
                refine ⟨59953206426985215178593421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79937608569313620238124561 59953206426985215178593421)
                ·
                  refine ⟨22482452410119455691972533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59953206426985215178593421 22482452410119455691972533)
                  ·
                    refine ⟨2107729913448698971122425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22482452410119455691972533 2107729913448698971122425)
                    ·
                      refine ⟨1580797435086524228341819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2107729913448698971122425 1580797435086524228341819)
                      ·
                        rfl

theorem cell23_3078592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_3078592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078592 prefixEnd_3078592 := by exact prefixLift 3078592
  have htrace : WordTrace (prefixWord ++ tailWord_3078592) baseStart_3078592 baseEnd_3078592 := by
    simpa [prefixWord, tailWord_3078592, baseEnd_3078592] using wordTrace_append hprefix tailTrace_3078592
  have hstable : (prefixWord ++ tailWord_3078592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078592).length < 2 ^ (prefixWord ++ tailWord_3078592).sum := by decide
  have hdescent : baseEnd_3078592 < baseStart_3078592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078632 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 1, 6]
def baseStart_3078632 : Nat := 118140960795 + 3078632 * 2 ^ 59
def prefixEnd_3078632 : Nat := 4983230072969 + 3 ^ 40 * 3078632 * 2
def baseEnd_3078632 : Nat := 526939324770901357280545

theorem tailTrace_3078632 : CollatzResearch.WordTrace tailWord_3078632 prefixEnd_3078632 526939324770901357280545 := by
  unfold tailWord_3078632
  simp only [CollatzResearch.WordTrace]
  refine ⟨56143466891324763665275075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74857955855099684887033433 56143466891324763665275075)
  ·
    refine ⟨84215200336987145497912613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56143466891324763665275075 84215200336987145497912613)
    ·
      refine ⟨15790350063185089780858615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84215200336987145497912613 15790350063185089780858615)
      ·
        refine ⟨23685525094777634671287923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15790350063185089780858615 23685525094777634671287923)
        ·
          refine ⟨35528287642166452006931885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23685525094777634671287923 35528287642166452006931885)
          ·
            refine ⟨13323107865812419502599457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35528287642166452006931885 13323107865812419502599457)
            ·
              refine ⟨9992330899359314626949593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13323107865812419502599457 9992330899359314626949593)
              ·
                refine ⟨7494248174519485970212195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9992330899359314626949593 7494248174519485970212195)
                ·
                  refine ⟨11241372261779228955318293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7494248174519485970212195 11241372261779228955318293)
                  ·
                    refine ⟨526939324770901357280545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11241372261779228955318293 526939324770901357280545)
                    ·
                      rfl

theorem cell23_3078632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_3078632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078632 prefixEnd_3078632 := by exact prefixLift 3078632
  have htrace : WordTrace (prefixWord ++ tailWord_3078632) baseStart_3078632 baseEnd_3078632 := by
    simpa [prefixWord, tailWord_3078632, baseEnd_3078632] using wordTrace_append hprefix tailTrace_3078632
  have hstable : (prefixWord ++ tailWord_3078632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078632).length < 2 ^ (prefixWord ++ tailWord_3078632).sum := by decide
  have hdescent : baseEnd_3078632 < baseStart_3078632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078639 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 7, 2, 2]
def baseStart_3078639 : Nat := 118140960795 + 3078639 * 2 ^ 59
def prefixEnd_3078639 : Nat := 4983230072969 + 3 ^ 40 * 3078639 * 2
def baseEnd_3078639 : Nat := 1580821568677285544454103

theorem tailTrace_3078639 : CollatzResearch.WordTrace tailWord_3078639 prefixEnd_3078639 1580821568677285544454103 := by
  unfold tailWord_3078639
  simp only [CollatzResearch.WordTrace]
  refine ⟨112287189093624167526054971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74858126062416111684036647 112287189093624167526054971)
  ·
    refine ⟨168430783640436251289082457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112287189093624167526054971 168430783640436251289082457)
    ·
      refine ⟨126323087730327188466811843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168430783640436251289082457 126323087730327188466811843)
      ·
        refine ⟨189484631595490782700217765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126323087730327188466811843 189484631595490782700217765)
        ·
          refine ⟨35528368424154521756290831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189484631595490782700217765 35528368424154521756290831)
          ·
            refine ⟨53292552636231782634436247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35528368424154521756290831 53292552636231782634436247)
            ·
              refine ⟨79938828954347673951654371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53292552636231782634436247 79938828954347673951654371)
              ·
                refine ⟨119908243431521510927481557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79938828954347673951654371 119908243431521510927481557)
                ·
                  refine ⟨2810349455426285412362849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119908243431521510927481557 2810349455426285412362849)
                  ·
                    refine ⟨2107762091569714059272137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2810349455426285412362849 2107762091569714059272137)
                    ·
                      refine ⟨1580821568677285544454103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2107762091569714059272137 1580821568677285544454103)
                      ·
                        rfl

theorem cell23_3078639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 2, 2].length) (baseStart_3078639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078639 prefixEnd_3078639 := by exact prefixLift 3078639
  have htrace : WordTrace (prefixWord ++ tailWord_3078639) baseStart_3078639 baseEnd_3078639 := by
    simpa [prefixWord, tailWord_3078639, baseEnd_3078639] using wordTrace_append hprefix tailTrace_3078639
  have hstable : (prefixWord ++ tailWord_3078639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078639).length < 2 ^ (prefixWord ++ tailWord_3078639).sum := by decide
  have hdescent : baseEnd_3078639 < baseStart_3078639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078649 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 2, 4]
def baseStart_3078649 : Nat := 118140960795 + 3078649 * 2 ^ 59
def prefixEnd_3078649 : Nat := 4983230072969 + 3 ^ 40 * 3078649 * 2
def baseEnd_3078649 : Nat := 526942234494610168443019

theorem tailTrace_3078649 : CollatzResearch.WordTrace tailWord_3078649 prefixEnd_3078649 526942234494610168443019 := by
  unfold tailWord_3078649
  simp only [CollatzResearch.WordTrace]
  refine ⟨112287553823587939233919001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74858369215725292822612667 112287553823587939233919001)
  ·
    refine ⟨84215665367690954425439251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112287553823587939233919001 84215665367690954425439251)
    ·
      refine ⟨126323498051536431638158877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84215665367690954425439251 126323498051536431638158877)
      ·
        refine ⟨47371311769326161864309579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126323498051536431638158877 47371311769326161864309579)
        ·
          refine ⟨71056967653989242796464369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47371311769326161864309579 71056967653989242796464369)
          ·
            refine ⟨53292725740491932097348277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71056967653989242796464369 53292725740491932097348277)
            ·
              refine ⟨4996193038171118634126401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53292725740491932097348277 4996193038171118634126401)
              ·
                refine ⟨3747144778628338975594801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4996193038171118634126401 3747144778628338975594801)
                ·
                  refine ⟨2810358583971254231696101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3747144778628338975594801 2810358583971254231696101)
                  ·
                    refine ⟨526942234494610168443019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2810358583971254231696101 526942234494610168443019)
                    ·
                      rfl

theorem cell23_3078649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 4].length) (baseStart_3078649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078649 prefixEnd_3078649 := by exact prefixLift 3078649
  have htrace : WordTrace (prefixWord ++ tailWord_3078649) baseStart_3078649 baseEnd_3078649 := by
    simpa [prefixWord, tailWord_3078649, baseEnd_3078649] using wordTrace_append hprefix tailTrace_3078649
  have hstable : (prefixWord ++ tailWord_3078649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078649).length < 2 ^ (prefixWord ++ tailWord_3078649).sum := by decide
  have hdescent : baseEnd_3078649 < baseStart_3078649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078665 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_3078665 : Nat := 118140960795 + 3078665 * 2 ^ 59
def prefixEnd_3078665 : Nat := 4983230072969 + 3 ^ 40 * 3078665 * 2
def baseEnd_3078665 : Nat := 1580834919174302442728983

theorem tailTrace_3078665 : CollatzResearch.WordTrace tailWord_3078665 prefixEnd_3078665 1580834919174302442728983 := by
  unfold tailWord_3078665
  simp only [CollatzResearch.WordTrace]
  refine ⟨112288137391529973966501449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74858758261019982644334299 112288137391529973966501449)
  ·
    refine ⟨84216103043647480474876087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112288137391529973966501449 84216103043647480474876087)
    ·
      refine ⟨126324154565471220712314131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84216103043647480474876087 126324154565471220712314131)
      ·
        refine ⟨189486231848206831068471197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126324154565471220712314131 189486231848206831068471197)
        ·
          refine ⟨71057336943077561650676699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189486231848206831068471197 71057336943077561650676699)
          ·
            refine ⟨106586005414616342476015049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71057336943077561650676699 106586005414616342476015049)
            ·
              refine ⟨79939504060962256857011287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106586005414616342476015049 79939504060962256857011287)
              ·
                refine ⟨119909256091443385285516931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79939504060962256857011287 119909256091443385285516931)
                ·
                  refine ⟨179863884137165077928275397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119909256091443385285516931 179863884137165077928275397)
                  ·
                    refine ⟨33724478275718452111551637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179863884137165077928275397 33724478275718452111551637)
                    ·
                      refine ⟨1580834919174302442728983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33724478275718452111551637 1580834919174302442728983)
                      ·
                        rfl

theorem cell23_3078665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_3078665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078665 prefixEnd_3078665 := by exact prefixLift 3078665
  have htrace : WordTrace (prefixWord ++ tailWord_3078665) baseStart_3078665 baseEnd_3078665 := by
    simpa [prefixWord, tailWord_3078665, baseEnd_3078665] using wordTrace_append hprefix tailTrace_3078665
  have hstable : (prefixWord ++ tailWord_3078665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078665).length < 2 ^ (prefixWord ++ tailWord_3078665).sum := by decide
  have hdescent : baseEnd_3078665 < baseStart_3078665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078666 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 2, 4]
def baseStart_3078666 : Nat := 118140960795 + 3078666 * 2 ^ 59
def prefixEnd_3078666 : Nat := 4983230072969 + 3 ^ 40 * 3078666 * 2
def baseEnd_3078666 : Nat := 526945144218318979605493

theorem tailTrace_3078666 : CollatzResearch.WordTrace tailWord_3078666 prefixEnd_3078666 526945144218318979605493 := by
  unfold tailWord_3078666
  simp only [CollatzResearch.WordTrace]
  refine ⟨28072043466131587784321963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74858782576350900758191901 28072043466131587784321963)
  ·
    refine ⟨42108065199197381676482945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28072043466131587784321963 42108065199197381676482945)
    ·
      refine ⟨31581048899398036257362209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42108065199197381676482945 31581048899398036257362209)
      ·
        refine ⟨23685786674548527193021657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31581048899398036257362209 23685786674548527193021657)
        ·
          refine ⟨17764340005911395394766243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23685786674548527193021657 17764340005911395394766243)
          ·
            refine ⟨26646510008867093092149365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17764340005911395394766243 26646510008867093092149365)
            ·
              refine ⟨2498110313331289977389003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26646510008867093092149365 2498110313331289977389003)
              ·
                refine ⟨3747165469996934966083505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498110313331289977389003 3747165469996934966083505)
                ·
                  refine ⟨2810374102497701224562629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3747165469996934966083505 2810374102497701224562629)
                  ·
                    refine ⟨526945144218318979605493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2810374102497701224562629 526945144218318979605493)
                    ·
                      rfl

theorem cell23_3078666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_3078666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078666 prefixEnd_3078666 := by exact prefixLift 3078666
  have htrace : WordTrace (prefixWord ++ tailWord_3078666) baseStart_3078666 baseEnd_3078666 := by
    simpa [prefixWord, tailWord_3078666, baseEnd_3078666] using wordTrace_append hprefix tailTrace_3078666
  have hstable : (prefixWord ++ tailWord_3078666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078666).length < 2 ^ (prefixWord ++ tailWord_3078666).sum := by decide
  have hdescent : baseEnd_3078666 < baseStart_3078666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078679 : List Nat := [1, 1, 3, 6, 1, 1, 1, 9]
def baseStart_3078679 : Nat := 118140960795 + 3078679 * 2 ^ 59
def prefixEnd_3078679 : Nat := 4983230072969 + 3 ^ 40 * 3078679 * 2
def baseEnd_3078679 : Nat := 58549707700128347701997

theorem tailTrace_3078679 : CollatzResearch.WordTrace tailWord_3078679 prefixEnd_3078679 58549707700128347701997 := by
  unfold tailWord_3078679
  simp only [CollatzResearch.WordTrace]
  refine ⟨112288648013479254357511091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74859098675652836238340727 112288648013479254357511091)
  ·
    refine ⟨168432972020218881536266637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112288648013479254357511091 168432972020218881536266637)
    ·
      refine ⟨63162364507582080576099989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168432972020218881536266637 63162364507582080576099989)
      ·
        refine ⟨2960735836292910027004687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63162364507582080576099989 2960735836292910027004687)
        ·
          refine ⟨4441103754439365040507031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2960735836292910027004687 4441103754439365040507031)
          ·
            refine ⟨6661655631659047560760547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4441103754439365040507031 6661655631659047560760547)
            ·
              refine ⟨9992483447488571341140821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6661655631659047560760547 9992483447488571341140821)
              ·
                refine ⟨58549707700128347701997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9992483447488571341140821 58549707700128347701997)
                ·
                  rfl

theorem cell23_3078679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 9].length) (baseStart_3078679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078679 prefixEnd_3078679 := by exact prefixLift 3078679
  have htrace : WordTrace (prefixWord ++ tailWord_3078679) baseStart_3078679 baseEnd_3078679 := by
    simpa [prefixWord, tailWord_3078679, baseEnd_3078679] using wordTrace_append hprefix tailTrace_3078679
  have hstable : (prefixWord ++ tailWord_3078679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078679).length < 2 ^ (prefixWord ++ tailWord_3078679).sum := by decide
  have hdescent : baseEnd_3078679 < baseStart_3078679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078689 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_3078689 : Nat := 118140960795 + 3078689 * 2 ^ 59
def prefixEnd_3078689 : Nat := 4983230072969 + 3 ^ 40 * 3078689 * 2
def baseEnd_3078689 : Nat := 1580847242710010348828873

theorem tailTrace_3078689 : CollatzResearch.WordTrace tailWord_3078689 prefixEnd_3078689 1580847242710010348828873 := by
  unfold tailWord_3078689
  simp only [CollatzResearch.WordTrace]
  refine ⟨112289012743443026065375121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74859341828962017376916747 112289012743443026065375121)
  ·
    refine ⟨84216759557582269549031341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112289012743443026065375121 84216759557582269549031341)
    ·
      refine ⟨31581284834093351080886753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84216759557582269549031341 31581284834093351080886753)
      ·
        refine ⟨23685963625570013310665065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31581284834093351080886753 23685963625570013310665065)
        ·
          refine ⟨17764472719177509982998799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23685963625570013310665065 17764472719177509982998799)
          ·
            refine ⟨26646709078766264974498199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17764472719177509982998799 26646709078766264974498199)
            ·
              refine ⟨39970063618149397461747299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26646709078766264974498199 39970063618149397461747299)
              ·
                refine ⟨59955095427224096192620949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39970063618149397461747299 59955095427224096192620949)
                ·
                  refine ⟨2810395098151129509029107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59955095427224096192620949 2810395098151129509029107)
                  ·
                    refine ⟨4215592647226694263543661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2810395098151129509029107 4215592647226694263543661)
                    ·
                      refine ⟨1580847242710010348828873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4215592647226694263543661 1580847242710010348828873)
                      ·
                        rfl

theorem cell23_3078689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_3078689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078689 prefixEnd_3078689 := by exact prefixLift 3078689
  have htrace : WordTrace (prefixWord ++ tailWord_3078689) baseStart_3078689 baseEnd_3078689 := by
    simpa [prefixWord, tailWord_3078689, baseEnd_3078689] using wordTrace_append hprefix tailTrace_3078689
  have hstable : (prefixWord ++ tailWord_3078689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078689).length < 2 ^ (prefixWord ++ tailWord_3078689).sum := by decide
  have hdescent : baseEnd_3078689 < baseStart_3078689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078712 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_3078712 : Nat := 118140960795 + 3078712 * 2 ^ 59
def prefixEnd_3078712 : Nat := 4983230072969 + 3 ^ 40 * 3078712 * 2
def baseEnd_3078712 : Nat := 1580859052765063758841267

theorem tailTrace_3078712 : CollatzResearch.WordTrace tailWord_3078712 prefixEnd_3078712 1580859052765063758841267 := by
  unfold tailWord_3078712
  simp only [CollatzResearch.WordTrace]
  refine ⟨56144925811179850496731195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74859901081573133995641593 56144925811179850496731195)
  ·
    refine ⟨84217388716769775745096793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56144925811179850496731195 84217388716769775745096793)
    ·
      refine ⟨63163041537577331808822595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84217388716769775745096793 63163041537577331808822595)
      ·
        refine ⟨94744562306365997713233893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63163041537577331808822595 94744562306365997713233893)
        ·
          refine ⟨17764605432443624571231355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94744562306365997713233893 17764605432443624571231355)
          ·
            refine ⟨26646908148665436856847033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17764605432443624571231355 26646908148665436856847033)
            ·
              refine ⟨19985181111499077642635275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26646908148665436856847033 19985181111499077642635275)
              ·
                refine ⟨29977771667248616463952913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19985181111499077642635275 29977771667248616463952913)
                ·
                  refine ⟨22483328750436462347964685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29977771667248616463952913 22483328750436462347964685)
                  ·
                    refine ⟨8431248281413673380486757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22483328750436462347964685 8431248281413673380486757)
                    ·
                      refine ⟨1580859052765063758841267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8431248281413673380486757 1580859052765063758841267)
                      ·
                        rfl

theorem cell23_3078712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_3078712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078712 prefixEnd_3078712 := by exact prefixLift 3078712
  have htrace : WordTrace (prefixWord ++ tailWord_3078712) baseStart_3078712 baseEnd_3078712 := by
    simpa [prefixWord, tailWord_3078712, baseEnd_3078712] using wordTrace_append hprefix tailTrace_3078712
  have hstable : (prefixWord ++ tailWord_3078712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078712).length < 2 ^ (prefixWord ++ tailWord_3078712).sum := by decide
  have hdescent : baseEnd_3078712 < baseStart_3078712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078732 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3078732 : Nat := 118140960795 + 3078732 * 2 ^ 59
def prefixEnd_3078732 : Nat := 4983230072969 + 3 ^ 40 * 3078732 * 2
def baseEnd_3078732 : Nat := 1580869322378153680591175

theorem tailTrace_3078732 : CollatzResearch.WordTrace tailWord_3078732 prefixEnd_3078732 1580869322378153680591175 := by
  unfold tailWord_3078732
  simp only [CollatzResearch.WordTrace]
  refine ⟨56145290541143622204595225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74860387388191496272793633 56145290541143622204595225)
  ·
    refine ⟨42108967905857716653446419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56145290541143622204595225 42108967905857716653446419)
    ·
      refine ⟨63163451858786574980169629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42108967905857716653446419 63163451858786574980169629)
      ·
        refine ⟨23686294447044965617563611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63163451858786574980169629 23686294447044965617563611)
        ·
          refine ⟨35529441670567448426345417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23686294447044965617563611 35529441670567448426345417)
          ·
            refine ⟨26647081252925586319759063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35529441670567448426345417 26647081252925586319759063)
            ·
              refine ⟨39970621879388379479638595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26647081252925586319759063 39970621879388379479638595)
              ·
                refine ⟨59955932819082569219457893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39970621879388379479638595 59955932819082569219457893)
                ·
                  refine ⟨11241737403577981728648355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59955932819082569219457893 11241737403577981728648355)
                  ·
                    refine ⟨16862606105366972592972533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11241737403577981728648355 16862606105366972592972533)
                    ·
                      refine ⟨1580869322378153680591175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16862606105366972592972533 1580869322378153680591175)
                      ·
                        rfl

theorem cell23_3078732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3078732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078732 prefixEnd_3078732 := by exact prefixLift 3078732
  have htrace : WordTrace (prefixWord ++ tailWord_3078732) baseStart_3078732 baseEnd_3078732 := by
    simpa [prefixWord, tailWord_3078732, baseEnd_3078732] using wordTrace_append hprefix tailTrace_3078732
  have hstable : (prefixWord ++ tailWord_3078732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078732).length < 2 ^ (prefixWord ++ tailWord_3078732).sum := by decide
  have hdescent : baseEnd_3078732 < baseStart_3078732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078733 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_3078733 : Nat := 118140960795 + 3078733 * 2 ^ 59
def prefixEnd_3078733 : Nat := 4983230072969 + 3 ^ 40 * 3078733 * 2
def baseEnd_3078733 : Nat := 1580869835858808176678671

theorem tailTrace_3078733 : CollatzResearch.WordTrace tailWord_3078733 prefixEnd_3078733 1580869835858808176678671 := by
  unfold tailWord_3078733
  simp only [CollatzResearch.WordTrace]
  refine ⟨112290617555283621579976853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74860411703522414386651235 112290617555283621579976853)
  ·
    refine ⟨5263622697903919761561415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112290617555283621579976853 5263622697903919761561415)
    ·
      refine ⟨7895434046855879642342123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5263622697903919761561415 7895434046855879642342123)
      ·
        refine ⟨11843151070283819463513185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7895434046855879642342123 11843151070283819463513185)
        ·
          refine ⟨8882363302712864597634889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11843151070283819463513185 8882363302712864597634889)
          ·
            refine ⟨6661772477034648448226167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8882363302712864597634889 6661772477034648448226167)
            ·
              refine ⟨9992658715551972672339251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6661772477034648448226167 9992658715551972672339251)
              ·
                refine ⟨14988988073327959008508877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9992658715551972672339251 14988988073327959008508877)
                ·
                  refine ⟨5620870527497984628190829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14988988073327959008508877 5620870527497984628190829)
                  ·
                    refine ⟨2107826447811744235571561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5620870527497984628190829 2107826447811744235571561)
                    ·
                      refine ⟨1580869835858808176678671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2107826447811744235571561 1580869835858808176678671)
                      ·
                        rfl

theorem cell23_3078733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_3078733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078733 prefixEnd_3078733 := by exact prefixLift 3078733
  have htrace : WordTrace (prefixWord ++ tailWord_3078733) baseStart_3078733 baseEnd_3078733 := by
    simpa [prefixWord, tailWord_3078733, baseEnd_3078733] using wordTrace_append hprefix tailTrace_3078733
  have hstable : (prefixWord ++ tailWord_3078733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078733).length < 2 ^ (prefixWord ++ tailWord_3078733).sum := by decide
  have hdescent : baseEnd_3078733 < baseStart_3078733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078832 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_3078832 : Nat := 118140960795 + 3078832 * 2 ^ 59
def prefixEnd_3078832 : Nat := 4983230072969 + 3 ^ 40 * 3078832 * 2
def baseEnd_3078832 : Nat := 1580920670443603289340715

theorem tailTrace_3078832 : CollatzResearch.WordTrace tailWord_3078832 prefixEnd_3078832 1580920670443603289340715 := by
  unfold tailWord_3078832
  simp only [CollatzResearch.WordTrace]
  refine ⟨56147114190962480743915375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74862818921283307658553833 56147114190962480743915375)
  ·
    refine ⟨84220671286443721115873063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56147114190962480743915375 84220671286443721115873063)
    ·
      refine ⟨126331006929665581673809595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84220671286443721115873063 126331006929665581673809595)
      ·
        refine ⟨189496510394498372510714393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126331006929665581673809595 189496510394498372510714393)
        ·
          refine ⟨142122382795873779383035795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189496510394498372510714393 142122382795873779383035795)
          ·
            refine ⟨213183574193810669074553693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142122382795873779383035795 213183574193810669074553693)
            ·
              refine ⟨79943840322679000902957635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213183574193810669074553693 79943840322679000902957635)
              ·
                refine ⟨119915760484018501354436453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79943840322679000902957635 119915760484018501354436453)
                ·
                  refine ⟨22484205090753469003956835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119915760484018501354436453 22484205090753469003956835)
                  ·
                    refine ⟨33726307636130203505935253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22484205090753469003956835 33726307636130203505935253)
                    ·
                      refine ⟨1580920670443603289340715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33726307636130203505935253 1580920670443603289340715)
                      ·
                        rfl

theorem cell23_3078832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_3078832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078832 prefixEnd_3078832 := by exact prefixLift 3078832
  have htrace : WordTrace (prefixWord ++ tailWord_3078832) baseStart_3078832 baseEnd_3078832 := by
    simpa [prefixWord, tailWord_3078832, baseEnd_3078832] using wordTrace_append hprefix tailTrace_3078832
  have hstable : (prefixWord ++ tailWord_3078832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078832).length < 2 ^ (prefixWord ++ tailWord_3078832).sum := by decide
  have hdescent : baseEnd_3078832 < baseStart_3078832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078846 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_3078846 : Nat := 118140960795 + 3078846 * 2 ^ 59
def prefixEnd_3078846 : Nat := 4983230072969 + 3 ^ 40 * 3078846 * 2
def baseEnd_3078846 : Nat := 526975953057588744855217

theorem tailTrace_3078846 : CollatzResearch.WordTrace tailWord_3078846 prefixEnd_3078846 526975953057588744855217 := by
  unfold tailWord_3078846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14036842375484280234855049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74863159335916161252560261 14036842375484280234855049)
  ·
    refine ⟨10527631781613210176141287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14036842375484280234855049 10527631781613210176141287)
    ·
      refine ⟨15791447672419815264211931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10527631781613210176141287 15791447672419815264211931)
      ·
        refine ⟨23687171508629722896317897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15791447672419815264211931 23687171508629722896317897)
        ·
          refine ⟨17765378631472292172238423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23687171508629722896317897 17765378631472292172238423)
          ·
            refine ⟨26648067947208438258357635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17765378631472292172238423 26648067947208438258357635)
            ·
              refine ⟨39972101920812657387536453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26648067947208438258357635 39972101920812657387536453)
              ·
                refine ⟨7494769110152373260163085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39972101920812657387536453 7494769110152373260163085)
                ·
                  refine ⟨2810538416307139972561157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7494769110152373260163085 2810538416307139972561157)
                  ·
                    refine ⟨526975953057588744855217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2810538416307139972561157 526975953057588744855217)
                    ·
                      rfl

theorem cell23_3078846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_3078846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078846 prefixEnd_3078846 := by exact prefixLift 3078846
  have htrace : WordTrace (prefixWord ++ tailWord_3078846) baseStart_3078846 baseEnd_3078846 := by
    simpa [prefixWord, tailWord_3078846, baseEnd_3078846] using wordTrace_append hprefix tailTrace_3078846
  have hstable : (prefixWord ++ tailWord_3078846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078846).length < 2 ^ (prefixWord ++ tailWord_3078846).sum := by decide
  have hdescent : baseEnd_3078846 < baseStart_3078846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078854 : List Nat := [6, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_3078854 : Nat := 118140960795 + 3078854 * 2 ^ 59
def prefixEnd_3078854 : Nat := 4983230072969 + 3 ^ 40 * 3078854 * 2
def baseEnd_3078854 : Nat := 175659107446444689251735

theorem tailTrace_3078854 : CollatzResearch.WordTrace tailWord_3078854 prefixEnd_3078854 175659107446444689251735 := by
  unfold tailWord_3078854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509219712120164351410363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74863353858563506163421077 3509219712120164351410363)
  ·
    refine ⟨5263829568180246527115545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3509219712120164351410363 5263829568180246527115545)
    ·
      refine ⟨3947872176135184895336659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5263829568180246527115545 3947872176135184895336659)
      ·
        refine ⟨5921808264202777343004989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3947872176135184895336659 5921808264202777343004989)
        ·
          refine ⟨2220678099076041503626871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5921808264202777343004989 2220678099076041503626871)
          ·
            refine ⟨3331017148614062255440307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220678099076041503626871 3331017148614062255440307)
            ·
              refine ⟨4996525722921093383160461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331017148614062255440307 4996525722921093383160461)
              ·
                refine ⟨1873697146095410018685173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4996525722921093383160461 1873697146095410018685173)
                ·
                  refine ⟨175659107446444689251735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1873697146095410018685173 175659107446444689251735)
                  ·
                    rfl

theorem cell23_3078854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_3078854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078854 prefixEnd_3078854 := by exact prefixLift 3078854
  have htrace : WordTrace (prefixWord ++ tailWord_3078854) baseStart_3078854 baseEnd_3078854 := by
    simpa [prefixWord, tailWord_3078854, baseEnd_3078854] using wordTrace_append hprefix tailTrace_3078854
  have hstable : (prefixWord ++ tailWord_3078854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078854).length < 2 ^ (prefixWord ++ tailWord_3078854).sum := by decide
  have hdescent : baseEnd_3078854 < baseStart_3078854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078876 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 8]
def baseStart_3078876 : Nat := 118140960795 + 3078876 * 2 ^ 59
def prefixEnd_3078876 : Nat := 4983230072969 + 3 ^ 40 * 3078876 * 2
def baseEnd_3078876 : Nat := 175660362621377901910057

theorem tailTrace_3078876 : CollatzResearch.WordTrace tailWord_3078876 prefixEnd_3078876 175660362621377901910057 := by
  unfold tailWord_3078876
  simp only [CollatzResearch.WordTrace]
  refine ⟨56147916596882778501216241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74863888795843704668288321 56147916596882778501216241)
  ·
    refine ⟨42110937447662083875912181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56147916596882778501216241 42110937447662083875912181)
    ·
      refine ⟨3947900385718320363366767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42110937447662083875912181 3947900385718320363366767)
      ·
        refine ⟨5921850578577480545050151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3947900385718320363366767 5921850578577480545050151)
        ·
          refine ⟨8882775867866220817575227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5921850578577480545050151 8882775867866220817575227)
          ·
            refine ⟨13324163801799331226362841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8882775867866220817575227 13324163801799331226362841)
            ·
              refine ⟨9993122851349498419772131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13324163801799331226362841 9993122851349498419772131)
              ·
                refine ⟨14989684277024247629658197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9993122851349498419772131 14989684277024247629658197)
                ·
                  refine ⟨175660362621377901910057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14989684277024247629658197 175660362621377901910057)
                  ·
                    rfl

theorem cell23_3078876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_3078876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078876 prefixEnd_3078876 := by exact prefixLift 3078876
  have htrace : WordTrace (prefixWord ++ tailWord_3078876) baseStart_3078876 baseEnd_3078876 := by
    simpa [prefixWord, tailWord_3078876, baseEnd_3078876] using wordTrace_append hprefix tailTrace_3078876
  have hstable : (prefixWord ++ tailWord_3078876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078876).length < 2 ^ (prefixWord ++ tailWord_3078876).sum := by decide
  have hdescent : baseEnd_3078876 < baseStart_3078876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078896 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 4, 3, 2]
def baseStart_3078896 : Nat := 118140960795 + 3078896 * 2 ^ 59
def prefixEnd_3078896 : Nat := 4983230072969 + 3 ^ 40 * 3078896 * 2
def baseEnd_3078896 : Nat := 1580953533205491038940421

theorem tailTrace_3078896 : CollatzResearch.WordTrace tailWord_3078896 prefixEnd_3078896 1580953533205491038940421 := by
  unfold tailWord_3078896
  simp only [CollatzResearch.WordTrace]
  refine ⟨56148281326846550209080271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74864375102462066945440361 56148281326846550209080271)
  ·
    refine ⟨84222421990269825313620407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56148281326846550209080271 84222421990269825313620407)
    ·
      refine ⟨126333632985404737970430611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84222421990269825313620407 126333632985404737970430611)
      ·
        refine ⟨189500449478107106955645917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126333632985404737970430611 189500449478107106955645917)
        ·
          refine ⟨71062668554290165108367219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189500449478107106955645917 71062668554290165108367219)
          ·
            refine ⟨106594002831435247662550829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71062668554290165108367219 106594002831435247662550829)
            ·
              refine ⟨39972751061788217873456561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106594002831435247662550829 39972751061788217873456561)
              ·
                refine ⟨29979563296341163405092421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39972751061788217873456561 29979563296341163405092421)
                ·
                  refine ⟨5621168118063968138454829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29979563296341163405092421 5621168118063968138454829)
                  ·
                    refine ⟨2107938044273988051920561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5621168118063968138454829 2107938044273988051920561)
                    ·
                      refine ⟨1580953533205491038940421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2107938044273988051920561 1580953533205491038940421)
                      ·
                        rfl

theorem cell23_3078896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4, 3, 2].length) (baseStart_3078896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078896 prefixEnd_3078896 := by exact prefixLift 3078896
  have htrace : WordTrace (prefixWord ++ tailWord_3078896) baseStart_3078896 baseEnd_3078896 := by
    simpa [prefixWord, tailWord_3078896, baseEnd_3078896] using wordTrace_append hprefix tailTrace_3078896
  have hstable : (prefixWord ++ tailWord_3078896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078896).length < 2 ^ (prefixWord ++ tailWord_3078896).sum := by decide
  have hdescent : baseEnd_3078896 < baseStart_3078896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078906 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_3078906 : Nat := 118140960795 + 3078906 * 2 ^ 59
def prefixEnd_3078906 : Nat := 4983230072969 + 3 ^ 40 * 3078906 * 2
def baseEnd_3078906 : Nat := 526986222670678666605125

theorem tailTrace_3078906 : CollatzResearch.WordTrace tailWord_3078906 prefixEnd_3078906 526986222670678666605125 := by
  unfold tailWord_3078906
  simp only [CollatzResearch.WordTrace]
  refine ⟨28074231845914218031506143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74864618255771248084016381 28074231845914218031506143)
  ·
    refine ⟨42111347768871327047259215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28074231845914218031506143 42111347768871327047259215)
    ·
      refine ⟨63167021653306990570888823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42111347768871327047259215 63167021653306990570888823)
      ·
        refine ⟨94750532479960485856333235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63167021653306990570888823 94750532479960485856333235)
        ·
          refine ⟨142125798719940728784499853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94750532479960485856333235 142125798719940728784499853)
          ·
            refine ⟨53297174519977773294187445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142125798719940728784499853 53297174519977773294187445)
            ·
              refine ⟨4996610111247916246330073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53297174519977773294187445 4996610111247916246330073)
              ·
                refine ⟨3747457583435937184747555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4996610111247916246330073 3747457583435937184747555)
                ·
                  refine ⟨5621186375153905777121333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747457583435937184747555 5621186375153905777121333)
                  ·
                    refine ⟨526986222670678666605125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5621186375153905777121333 526986222670678666605125)
                    ·
                      rfl

theorem cell23_3078906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_3078906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078906 prefixEnd_3078906 := by exact prefixLift 3078906
  have htrace : WordTrace (prefixWord ++ tailWord_3078906) baseStart_3078906 baseEnd_3078906 := by
    simpa [prefixWord, tailWord_3078906, baseEnd_3078906] using wordTrace_append hprefix tailTrace_3078906
  have hstable : (prefixWord ++ tailWord_3078906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078906).length < 2 ^ (prefixWord ++ tailWord_3078906).sum := by decide
  have hdescent : baseEnd_3078906 < baseStart_3078906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078956 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 4]
def baseStart_3078956 : Nat := 118140960795 + 3078956 * 2 ^ 59
def prefixEnd_3078956 : Nat := 4983230072969 + 3 ^ 40 * 3078956 * 2
def baseEnd_3078956 : Nat := 1580984342044760804190145

theorem tailTrace_3078956 : CollatzResearch.WordTrace tailWord_3078956 prefixEnd_3078956 1580984342044760804190145 := by
  unfold tailWord_3078956
  simp only [CollatzResearch.WordTrace]
  refine ⟨56149375516737865332672361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74865834022317153776896481 56149375516737865332672361)
  ·
    refine ⟨42112031637553398999504271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56149375516737865332672361 42112031637553398999504271)
    ·
      refine ⟨63168047456330098499256407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42112031637553398999504271 63168047456330098499256407)
      ·
        refine ⟨94752071184495147748884611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63168047456330098499256407 94752071184495147748884611)
        ·
          refine ⟨142128106776742721623326917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94752071184495147748884611 142128106776742721623326917)
          ·
            refine ⟨26649020020639260304373797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142128106776742721623326917 26649020020639260304373797)
            ·
              refine ⟨4996691253869861307070087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26649020020639260304373797 4996691253869861307070087)
              ·
                refine ⟨7495036880804791960605131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4996691253869861307070087 7495036880804791960605131)
                ·
                  refine ⟨11242555321207187940907697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7495036880804791960605131 11242555321207187940907697)
                  ·
                    refine ⟨8431916490905390955680773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11242555321207187940907697 8431916490905390955680773)
                    ·
                      refine ⟨1580984342044760804190145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8431916490905390955680773 1580984342044760804190145)
                      ·
                        rfl

theorem cell23_3078956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_3078956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078956 prefixEnd_3078956 := by exact prefixLift 3078956
  have htrace : WordTrace (prefixWord ++ tailWord_3078956) baseStart_3078956 baseEnd_3078956 := by
    simpa [prefixWord, tailWord_3078956, baseEnd_3078956] using wordTrace_append hprefix tailTrace_3078956
  have hstable : (prefixWord ++ tailWord_3078956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078956).length < 2 ^ (prefixWord ++ tailWord_3078956).sum := by decide
  have hdescent : baseEnd_3078956 < baseStart_3078956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3078964 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_3078964 : Nat := 118140960795 + 3078964 * 2 ^ 59
def prefixEnd_3078964 : Nat := 4983230072969 + 3 ^ 40 * 3078964 * 2
def baseEnd_3078964 : Nat := 1580988449889996772890109

theorem tailTrace_3078964 : CollatzResearch.WordTrace tailWord_3078964 prefixEnd_3078964 1580988449889996772890109 := by
  unfold tailWord_3078964
  simp only [CollatzResearch.WordTrace]
  refine ⟨56149521408723374015817973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74866028544964498687757297 56149521408723374015817973)
  ·
    refine ⟨5264017632067816313982935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56149521408723374015817973 5264017632067816313982935)
    ·
      refine ⟨7896026448101724470974403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5264017632067816313982935 7896026448101724470974403)
      ·
        refine ⟨11844039672152586706461605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7896026448101724470974403 11844039672152586706461605)
        ·
          refine ⟨2220757438528610007461551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11844039672152586706461605 2220757438528610007461551)
          ·
            refine ⟨3331136157792915011192327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220757438528610007461551 3331136157792915011192327)
            ·
              refine ⟨4996704236689372516788491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331136157792915011192327 4996704236689372516788491)
              ·
                refine ⟨7495056355034058775182737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4996704236689372516788491 7495056355034058775182737)
                ·
                  refine ⟨5621292266275544081387053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7495056355034058775182737 5621292266275544081387053)
                  ·
                    refine ⟨2107984599853329030520145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5621292266275544081387053 2107984599853329030520145)
                    ·
                      refine ⟨1580988449889996772890109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2107984599853329030520145 1580988449889996772890109)
                      ·
                        rfl

theorem cell23_3078964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_3078964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3078964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3078964 prefixEnd_3078964 := by exact prefixLift 3078964
  have htrace : WordTrace (prefixWord ++ tailWord_3078964) baseStart_3078964 baseEnd_3078964 := by
    simpa [prefixWord, tailWord_3078964, baseEnd_3078964] using wordTrace_append hprefix tailTrace_3078964
  have hstable : (prefixWord ++ tailWord_3078964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3078964).length < 2 ^ (prefixWord ++ tailWord_3078964).sum := by decide
  have hdescent : baseEnd_3078964 < baseStart_3078964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3078964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079009 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 1, 8]
def baseStart_3079009 : Nat := 118140960795 + 3079009 * 2 ^ 59
def prefixEnd_3079009 : Nat := 4983230072969 + 3 ^ 40 * 3079009 * 2
def baseEnd_3079009 : Nat := 527003852173149698942467

theorem tailTrace_3079009 : CollatzResearch.WordTrace tailWord_3079009 prefixEnd_3079009 527003852173149698942467 := by
  unfold tailWord_3079009
  simp only [CollatzResearch.WordTrace]
  refine ⟨112300684102283720717024081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74867122734855813811349387 112300684102283720717024081)
  ·
    refine ⟨84225513076712790537768061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112300684102283720717024081 84225513076712790537768061)
    ·
      refine ⟨31584567403767296451663023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84225513076712790537768061 31584567403767296451663023)
      ·
        refine ⟨47376851105650944677494535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31584567403767296451663023 47376851105650944677494535)
        ·
          refine ⟨71065276658476417016241803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47376851105650944677494535 71065276658476417016241803)
          ·
            refine ⟨106597914987714625524362705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71065276658476417016241803 106597914987714625524362705)
            ·
              refine ⟨79948436240785969143272029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106597914987714625524362705 79948436240785969143272029)
              ·
                refine ⟨29980663590294738428727011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79948436240785969143272029 29980663590294738428727011)
                ·
                  refine ⟨44970995385442107643090517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29980663590294738428727011 44970995385442107643090517)
                  ·
                    refine ⟨527003852173149698942467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44970995385442107643090517 527003852173149698942467)
                    ·
                      rfl

theorem cell23_3079009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_3079009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079009 prefixEnd_3079009 := by exact prefixLift 3079009
  have htrace : WordTrace (prefixWord ++ tailWord_3079009) baseStart_3079009 baseEnd_3079009 := by
    simpa [prefixWord, tailWord_3079009, baseEnd_3079009] using wordTrace_append hprefix tailTrace_3079009
  have hstable : (prefixWord ++ tailWord_3079009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079009).length < 2 ^ (prefixWord ++ tailWord_3079009).sum := by decide
  have hdescent : baseEnd_3079009 < baseStart_3079009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079020 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 1, 3, 2]
def baseStart_3079020 : Nat := 118140960795 + 3079020 * 2 ^ 59
def prefixEnd_3079020 : Nat := 4983230072969 + 3 ^ 40 * 3079020 * 2
def baseEnd_3079020 : Nat := 1581017204806648553789851

theorem tailTrace_3079020 : CollatzResearch.WordTrace tailWord_3079020 prefixEnd_3079020 1581017204806648553789851 := by
  unfold tailWord_3079020
  simp only [CollatzResearch.WordTrace]
  refine ⟨56150542652621934797837257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74867390203495913063783009 56150542652621934797837257)
  ·
    refine ⟨42112906989466451098377943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56150542652621934797837257 42112906989466451098377943)
    ·
      refine ⟨63169360484199676647566915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42112906989466451098377943 63169360484199676647566915)
      ·
        refine ⟨94754040726299514971350373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63169360484199676647566915 94754040726299514971350373)
        ·
          refine ⟨17766382636181159057128195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94754040726299514971350373 17766382636181159057128195)
          ·
            refine ⟨26649573954271738585692293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17766382636181159057128195 26649573954271738585692293)
            ·
              refine ⟨4996795116425950984817305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26649573954271738585692293 4996795116425950984817305)
              ·
                refine ⟨3747596337319463238612979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4996795116425950984817305 3747596337319463238612979)
                ·
                  refine ⟨5621394505979194857919469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747596337319463238612979 5621394505979194857919469)
                  ·
                    refine ⟨2108022939742198071719801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5621394505979194857919469 2108022939742198071719801)
                    ·
                      refine ⟨1581017204806648553789851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2108022939742198071719801 1581017204806648553789851)
                      ·
                        rfl

theorem cell23_3079020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_3079020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079020 prefixEnd_3079020 := by exact prefixLift 3079020
  have htrace : WordTrace (prefixWord ++ tailWord_3079020) baseStart_3079020 baseEnd_3079020 := by
    simpa [prefixWord, tailWord_3079020, baseEnd_3079020] using wordTrace_append hprefix tailTrace_3079020
  have hstable : (prefixWord ++ tailWord_3079020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079020).length < 2 ^ (prefixWord ++ tailWord_3079020).sum := by decide
  have hdescent : baseEnd_3079020 < baseStart_3079020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079039 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 9]
def baseStart_3079039 : Nat := 118140960795 + 3079039 * 2 ^ 59
def prefixEnd_3079039 : Nat := 4983230072969 + 3 ^ 40 * 3079039 * 2
def baseEnd_3079039 : Nat := 175669662326564886605807

theorem tailTrace_3079039 : CollatzResearch.WordTrace tailWord_3079039 prefixEnd_3079039 175669662326564886605807 := by
  unfold tailWord_3079039
  simp only [CollatzResearch.WordTrace]
  refine ⟨112301778292175035840616171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74867852194783357227077447 112301778292175035840616171)
  ·
    refine ⟨168452667438262553760924257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112301778292175035840616171 168452667438262553760924257)
    ·
      refine ⟨126339500578696915320693193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168452667438262553760924257 126339500578696915320693193)
      ·
        refine ⟨94754625434022686490519895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126339500578696915320693193 94754625434022686490519895)
        ·
          refine ⟨142131938151034029735779843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94754625434022686490519895 142131938151034029735779843)
          ·
            refine ⟨213197907226551044603669765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142131938151034029735779843 213197907226551044603669765)
            ·
              refine ⟨39974607604978320863188081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213197907226551044603669765 39974607604978320863188081)
              ·
                refine ⟨29980955703733740647391061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39974607604978320863188081 29980955703733740647391061)
                ·
                  refine ⟨175669662326564886605807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29980955703733740647391061 175669662326564886605807)
                  ·
                    rfl

theorem cell23_3079039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 9].length) (baseStart_3079039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079039 prefixEnd_3079039 := by exact prefixLift 3079039
  have htrace : WordTrace (prefixWord ++ tailWord_3079039) baseStart_3079039 baseEnd_3079039 := by
    simpa [prefixWord, tailWord_3079039, baseEnd_3079039] using wordTrace_append hprefix tailTrace_3079039
  have hstable : (prefixWord ++ tailWord_3079039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079039).length < 2 ^ (prefixWord ++ tailWord_3079039).sum := by decide
  have hdescent : baseEnd_3079039 < baseStart_3079039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079059 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 8]
def baseStart_3079059 : Nat := 118140960795 + 3079059 * 2 ^ 59
def prefixEnd_3079059 : Nat := 4983230072969 + 3 ^ 40 * 3079059 * 2
def baseEnd_3079059 : Nat := 1581037230552173901202171

theorem tailTrace_3079059 : CollatzResearch.WordTrace tailWord_3079059 prefixEnd_3079059 1581037230552173901202171 := by
  unfold tailWord_3079059
  simp only [CollatzResearch.WordTrace]
  refine ⟨112302507752102579256344231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74868338501401719504229487 112302507752102579256344231)
  ·
    refine ⟨168453761628153868884516347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112302507752102579256344231 168453761628153868884516347)
    ·
      refine ⟨252680642442230803326774521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168453761628153868884516347 252680642442230803326774521)
      ·
        refine ⟨189510481831673102495080891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252680642442230803326774521 189510481831673102495080891)
        ·
          refine ⟨284265722747509653742621337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189510481831673102495080891 284265722747509653742621337)
          ·
            refine ⟨213199292060632240306966003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284265722747509653742621337 213199292060632240306966003)
            ·
              refine ⟨319798938090948360460449005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213199292060632240306966003 319798938090948360460449005)
              ·
                refine ⟨119924601784105635172668377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319798938090948360460449005 119924601784105635172668377)
                ·
                  refine ⟨89943451338079226379501283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119924601784105635172668377 89943451338079226379501283)
                  ·
                    refine ⟨134915177007118839569251925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89943451338079226379501283 134915177007118839569251925)
                    ·
                      refine ⟨1581037230552173901202171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 134915177007118839569251925 1581037230552173901202171)
                      ·
                        rfl

theorem cell23_3079059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_3079059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079059 prefixEnd_3079059 := by exact prefixLift 3079059
  have htrace : WordTrace (prefixWord ++ tailWord_3079059) baseStart_3079059 baseEnd_3079059 := by
    simpa [prefixWord, tailWord_3079059, baseEnd_3079059] using wordTrace_append hprefix tailTrace_3079059
  have hstable : (prefixWord ++ tailWord_3079059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079059).length < 2 ^ (prefixWord ++ tailWord_3079059).sum := by decide
  have hdescent : baseEnd_3079059 < baseStart_3079059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079096 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_3079096 : Nat := 118140960795 + 3079096 * 2 ^ 59
def prefixEnd_3079096 : Nat := 4983230072969 + 3 ^ 40 * 3079096 * 2
def baseEnd_3079096 : Nat := 1581056229336390256439501

theorem tailTrace_3079096 : CollatzResearch.WordTrace tailWord_3079096 prefixEnd_3079096 1581056229336390256439501 := by
  unfold tailWord_3079096
  simp only [CollatzResearch.WordTrace]
  refine ⟨56151928626484267287720571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74869238168645689716960761 56151928626484267287720571)
  ·
    refine ⟨84227892939726400931580857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56151928626484267287720571 84227892939726400931580857)
    ·
      refine ⟨63170919704794800698685643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84227892939726400931580857 63170919704794800698685643)
      ·
        refine ⟨94756379557192201048028465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63170919704794800698685643 94756379557192201048028465)
        ·
          refine ⟨71067284667894150786021349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94756379557192201048028465 71067284667894150786021349)
          ·
            refine ⟨13325115875230153272379003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71067284667894150786021349 13325115875230153272379003)
            ·
              refine ⟨19987673812845229908568505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13325115875230153272379003 19987673812845229908568505)
              ·
                refine ⟨14990755359633922431426379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19987673812845229908568505 14990755359633922431426379)
                ·
                  refine ⟨22486133039450883647139569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14990755359633922431426379 22486133039450883647139569)
                  ·
                    refine ⟨16864599779588162735354677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22486133039450883647139569 16864599779588162735354677)
                    ·
                      refine ⟨1581056229336390256439501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16864599779588162735354677 1581056229336390256439501)
                      ·
                        rfl

theorem cell23_3079096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_3079096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079096 prefixEnd_3079096 := by exact prefixLift 3079096
  have htrace : WordTrace (prefixWord ++ tailWord_3079096) baseStart_3079096 baseEnd_3079096 := by
    simpa [prefixWord, tailWord_3079096, baseEnd_3079096] using wordTrace_append hprefix tailTrace_3079096
  have hstable : (prefixWord ++ tailWord_3079096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079096).length < 2 ^ (prefixWord ++ tailWord_3079096).sum := by decide
  have hdescent : baseEnd_3079096 < baseStart_3079096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079180 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 6]
def baseStart_3079180 : Nat := 118140960795 + 3079180 * 2 ^ 59
def prefixEnd_3079180 : Nat := 4983230072969 + 3 ^ 40 * 3079180 * 2
def baseEnd_3079180 : Nat := 175677706856818658643235

theorem tailTrace_3079180 : CollatzResearch.WordTrace tailWord_3079180 prefixEnd_3079180 175677706856818658643235 := by
  unfold tailWord_3079180
  simp only [CollatzResearch.WordTrace]
  refine ⟨56153460492332108460749497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74871280656442811280999329 56153460492332108460749497)
  ·
    refine ⟨42115095369249081345562123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56153460492332108460749497 42115095369249081345562123)
    ·
      refine ⟨63172643053873622018343185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42115095369249081345562123 63172643053873622018343185)
      ·
        refine ⟨47379482290405216513757389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63172643053873622018343185 47379482290405216513757389)
        ·
          refine ⟨17767305858901956192659021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47379482290405216513757389 17767305858901956192659021)
          ·
            refine ⟨6662739697088233572247133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17767305858901956192659021 6662739697088233572247133)
            ·
              refine ⟨2498527386408087589592675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6662739697088233572247133 2498527386408087589592675)
              ·
                refine ⟨3747791079612131384389013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498527386408087589592675 3747791079612131384389013)
                ·
                  refine ⟨175677706856818658643235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3747791079612131384389013 175677706856818658643235)
                  ·
                    rfl

theorem cell23_3079180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_3079180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079180 prefixEnd_3079180 := by exact prefixLift 3079180
  have htrace : WordTrace (prefixWord ++ tailWord_3079180) baseStart_3079180 baseEnd_3079180 := by
    simpa [prefixWord, tailWord_3079180, baseEnd_3079180] using wordTrace_append hprefix tailTrace_3079180
  have hstable : (prefixWord ++ tailWord_3079180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079180).length < 2 ^ (prefixWord ++ tailWord_3079180).sum := by decide
  have hdescent : baseEnd_3079180 < baseStart_3079180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079193 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 1, 5]
def baseStart_3079193 : Nat := 118140960795 + 3079193 * 2 ^ 59
def prefixEnd_3079193 : Nat := 4983230072969 + 3 ^ 40 * 3079193 * 2
def baseEnd_3079193 : Nat := 527035345653292125642185

theorem tailTrace_3079193 : CollatzResearch.WordTrace tailWord_3079193 prefixEnd_3079193 527035345653292125642185 := by
  unfold tailWord_3079193
  simp only [CollatzResearch.WordTrace]
  refine ⟨112307395133617120141722233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74871596755744746761148155 112307395133617120141722233)
  ·
    refine ⟨84230546350212840106291675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112307395133617120141722233 84230546350212840106291675)
    ·
      refine ⟨126345819525319260159437513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84230546350212840106291675 126345819525319260159437513)
      ·
        refine ⟨94759364643989445119578135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126345819525319260159437513 94759364643989445119578135)
        ·
          refine ⟨142139046965984167679367203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94759364643989445119578135 142139046965984167679367203)
          ·
            refine ⟨213208570448976251519050805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142139046965984167679367203 213208570448976251519050805)
            ·
              refine ⟨19988303479591523579911013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213208570448976251519050805 19988303479591523579911013)
              ·
                refine ⟨3747806902423410671233315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19988303479591523579911013 3747806902423410671233315)
                ·
                  refine ⟨5621710353635116006849973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747806902423410671233315 5621710353635116006849973)
                  ·
                    refine ⟨527035345653292125642185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5621710353635116006849973 527035345653292125642185)
                    ·
                      rfl

theorem cell23_3079193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 5].length) (baseStart_3079193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079193 prefixEnd_3079193 := by exact prefixLift 3079193
  have htrace : WordTrace (prefixWord ++ tailWord_3079193) baseStart_3079193 baseEnd_3079193 := by
    simpa [prefixWord, tailWord_3079193, baseEnd_3079193] using wordTrace_append hprefix tailTrace_3079193
  have hstable : (prefixWord ++ tailWord_3079193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079193).length < 2 ^ (prefixWord ++ tailWord_3079193).sum := by decide
  have hdescent : baseEnd_3079193 < baseStart_3079193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079240 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 2, 4]
def baseStart_3079240 : Nat := 118140960795 + 3079240 * 2 ^ 59
def prefixEnd_3079240 : Nat := 4983230072969 + 3 ^ 40 * 3079240 * 2
def baseEnd_3079240 : Nat := 527043390183545897679613

theorem tailTrace_3079240 : CollatzResearch.WordTrace tailWord_3079240 prefixEnd_3079240 527043390183545897679613 := by
  unfold tailWord_3079240
  simp only [CollatzResearch.WordTrace]
  refine ⟨56154554682223423584341587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74872739576297898112455449 56154554682223423584341587)
  ·
    refine ⟨84231832023335135376512381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56154554682223423584341587 84231832023335135376512381)
    ·
      refine ⟨31586937008750675766192143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84231832023335135376512381 31586937008750675766192143)
      ·
        refine ⟨47380405513126013649288215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31586937008750675766192143 47380405513126013649288215)
        ·
          refine ⟨71070608269689020473932323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47380405513126013649288215 71070608269689020473932323)
          ·
            refine ⟨106605912404533530710898485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71070608269689020473932323 106605912404533530710898485)
            ·
              refine ⟨9994304287925018504146733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106605912404533530710898485 9994304287925018504146733)
              ·
                refine ⟨3747864107971881939055025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9994304287925018504146733 3747864107971881939055025)
                ·
                  refine ⟨2810898080978911454291269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3747864107971881939055025 2810898080978911454291269)
                  ·
                    refine ⟨527043390183545897679613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2810898080978911454291269 527043390183545897679613)
                    ·
                      rfl

theorem cell23_3079240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_3079240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079240 prefixEnd_3079240 := by exact prefixLift 3079240
  have htrace : WordTrace (prefixWord ++ tailWord_3079240) baseStart_3079240 baseEnd_3079240 := by
    simpa [prefixWord, tailWord_3079240, baseEnd_3079240] using wordTrace_append hprefix tailTrace_3079240
  have hstable : (prefixWord ++ tailWord_3079240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079240).length < 2 ^ (prefixWord ++ tailWord_3079240).sum := by decide
  have hdescent : baseEnd_3079240 < baseStart_3079240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079260 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3079260 : Nat := 118140960795 + 3079260 * 2 ^ 59
def prefixEnd_3079260 : Nat := 4983230072969 + 3 ^ 40 * 3079260 * 2
def baseEnd_3079260 : Nat := 1581140440163727614788747

theorem tailTrace_3079260 : CollatzResearch.WordTrace tailWord_3079260 prefixEnd_3079260 1581140440163727614788747 := by
  unfold tailWord_3079260
  simp only [CollatzResearch.WordTrace]
  refine ⟨56154919412187195292205617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74873225882916260389607489 56154919412187195292205617)
  ·
    refine ⟨42116189559140396469154213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56154919412187195292205617 42116189559140396469154213)
    ·
      refine ⟨7896785542338824337966415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42116189559140396469154213 7896785542338824337966415)
      ·
        refine ⟨11845178313508236506949623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7896785542338824337966415 11845178313508236506949623)
        ·
          refine ⟨17767767470262354760424435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11845178313508236506949623 17767767470262354760424435)
          ·
            refine ⟨26651651205393532140636653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17767767470262354760424435 26651651205393532140636653)
            ·
              refine ⟨9994369202022574552738745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26651651205393532140636653 9994369202022574552738745)
              ·
                refine ⟨7495776901516930914554059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9994369202022574552738745 7495776901516930914554059)
                ·
                  refine ⟨11243665352275396371831089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7495776901516930914554059 11243665352275396371831089)
                  ·
                    refine ⟨8432749014206547278873317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11243665352275396371831089 8432749014206547278873317)
                    ·
                      refine ⟨1581140440163727614788747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8432749014206547278873317 1581140440163727614788747)
                      ·
                        rfl

theorem cell23_3079260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3079260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079260 prefixEnd_3079260 := by exact prefixLift 3079260
  have htrace : WordTrace (prefixWord ++ tailWord_3079260) baseStart_3079260 baseEnd_3079260 := by
    simpa [prefixWord, tailWord_3079260, baseEnd_3079260] using wordTrace_append hprefix tailTrace_3079260
  have hstable : (prefixWord ++ tailWord_3079260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079260).length < 2 ^ (prefixWord ++ tailWord_3079260).sum := by decide
  have hdescent : baseEnd_3079260 < baseStart_3079260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079264 : List Nat := [2, 1, 1, 3, 2, 2, 2, 5, 1, 2, 2]
def baseStart_3079264 : Nat := 118140960795 + 3079264 * 2 ^ 59
def prefixEnd_3079264 : Nat := 4983230072969 + 3 ^ 40 * 3079264 * 2
def baseEnd_3079264 : Nat := 1581142494086345599138729

theorem tailTrace_3079264 : CollatzResearch.WordTrace tailWord_3079264 prefixEnd_3079264 1581142494086345599138729 := by
  unfold tailWord_3079264
  simp only [CollatzResearch.WordTrace]
  refine ⟨56154992358179949633778423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74873323144239932845037897 56154992358179949633778423)
  ·
    refine ⟨84232488537269924450667635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56154992358179949633778423 84232488537269924450667635)
    ·
      refine ⟨126348732805904886676001453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84232488537269924450667635 126348732805904886676001453)
      ·
        refine ⟨47380774802214332503500545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126348732805904886676001453 47380774802214332503500545)
        ·
          refine ⟨35535581101660749377625409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47380774802214332503500545 35535581101660749377625409)
          ·
            refine ⟨26651685826245562033219057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35535581101660749377625409 26651685826245562033219057)
            ·
              refine ⟨19988764369684171524914293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26651685826245562033219057 19988764369684171524914293)
              ·
                refine ⟨1873946659657891080460715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19988764369684171524914293 1873946659657891080460715)
                ·
                  refine ⟨2810919989486836620691073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873946659657891080460715 2810919989486836620691073)
                  ·
                    refine ⟨2108189992115127465518305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2810919989486836620691073 2108189992115127465518305)
                    ·
                      refine ⟨1581142494086345599138729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2108189992115127465518305 1581142494086345599138729)
                      ·
                        rfl

theorem cell23_3079264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_3079264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079264 prefixEnd_3079264 := by exact prefixLift 3079264
  have htrace : WordTrace (prefixWord ++ tailWord_3079264) baseStart_3079264 baseEnd_3079264 := by
    simpa [prefixWord, tailWord_3079264, baseEnd_3079264] using wordTrace_append hprefix tailTrace_3079264
  have hstable : (prefixWord ++ tailWord_3079264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079264).length < 2 ^ (prefixWord ++ tailWord_3079264).sum := by decide
  have hdescent : baseEnd_3079264 < baseStart_3079264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079297 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_3079297 : Nat := 118140960795 + 3079297 * 2 ^ 59
def prefixEnd_3079297 : Nat := 4983230072969 + 3 ^ 40 * 3079297 * 2
def baseEnd_3079297 : Nat := 1581159438947943970026077

theorem tailTrace_3079297 : CollatzResearch.WordTrace tailWord_3079297 prefixEnd_3079297 1581159438947943970026077 := by
  unfold tailWord_3079297
  simp only [CollatzResearch.WordTrace]
  refine ⟨112311188325240345903508145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74874125550160230602338763 112311188325240345903508145)
  ·
    refine ⟨84233391243930259427631109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112311188325240345903508145 84233391243930259427631109)
    ·
      refine ⟨15793760858236923642680833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84233391243930259427631109 15793760858236923642680833)
      ·
        refine ⟨11845320643677692732010625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15793760858236923642680833 11845320643677692732010625)
        ·
          refine ⟨8883990482758269549007969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11845320643677692732010625 8883990482758269549007969)
          ·
            refine ⟨6662992862068702161755977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8883990482758269549007969 6662992862068702161755977)
            ·
              refine ⟨4997244646551526621316983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6662992862068702161755977 4997244646551526621316983)
              ·
                refine ⟨7495866969827289931975475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997244646551526621316983 7495866969827289931975475)
                ·
                  refine ⟨11243800454740934897963213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7495866969827289931975475 11243800454740934897963213)
                  ·
                    refine ⟨4216425170527850586736205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11243800454740934897963213 4216425170527850586736205)
                    ·
                      refine ⟨1581159438947943970026077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4216425170527850586736205 1581159438947943970026077)
                      ·
                        rfl

theorem cell23_3079297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_3079297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079297 prefixEnd_3079297 := by exact prefixLift 3079297
  have htrace : WordTrace (prefixWord ++ tailWord_3079297) baseStart_3079297 baseEnd_3079297 := by
    simpa [prefixWord, tailWord_3079297, baseEnd_3079297] using wordTrace_append hprefix tailTrace_3079297
  have hstable : (prefixWord ++ tailWord_3079297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079297).length < 2 ^ (prefixWord ++ tailWord_3079297).sum := by decide
  have hdescent : baseEnd_3079297 < baseStart_3079297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079303 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_3079303 : Nat := 118140960795 + 3079303 * 2 ^ 59
def prefixEnd_3079303 : Nat := 4983230072969 + 3 ^ 40 * 3079303 * 2
def baseEnd_3079303 : Nat := 1581162519831870946551049

theorem tailTrace_3079303 : CollatzResearch.WordTrace tailWord_3079303 prefixEnd_3079303 1581162519831870946551049 := by
  unfold tailWord_3079303
  simp only [CollatzResearch.WordTrace]
  refine ⟨112311407163218608928226563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74874271442145739285484375 112311407163218608928226563)
  ·
    refine ⟨168467110744827913392339845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112311407163218608928226563 168467110744827913392339845)
    ·
      refine ⟨31587583264655233761063721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168467110744827913392339845 31587583264655233761063721)
      ·
        refine ⟨23690687448491425320797791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31587583264655233761063721 23690687448491425320797791)
        ·
          refine ⟨35536031172737137981196687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23690687448491425320797791 35536031172737137981196687)
          ·
            refine ⟨53304046759105706971795031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35536031172737137981196687 53304046759105706971795031)
            ·
              refine ⟨79956070138658560457692547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53304046759105706971795031 79956070138658560457692547)
              ·
                refine ⟨119934105207987840686538821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79956070138658560457692547 119934105207987840686538821)
                ·
                  refine ⟨22487644726497720128726029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119934105207987840686538821 22487644726497720128726029)
                  ·
                    refine ⟨8432866772436645048272261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22487644726497720128726029 8432866772436645048272261)
                    ·
                      refine ⟨1581162519831870946551049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8432866772436645048272261 1581162519831870946551049)
                      ·
                        rfl

theorem cell23_3079303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_3079303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079303 prefixEnd_3079303 := by exact prefixLift 3079303
  have htrace : WordTrace (prefixWord ++ tailWord_3079303) baseStart_3079303 baseEnd_3079303 := by
    simpa [prefixWord, tailWord_3079303, baseEnd_3079303] using wordTrace_append hprefix tailTrace_3079303
  have hstable : (prefixWord ++ tailWord_3079303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079303).length < 2 ^ (prefixWord ++ tailWord_3079303).sum := by decide
  have hdescent : baseEnd_3079303 < baseStart_3079303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079323 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 3]
def baseStart_3079323 : Nat := 118140960795 + 3079323 * 2 ^ 59
def prefixEnd_3079323 : Nat := 4983230072969 + 3 ^ 40 * 3079323 * 2
def baseEnd_3079323 : Nat := 1581172789444960868300957

theorem tailTrace_3079323 : CollatzResearch.WordTrace tailWord_3079323 prefixEnd_3079323 1581172789444960868300957 := by
  unfold tailWord_3079323
  simp only [CollatzResearch.WordTrace]
  refine ⟨112312136623146152343954623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74874757748764101562636415 112312136623146152343954623)
  ·
    refine ⟨168468204934719228515931935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112312136623146152343954623 168468204934719228515931935)
    ·
      refine ⟨252702307402078842773897903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168468204934719228515931935 252702307402078842773897903)
      ·
        refine ⟨379053461103118264160846855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252702307402078842773897903 379053461103118264160846855)
        ·
          refine ⟨568580191654677396241270283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379053461103118264160846855 568580191654677396241270283)
          ·
            refine ⟨852870287482016094361905425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568580191654677396241270283 852870287482016094361905425)
            ·
              refine ⟨639652715611512070771429069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852870287482016094361905425 639652715611512070771429069)
              ·
                refine ⟨239869768354317026539285901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 639652715611512070771429069 239869768354317026539285901)
                ·
                  refine ⟨89951163132868884952232213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239869768354317026539285901 89951163132868884952232213)
                  ·
                    refine ⟨4216460771853228982135885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89951163132868884952232213 4216460771853228982135885)
                    ·
                      refine ⟨1581172789444960868300957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4216460771853228982135885 1581172789444960868300957)
                      ·
                        rfl

theorem cell23_3079323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 3].length) (baseStart_3079323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079323 prefixEnd_3079323 := by exact prefixLift 3079323
  have htrace : WordTrace (prefixWord ++ tailWord_3079323) baseStart_3079323 baseEnd_3079323 := by
    simpa [prefixWord, tailWord_3079323, baseEnd_3079323] using wordTrace_append hprefix tailTrace_3079323
  have hstable : (prefixWord ++ tailWord_3079323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079323).length < 2 ^ (prefixWord ++ tailWord_3079323).sum := by decide
  have hdescent : baseEnd_3079323 < baseStart_3079323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079324 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_3079324 : Nat := 118140960795 + 3079324 * 2 ^ 59
def prefixEnd_3079324 : Nat := 4983230072969 + 3 ^ 40 * 3079324 * 2
def baseEnd_3079324 : Nat := 1581173302925615364388453

theorem tailTrace_3079324 : CollatzResearch.WordTrace tailWord_3079324 prefixEnd_3079324 1581173302925615364388453 := by
  unfold tailWord_3079324
  simp only [CollatzResearch.WordTrace]
  refine ⟨56156086548071264757370513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74874782064095019676494017 56156086548071264757370513)
  ·
    refine ⟨42117064911053448568027885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56156086548071264757370513 42117064911053448568027885)
    ·
      refine ⟨15793899341645043213010457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42117064911053448568027885 15793899341645043213010457)
      ·
        refine ⟨11845424506233782409757843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15793899341645043213010457 11845424506233782409757843)
        ·
          refine ⟨17768136759350673614636765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11845424506233782409757843 17768136759350673614636765)
          ·
            refine ⟨6663051284756502605488787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17768136759350673614636765 6663051284756502605488787)
            ·
              refine ⟨9994576927134753908233181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6663051284756502605488787 9994576927134753908233181)
              ·
                refine ⟨3747966347675532715587443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9994576927134753908233181 3747966347675532715587443)
                ·
                  refine ⟨5621949521513299073381165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747966347675532715587443 5621949521513299073381165)
                  ·
                    refine ⟨2108231070567487152517937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5621949521513299073381165 2108231070567487152517937)
                    ·
                      refine ⟨1581173302925615364388453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2108231070567487152517937 1581173302925615364388453)
                      ·
                        rfl

theorem cell23_3079324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_3079324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079324 prefixEnd_3079324 := by exact prefixLift 3079324
  have htrace : WordTrace (prefixWord ++ tailWord_3079324) baseStart_3079324 baseEnd_3079324 := by
    simpa [prefixWord, tailWord_3079324, baseEnd_3079324] using wordTrace_append hprefix tailTrace_3079324
  have hstable : (prefixWord ++ tailWord_3079324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079324).length < 2 ^ (prefixWord ++ tailWord_3079324).sum := by decide
  have hdescent : baseEnd_3079324 < baseStart_3079324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079343 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 7]
def baseStart_3079343 : Nat := 118140960795 + 3079343 * 2 ^ 59
def prefixEnd_3079343 : Nat := 4983230072969 + 3 ^ 40 * 3079343 * 2
def baseEnd_3079343 : Nat := 175687006562005643338985

theorem tailTrace_3079343 : CollatzResearch.WordTrace tailWord_3079343 prefixEnd_3079343 175687006562005643338985 := by
  unfold tailWord_3079343
  simp only [CollatzResearch.WordTrace]
  refine ⟨112312866083073695759682683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74875244055382463839788455 112312866083073695759682683)
  ·
    refine ⟨168469299124610543639524025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112312866083073695759682683 168469299124610543639524025)
    ·
      refine ⟨126351974343457907729643019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168469299124610543639524025 126351974343457907729643019)
      ·
        refine ⟨189527961515186861594464529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126351974343457907729643019 189527961515186861594464529)
        ·
          refine ⟨142145971136390146195848397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189527961515186861594464529 142145971136390146195848397)
          ·
            refine ⟨53304739176146304823443149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142145971136390146195848397 53304739176146304823443149)
            ·
              refine ⟨19989277191054864308791181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53304739176146304823443149 19989277191054864308791181)
              ·
                refine ⟨7495978946645574115796693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19989277191054864308791181 7495978946645574115796693)
                ·
                  refine ⟨175687006562005643338985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7495978946645574115796693 175687006562005643338985)
                  ·
                    rfl

theorem cell23_3079343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 7].length) (baseStart_3079343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079343 prefixEnd_3079343 := by exact prefixLift 3079343
  have htrace : WordTrace (prefixWord ++ tailWord_3079343) baseStart_3079343 baseEnd_3079343 := by
    simpa [prefixWord, tailWord_3079343, baseEnd_3079343] using wordTrace_append hprefix tailTrace_3079343
  have hstable : (prefixWord ++ tailWord_3079343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079343).length < 2 ^ (prefixWord ++ tailWord_3079343).sum := by decide
  have hdescent : baseEnd_3079343 < baseStart_3079343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079400 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3079400 : Nat := 118140960795 + 3079400 * 2 ^ 59
def prefixEnd_3079400 : Nat := 4983230072969 + 3 ^ 40 * 3079400 * 2
def baseEnd_3079400 : Nat := 1581212327455357067038103

theorem tailTrace_3079400 : CollatzResearch.WordTrace tailWord_3079400 prefixEnd_3079400 1581212327455357067038103 := by
  unfold tailWord_3079400
  simp only [CollatzResearch.WordTrace]
  refine ⟨56157472521933597247253827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74876630029244796329671769 56157472521933597247253827)
  ·
    refine ⟨84236208782900395870880741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56157472521933597247253827 84236208782900395870880741)
    ·
      refine ⟨15794289146793824225790139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84236208782900395870880741 15794289146793824225790139)
      ·
        refine ⟨23691433720190736338685209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15794289146793824225790139 23691433720190736338685209)
        ·
          refine ⟨17768575290143052254013907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23691433720190736338685209 17768575290143052254013907)
          ·
            refine ⟨26652862935214578381020861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17768575290143052254013907 26652862935214578381020861)
            ·
              refine ⟨9994823600705466892882823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26652862935214578381020861 9994823600705466892882823)
              ·
                refine ⟨14992235401058200339324235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9994823600705466892882823 14992235401058200339324235)
                ·
                  refine ⟨22488353101587300508986353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14992235401058200339324235 22488353101587300508986353)
                  ·
                    refine ⟨16866264826190475381739765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22488353101587300508986353 16866264826190475381739765)
                    ·
                      refine ⟨1581212327455357067038103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16866264826190475381739765 1581212327455357067038103)
                      ·
                        rfl

theorem cell23_3079400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3079400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079400 prefixEnd_3079400 := by exact prefixLift 3079400
  have htrace : WordTrace (prefixWord ++ tailWord_3079400) baseStart_3079400 baseEnd_3079400 := by
    simpa [prefixWord, tailWord_3079400, baseEnd_3079400] using wordTrace_append hprefix tailTrace_3079400
  have hstable : (prefixWord ++ tailWord_3079400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079400).length < 2 ^ (prefixWord ++ tailWord_3079400).sum := by decide
  have hdescent : baseEnd_3079400 < baseStart_3079400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079427 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 4]
def baseStart_3079427 : Nat := 118140960795 + 3079427 * 2 ^ 59
def prefixEnd_3079427 : Nat := 4983230072969 + 3 ^ 40 * 3079427 * 2
def baseEnd_3079427 : Nat := 1581226191433028461400479

theorem tailTrace_3079427 : CollatzResearch.WordTrace tailWord_3079427 prefixEnd_3079427 1581226191433028461400479 := by
  unfold tailWord_3079427
  simp only [CollatzResearch.WordTrace]
  refine ⟨112315929814769378105740535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74877286543179585403827023 112315929814769378105740535)
  ·
    refine ⟨168473894722154067158610803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112315929814769378105740535 168473894722154067158610803)
    ·
      refine ⟨252710842083231100737916205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168473894722154067158610803 252710842083231100737916205)
      ·
        refine ⟨94766565781211662776718577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252710842083231100737916205 94766565781211662776718577)
        ·
          refine ⟨71074924335908747082538933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94766565781211662776718577 71074924335908747082538933)
          ·
            refine ⟨6663274156491445038988025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71074924335908747082538933 6663274156491445038988025)
            ·
              refine ⟨4997455617368583779241019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6663274156491445038988025 4997455617368583779241019)
              ·
                refine ⟨7496183426052875668861529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997455617368583779241019 7496183426052875668861529)
                ·
                  refine ⟨5622137569539656751646147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7496183426052875668861529 5622137569539656751646147)
                  ·
                    refine ⟨8433206354309485127469221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5622137569539656751646147 8433206354309485127469221)
                    ·
                      refine ⟨1581226191433028461400479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8433206354309485127469221 1581226191433028461400479)
                      ·
                        rfl

theorem cell23_3079427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_3079427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079427 prefixEnd_3079427 := by exact prefixLift 3079427
  have htrace : WordTrace (prefixWord ++ tailWord_3079427) baseStart_3079427 baseEnd_3079427 := by
    simpa [prefixWord, tailWord_3079427, baseEnd_3079427] using wordTrace_append hprefix tailTrace_3079427
  have hstable : (prefixWord ++ tailWord_3079427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079427).length < 2 ^ (prefixWord ++ tailWord_3079427).sum := by decide
  have hdescent : baseEnd_3079427 < baseStart_3079427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079447 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3079447 : Nat := 118140960795 + 3079447 * 2 ^ 59
def prefixEnd_3079447 : Nat := 4983230072969 + 3 ^ 40 * 3079447 * 2
def baseEnd_3079447 : Nat := 1581236461046118383150387

theorem tailTrace_3079447 : CollatzResearch.WordTrace tailWord_3079447 prefixEnd_3079447 1581236461046118383150387 := by
  unfold tailWord_3079447
  simp only [CollatzResearch.WordTrace]
  refine ⟨112316659274696921521468595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74877772849797947680979063 112316659274696921521468595)
  ·
    refine ⟨168474988912045382282202893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112316659274696921521468595 168474988912045382282202893)
    ·
      refine ⟨63178120842017018355826085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168474988912045382282202893 63178120842017018355826085)
      ·
        refine ⟨11845897657878190941717391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63178120842017018355826085 11845897657878190941717391)
        ·
          refine ⟨17768846486817286412576087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11845897657878190941717391 17768846486817286412576087)
          ·
            refine ⟨26653269730225929618864131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17768846486817286412576087 26653269730225929618864131)
            ·
              refine ⟨39979904595338894428296197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26653269730225929618864131 39979904595338894428296197)
              ·
                refine ⟨7496232111626042705305537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39979904595338894428296197 7496232111626042705305537)
                ·
                  refine ⟨5622174083719532028979153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7496232111626042705305537 5622174083719532028979153)
                  ·
                    refine ⟨4216630562789649021734365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5622174083719532028979153 4216630562789649021734365)
                    ·
                      refine ⟨1581236461046118383150387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4216630562789649021734365 1581236461046118383150387)
                      ·
                        rfl

theorem cell23_3079447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3079447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079447 prefixEnd_3079447 := by exact prefixLift 3079447
  have htrace : WordTrace (prefixWord ++ tailWord_3079447) baseStart_3079447 baseEnd_3079447 := by
    simpa [prefixWord, tailWord_3079447, baseEnd_3079447] using wordTrace_append hprefix tailTrace_3079447
  have hstable : (prefixWord ++ tailWord_3079447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079447).length < 2 ^ (prefixWord ++ tailWord_3079447).sum := by decide
  have hdescent : baseEnd_3079447 < baseStart_3079447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079478 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3079478 : Nat := 118140960795 + 3079478 * 2 ^ 59
def prefixEnd_3079478 : Nat := 4983230072969 + 3 ^ 40 * 3079478 * 2
def baseEnd_3079478 : Nat := 1581252378946407761862745

theorem tailTrace_3079478 : CollatzResearch.WordTrace tailWord_3079478 prefixEnd_3079478 1581252378946407761862745 := by
  unfold tailWord_3079478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7019861871099038363490443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74878526625056409210564725 7019861871099038363490443)
  ·
    refine ⟨10529792806648557545235665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7019861871099038363490443 10529792806648557545235665)
    ·
      refine ⟨7897344604986418158926749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10529792806648557545235665 7897344604986418158926749)
      ·
        refine ⟨2961504226869906809597531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7897344604986418158926749 2961504226869906809597531)
        ·
          refine ⟨4442256340304860214396297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2961504226869906809597531 4442256340304860214396297)
          ·
            refine ⟨3331692255228645160797223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4442256340304860214396297 3331692255228645160797223)
            ·
              refine ⟨4997538382842967741195835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331692255228645160797223 4997538382842967741195835)
              ·
                refine ⟨7496307574264451611793753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997538382842967741195835 7496307574264451611793753)
                ·
                  refine ⟨5622230680698338708845315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7496307574264451611793753 5622230680698338708845315)
                  ·
                    refine ⟨8433346021047508063267973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5622230680698338708845315 8433346021047508063267973)
                    ·
                      refine ⟨1581252378946407761862745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8433346021047508063267973 1581252378946407761862745)
                      ·
                        rfl

theorem cell23_3079478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3079478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079478 prefixEnd_3079478 := by exact prefixLift 3079478
  have htrace : WordTrace (prefixWord ++ tailWord_3079478) baseStart_3079478 baseEnd_3079478 := by
    simpa [prefixWord, tailWord_3079478, baseEnd_3079478] using wordTrace_append hprefix tailTrace_3079478
  have hstable : (prefixWord ++ tailWord_3079478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079478).length < 2 ^ (prefixWord ++ tailWord_3079478).sum := by decide
  have hdescent : baseEnd_3079478 < baseStart_3079478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079481 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3079481 : Nat := 118140960795 + 3079481 * 2 ^ 59
def prefixEnd_3079481 : Nat := 4983230072969 + 3 ^ 40 * 3079481 * 2
def baseEnd_3079481 : Nat := 1581253919388371250125231

theorem tailTrace_3079481 : CollatzResearch.WordTrace tailWord_3079481 prefixEnd_3079481 1581253919388371250125231 := by
  unfold tailWord_3079481
  simp only [CollatzResearch.WordTrace]
  refine ⟨112317899356573745328206297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74878599571049163552137531 112317899356573745328206297)
  ·
    refine ⟨84238424517430308996154723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112317899356573745328206297 84238424517430308996154723)
    ·
      refine ⟨126357636776145463494232085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84238424517430308996154723 126357636776145463494232085)
      ·
        refine ⟨5923014223881818601292129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126357636776145463494232085 5923014223881818601292129)
        ·
          refine ⟨4442260667911363950969097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5923014223881818601292129 4442260667911363950969097)
          ·
            refine ⟨3331695500933522963226823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4442260667911363950969097 3331695500933522963226823)
            ·
              refine ⟨4997543251400284444840235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331695500933522963226823 4997543251400284444840235)
              ·
                refine ⟨7496314877100426667260353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997543251400284444840235 7496314877100426667260353)
                ·
                  refine ⟨5622236157825320000445265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7496314877100426667260353 5622236157825320000445265)
                  ·
                    refine ⟨4216677118368990000333949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5622236157825320000445265 4216677118368990000333949)
                    ·
                      refine ⟨1581253919388371250125231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4216677118368990000333949 1581253919388371250125231)
                      ·
                        rfl

theorem cell23_3079481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3079481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079481 prefixEnd_3079481 := by exact prefixLift 3079481
  have htrace : WordTrace (prefixWord ++ tailWord_3079481) baseStart_3079481 baseEnd_3079481 := by
    simpa [prefixWord, tailWord_3079481, baseEnd_3079481] using wordTrace_append hprefix tailTrace_3079481
  have hstable : (prefixWord ++ tailWord_3079481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079481).length < 2 ^ (prefixWord ++ tailWord_3079481).sum := by decide
  have hdescent : baseEnd_3079481 < baseStart_3079481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079511 : List Nat := [1, 1, 3, 2, 3, 2, 2, 4, 1, 1, 3]
def baseStart_3079511 : Nat := 118140960795 + 3079511 * 2 ^ 59
def prefixEnd_3079511 : Nat := 4983230072969 + 3 ^ 40 * 3079511 * 2
def baseEnd_3079511 : Nat := 1581269323808006132750093

theorem tailTrace_3079511 : CollatzResearch.WordTrace tailWord_3079511 prefixEnd_3079511 1581269323808006132750093 := by
  unfold tailWord_3079511
  simp only [CollatzResearch.WordTrace]
  refine ⟨112318993546465060451798387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74879329030976706967865591 112318993546465060451798387)
  ·
    refine ⟨168478490319697590677697581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112318993546465060451798387 168478490319697590677697581)
    ·
      refine ⟨63179433869886596504136593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168478490319697590677697581 63179433869886596504136593)
      ·
        refine ⟨47384575402414947378102445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63179433869886596504136593 47384575402414947378102445)
        ·
          refine ⟨17769215775905605266788417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47384575402414947378102445 17769215775905605266788417)
          ·
            refine ⟨13326911831929203950091313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17769215775905605266788417 13326911831929203950091313)
            ·
              refine ⟨9995183873946902962568485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13326911831929203950091313 9995183873946902962568485)
              ·
                refine ⟨1874096976365044305481591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9995183873946902962568485 1874096976365044305481591)
                ·
                  refine ⟨2811145464547566458222387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874096976365044305481591 2811145464547566458222387)
                  ·
                    refine ⟨4216718196821349687333581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2811145464547566458222387 4216718196821349687333581)
                    ·
                      refine ⟨1581269323808006132750093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4216718196821349687333581 1581269323808006132750093)
                      ·
                        rfl

theorem cell23_3079511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_3079511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079511 prefixEnd_3079511 := by exact prefixLift 3079511
  have htrace : WordTrace (prefixWord ++ tailWord_3079511) baseStart_3079511 baseEnd_3079511 := by
    simpa [prefixWord, tailWord_3079511, baseEnd_3079511] using wordTrace_append hprefix tailTrace_3079511
  have hstable : (prefixWord ++ tailWord_3079511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079511).length < 2 ^ (prefixWord ++ tailWord_3079511).sum := by decide
  have hdescent : baseEnd_3079511 < baseStart_3079511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079537 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 3]
def baseStart_3079537 : Nat := 118140960795 + 3079537 * 2 ^ 59
def prefixEnd_3079537 : Nat := 4983230072969 + 3 ^ 40 * 3079537 * 2
def baseEnd_3079537 : Nat := 1581282674305023031024973

theorem tailTrace_3079537 : CollatzResearch.WordTrace tailWord_3079537 prefixEnd_3079537 1581282674305023031024973 := by
  unfold tailWord_3079537
  simp only [CollatzResearch.WordTrace]
  refine ⟨112319941844370866892244865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74879961229580577928163243 112319941844370866892244865)
  ·
    refine ⟨84239956383278150169183649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112319941844370866892244865 84239956383278150169183649)
    ·
      refine ⟨63179967287458612626887737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84239956383278150169183649 63179967287458612626887737)
      ·
        refine ⟨47384975465593959470165803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63179967287458612626887737 47384975465593959470165803)
        ·
          refine ⟨71077463198390939205248705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47384975465593959470165803 71077463198390939205248705)
          ·
            refine ⟨53308097398793204403936529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71077463198390939205248705 53308097398793204403936529)
            ·
              refine ⟨39981073049094903302952397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53308097398793204403936529 39981073049094903302952397)
              ·
                refine ⟨14992902393410588738607149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39981073049094903302952397 14992902393410588738607149)
                ·
                  refine ⟨5622338397528970776977681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14992902393410588738607149 5622338397528970776977681)
                  ·
                    refine ⟨4216753798146728082733261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5622338397528970776977681 4216753798146728082733261)
                    ·
                      refine ⟨1581282674305023031024973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4216753798146728082733261 1581282674305023031024973)
                      ·
                        rfl

theorem cell23_3079537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_3079537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079537 prefixEnd_3079537 := by exact prefixLift 3079537
  have htrace : WordTrace (prefixWord ++ tailWord_3079537) baseStart_3079537 baseEnd_3079537 := by
    simpa [prefixWord, tailWord_3079537, baseEnd_3079537] using wordTrace_append hprefix tailTrace_3079537
  have hstable : (prefixWord ++ tailWord_3079537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079537).length < 2 ^ (prefixWord ++ tailWord_3079537).sum := by decide
  have hdescent : baseEnd_3079537 < baseStart_3079537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079600 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 3, 8]
def baseStart_3079600 : Nat := 118140960795 + 3079600 * 2 ^ 59
def prefixEnd_3079600 : Nat := 4983230072969 + 3 ^ 40 * 3079600 * 2
def baseEnd_3079600 : Nat := 527105007862085428179061

theorem tailTrace_3079600 : CollatzResearch.WordTrace tailWord_3079600 prefixEnd_3079600 527105007862085428179061 := by
  unfold tailWord_3079600
  simp only [CollatzResearch.WordTrace]
  refine ⟨56161119821571314325894127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74881493095428419101192169 56161119821571314325894127)
  ·
    refine ⟨84241679732356971488841191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56161119821571314325894127 84241679732356971488841191)
    ·
      refine ⟨126362519598535457233261787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84241679732356971488841191 126362519598535457233261787)
      ·
        refine ⟨189543779397803185849892681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126362519598535457233261787 189543779397803185849892681)
        ·
          refine ⟨142157834548352389387419511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189543779397803185849892681 142157834548352389387419511)
          ·
            refine ⟨213236751822528584081129267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142157834548352389387419511 213236751822528584081129267)
            ·
              refine ⟨319855127733792876121693901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213236751822528584081129267 319855127733792876121693901)
              ·
                refine ⟨119945672900172328545635213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319855127733792876121693901 119945672900172328545635213)
                ·
                  refine ⟨44979627337564623204613205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119945672900172328545635213 44979627337564623204613205)
                  ·
                    refine ⟨527105007862085428179061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44979627337564623204613205 527105007862085428179061)
                    ·
                      rfl

theorem cell23_3079600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_3079600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079600 prefixEnd_3079600 := by exact prefixLift 3079600
  have htrace : WordTrace (prefixWord ++ tailWord_3079600) baseStart_3079600 baseEnd_3079600 := by
    simpa [prefixWord, tailWord_3079600, baseEnd_3079600] using wordTrace_append hprefix tailTrace_3079600
  have hstable : (prefixWord ++ tailWord_3079600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079600).length < 2 ^ (prefixWord ++ tailWord_3079600).sum := by decide
  have hdescent : baseEnd_3079600 < baseStart_3079600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079624 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 3, 4, 2]
def baseStart_3079624 : Nat := 118140960795 + 3079624 * 2 ^ 59
def prefixEnd_3079624 : Nat := 4983230072969 + 3 ^ 40 * 3079624 * 2
def baseEnd_3079624 : Nat := 1581327347121964190637073

theorem tailTrace_3079624 : CollatzResearch.WordTrace tailWord_3079624 prefixEnd_3079624 1581327347121964190637073 := by
  unfold tailWord_3079624
  simp only [CollatzResearch.WordTrace]
  refine ⟨56161557497527840375330963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74882076663370453833774617 56161557497527840375330963)
  ·
    refine ⟨84242336246291760562996445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56161557497527840375330963 84242336246291760562996445)
    ·
      refine ⟨31590876092359410211123667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84242336246291760562996445 31590876092359410211123667)
      ·
        refine ⟨47386314138539115316685501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31590876092359410211123667 47386314138539115316685501)
        ·
          refine ⟨17769867801952168243757063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47386314138539115316685501 17769867801952168243757063)
          ·
            refine ⟨26654801702928252365635595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17769867801952168243757063 26654801702928252365635595)
            ·
              refine ⟨39982202554392378548453393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26654801702928252365635595 39982202554392378548453393)
              ·
                refine ⟨29986651915794283911340045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39982202554392378548453393 29986651915794283911340045)
                ·
                  refine ⟨11244994468422856466752517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29986651915794283911340045 11244994468422856466752517)
                  ·
                    refine ⟨2108436462829285587516097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11244994468422856466752517 2108436462829285587516097)
                    ·
                      refine ⟨1581327347121964190637073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2108436462829285587516097 1581327347121964190637073)
                      ·
                        rfl

theorem cell23_3079624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_3079624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079624 prefixEnd_3079624 := by exact prefixLift 3079624
  have htrace : WordTrace (prefixWord ++ tailWord_3079624) baseStart_3079624 baseEnd_3079624 := by
    simpa [prefixWord, tailWord_3079624, baseEnd_3079624] using wordTrace_append hprefix tailTrace_3079624
  have hstable : (prefixWord ++ tailWord_3079624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079624).length < 2 ^ (prefixWord ++ tailWord_3079624).sum := by decide
  have hdescent : baseEnd_3079624 < baseStart_3079624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079627 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 3]
def baseStart_3079627 : Nat := 118140960795 + 3079627 * 2 ^ 59
def prefixEnd_3079627 : Nat := 4983230072969 + 3 ^ 40 * 3079627 * 2
def baseEnd_3079627 : Nat := 1581328887563927678899559

theorem tailTrace_3079627 : CollatzResearch.WordTrace tailWord_3079627 prefixEnd_3079627 1581328887563927678899559 := by
  unfold tailWord_3079627
  simp only [CollatzResearch.WordTrace]
  refine ⟨112323224414044812263021135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74882149609363208175347423 112323224414044812263021135)
  ·
    refine ⟨168484836621067218394531703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112323224414044812263021135 168484836621067218394531703)
    ·
      refine ⟨252727254931600827591797555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168484836621067218394531703 252727254931600827591797555)
      ·
        refine ⟨379090882397401241387696333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252727254931600827591797555 379090882397401241387696333)
        ·
          refine ⟨142159080899025465520386125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379090882397401241387696333 142159080899025465520386125)
          ·
            refine ⟨53309655337134549570144797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142159080899025465520386125 53309655337134549570144797)
            ·
              refine ⟨19991120751425456088804299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53309655337134549570144797 19991120751425456088804299)
              ·
                refine ⟨29986681127138184133206449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19991120751425456088804299 29986681127138184133206449)
                ·
                  refine ⟨22490010845353638099904837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29986681127138184133206449 22490010845353638099904837)
                  ·
                    refine ⟨4216877033503807143732157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22490010845353638099904837 4216877033503807143732157)
                    ·
                      refine ⟨1581328887563927678899559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4216877033503807143732157 1581328887563927678899559)
                      ·
                        rfl

theorem cell23_3079627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 3].length) (baseStart_3079627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079627 prefixEnd_3079627 := by exact prefixLift 3079627
  have htrace : WordTrace (prefixWord ++ tailWord_3079627) baseStart_3079627 baseEnd_3079627 := by
    simpa [prefixWord, tailWord_3079627, baseEnd_3079627] using wordTrace_append hprefix tailTrace_3079627
  have hstable : (prefixWord ++ tailWord_3079627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079627).length < 2 ^ (prefixWord ++ tailWord_3079627).sum := by decide
  have hdescent : baseEnd_3079627 < baseStart_3079627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079641 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 1, 4, 2]
def baseStart_3079641 : Nat := 118140960795 + 3079641 * 2 ^ 59
def prefixEnd_3079641 : Nat := 4983230072969 + 3 ^ 40 * 3079641 * 2
def baseEnd_3079641 : Nat := 1581336076293090624124495

theorem tailTrace_3079641 : CollatzResearch.WordTrace tailWord_3079641 prefixEnd_3079641 1581336076293090624124495 := by
  unfold tailWord_3079641
  simp only [CollatzResearch.WordTrace]
  refine ⟨112323735035994092654030777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74882490023996061769353851 112323735035994092654030777)
  ·
    refine ⟨84242801276995569490523083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112323735035994092654030777 84242801276995569490523083)
    ·
      refine ⟨126364201915493354235784625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84242801276995569490523083 126364201915493354235784625)
      ·
        refine ⟨94773151436620015676838469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126364201915493354235784625 94773151436620015676838469)
        ·
          refine ⟨17769965894366252939407213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94773151436620015676838469 17769965894366252939407213)
          ·
            refine ⟨6663737210387344852277705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17769965894366252939407213 6663737210387344852277705)
            ·
              refine ⟨4997802907790508639208279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6663737210387344852277705 4997802907790508639208279)
              ·
                refine ⟨7496704361685762958812419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997802907790508639208279 7496704361685762958812419)
                ·
                  refine ⟨11245056542528644438218629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7496704361685762958812419 11245056542528644438218629)
                  ·
                    refine ⟨2108448101724120832165993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11245056542528644438218629 2108448101724120832165993)
                    ·
                      refine ⟨1581336076293090624124495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2108448101724120832165993 1581336076293090624124495)
                      ·
                        rfl

theorem cell23_3079641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_3079641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079641 prefixEnd_3079641 := by exact prefixLift 3079641
  have htrace : WordTrace (prefixWord ++ tailWord_3079641) baseStart_3079641 baseEnd_3079641 := by
    simpa [prefixWord, tailWord_3079641, baseEnd_3079641] using wordTrace_append hprefix tailTrace_3079641
  have hstable : (prefixWord ++ tailWord_3079641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079641).length < 2 ^ (prefixWord ++ tailWord_3079641).sum := by decide
  have hdescent : baseEnd_3079641 < baseStart_3079641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079647 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 7]
def baseStart_3079647 : Nat := 118140960795 + 3079647 * 2 ^ 59
def prefixEnd_3079647 : Nat := 4983230072969 + 3 ^ 40 * 3079647 * 2
def baseEnd_3079647 : Nat := 175704350797446400072163

theorem tailTrace_3079647 : CollatzResearch.WordTrace tailWord_3079647 prefixEnd_3079647 175704350797446400072163 := by
  unfold tailWord_3079647
  simp only [CollatzResearch.WordTrace]
  refine ⟨112323953873972355678749195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74882635915981570452499463 112323953873972355678749195)
  ·
    refine ⟨168485930810958533518123793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112323953873972355678749195 168485930810958533518123793)
    ·
      refine ⟨126364448108218900138592845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168485930810958533518123793 126364448108218900138592845)
      ·
        refine ⟨47386668040582087551972317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126364448108218900138592845 47386668040582087551972317)
        ·
          refine ⟨17770000515218282831989619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47386668040582087551972317 17770000515218282831989619)
          ·
            refine ⟨26655000772827424247984429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17770000515218282831989619 26655000772827424247984429)
            ·
              refine ⟨9995625289810284092994161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26655000772827424247984429 9995625289810284092994161)
              ·
                refine ⟨7496718967357713069745621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9995625289810284092994161 7496718967357713069745621)
                ·
                  refine ⟨175704350797446400072163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7496718967357713069745621 175704350797446400072163)
                  ·
                    rfl

theorem cell23_3079647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 7].length) (baseStart_3079647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079647 prefixEnd_3079647 := by exact prefixLift 3079647
  have htrace : WordTrace (prefixWord ++ tailWord_3079647) baseStart_3079647 baseEnd_3079647 := by
    simpa [prefixWord, tailWord_3079647, baseEnd_3079647] using wordTrace_append hprefix tailTrace_3079647
  have hstable : (prefixWord ++ tailWord_3079647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079647).length < 2 ^ (prefixWord ++ tailWord_3079647).sum := by decide
  have hdescent : baseEnd_3079647 < baseStart_3079647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079664 : List Nat := [2, 1, 1, 1, 3, 4, 1, 5, 5]
def baseStart_3079664 : Nat := 118140960795 + 3079664 * 2 ^ 59
def prefixEnd_3079664 : Nat := 4983230072969 + 3 ^ 40 * 3079664 * 2
def baseEnd_3079664 : Nat := 175705320705349337126321

theorem tailTrace_3079664 : CollatzResearch.WordTrace tailWord_3079664 prefixEnd_3079664 175705320705349337126321 := by
  unfold tailWord_3079664
  simp only [CollatzResearch.WordTrace]
  refine ⟨56162286957455383791059023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74883049276607178388078697 56162286957455383791059023)
  ·
    refine ⟨84243430436183075686588535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56162286957455383791059023 84243430436183075686588535)
    ·
      refine ⟨126365145654274613529882803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84243430436183075686588535 126365145654274613529882803)
      ·
        refine ⟨189547718481411920294824205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126365145654274613529882803 189547718481411920294824205)
        ·
          refine ⟨71080394430529470110559077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189547718481411920294824205 71080394430529470110559077)
          ·
            refine ⟨13327573955724275645729827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71080394430529470110559077 13327573955724275645729827)
            ·
              refine ⟨19991360933586413468594741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13327573955724275645729827 19991360933586413468594741)
              ·
                refine ⟨1874190087523726262680757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19991360933586413468594741 1874190087523726262680757)
                ·
                  refine ⟨175705320705349337126321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1874190087523726262680757 175705320705349337126321)
                  ·
                    rfl

theorem cell23_3079664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 5].length) (baseStart_3079664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079664 prefixEnd_3079664 := by exact prefixLift 3079664
  have htrace : WordTrace (prefixWord ++ tailWord_3079664) baseStart_3079664 baseEnd_3079664 := by
    simpa [prefixWord, tailWord_3079664, baseEnd_3079664] using wordTrace_append hprefix tailTrace_3079664
  have hstable : (prefixWord ++ tailWord_3079664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079664).length < 2 ^ (prefixWord ++ tailWord_3079664).sum := by decide
  have hdescent : baseEnd_3079664 < baseStart_3079664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079697 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_3079697 : Nat := 118140960795 + 3079697 * 2 ^ 59
def prefixEnd_3079697 : Nat := 4983230072969 + 3 ^ 40 * 3079697 * 2
def baseEnd_3079697 : Nat := 1581364831209742405024237

theorem tailTrace_3079697 : CollatzResearch.WordTrace tailWord_3079697 prefixEnd_3079697 1581364831209742405024237 := by
  unfold tailWord_3079697
  simp only [CollatzResearch.WordTrace]
  refine ⟨112325777523791214218069345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74883851682527476145379563 112325777523791214218069345)
  ·
    refine ⟨84244333142843410663552009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112325777523791214218069345 84244333142843410663552009)
    ·
      refine ⟨63183249857132557997664007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84244333142843410663552009 63183249857132557997664007)
      ·
        refine ⟨94774874785698836996496011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63183249857132557997664007 94774874785698836996496011)
        ·
          refine ⟨142162312178548255494744017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94774874785698836996496011 142162312178548255494744017)
          ·
            refine ⟨106621734133911191621058013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142162312178548255494744017 106621734133911191621058013)
            ·
              refine ⟨39983150300216696857896755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106621734133911191621058013 39983150300216696857896755)
              ·
                refine ⟨59974725450325045286845133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39983150300216696857896755 59974725450325045286845133)
                ·
                  refine ⟨22490522043871891982566925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59974725450325045286845133 22490522043871891982566925)
                  ·
                    refine ⟨8433945766451959493462597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22490522043871891982566925 8433945766451959493462597)
                    ·
                      refine ⟨1581364831209742405024237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8433945766451959493462597 1581364831209742405024237)
                      ·
                        rfl

theorem cell23_3079697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_3079697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079697 prefixEnd_3079697 := by exact prefixLift 3079697
  have htrace : WordTrace (prefixWord ++ tailWord_3079697) baseStart_3079697 baseEnd_3079697 := by
    simpa [prefixWord, tailWord_3079697, baseEnd_3079697] using wordTrace_append hprefix tailTrace_3079697
  have hstable : (prefixWord ++ tailWord_3079697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079697).length < 2 ^ (prefixWord ++ tailWord_3079697).sum := by decide
  have hdescent : baseEnd_3079697 < baseStart_3079697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079714 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3079714 : Nat := 118140960795 + 3079714 * 2 ^ 59
def prefixEnd_3079714 : Nat := 4983230072969 + 3 ^ 40 * 3079714 * 2
def baseEnd_3079714 : Nat := 1581373560380868838511659

theorem tailTrace_3079714 : CollatzResearch.WordTrace tailWord_3079714 prefixEnd_3079714 1581373560380868838511659 := by
  unfold tailWord_3079714
  simp only [CollatzResearch.WordTrace]
  refine ⟨28081599391182406530359549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74884265043153084080958797 28081599391182406530359549)
  ·
    refine ⟨10530599771693402448884831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28081599391182406530359549 10530599771693402448884831)
    ·
      refine ⟨15795899657540103673327247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10530599771693402448884831 15795899657540103673327247)
      ·
        refine ⟨23693849486310155509990871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15795899657540103673327247 23693849486310155509990871)
        ·
          refine ⟨35540774229465233264986307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23693849486310155509990871 35540774229465233264986307)
          ·
            refine ⟨53311161344197849897479461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35540774229465233264986307 53311161344197849897479461)
            ·
              refine ⟨9995842752037096855777399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53311161344197849897479461 9995842752037096855777399)
              ·
                refine ⟨14993764128055645283666099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9995842752037096855777399 14993764128055645283666099)
                ·
                  refine ⟨22490646192083467925499149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14993764128055645283666099 22490646192083467925499149)
                  ·
                    refine ⟨8433992322031300472062181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22490646192083467925499149 8433992322031300472062181)
                    ·
                      refine ⟨1581373560380868838511659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8433992322031300472062181 1581373560380868838511659)
                      ·
                        rfl

theorem cell23_3079714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3079714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079714 prefixEnd_3079714 := by exact prefixLift 3079714
  have htrace : WordTrace (prefixWord ++ tailWord_3079714) baseStart_3079714 baseEnd_3079714 := by
    simpa [prefixWord, tailWord_3079714, baseEnd_3079714] using wordTrace_append hprefix tailTrace_3079714
  have hstable : (prefixWord ++ tailWord_3079714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079714).length < 2 ^ (prefixWord ++ tailWord_3079714).sum := by decide
  have hdescent : baseEnd_3079714 < baseStart_3079714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079717 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_3079717 : Nat := 118140960795 + 3079717 * 2 ^ 59
def prefixEnd_3079717 : Nat := 4983230072969 + 3 ^ 40 * 3079717 * 2
def baseEnd_3079717 : Nat := 1581375100822832326774145

theorem tailTrace_3079717 : CollatzResearch.WordTrace tailWord_3079717 prefixEnd_3079717 1581375100822832326774145 := by
  unfold tailWord_3079717
  simp only [CollatzResearch.WordTrace]
  refine ⟨112326506983718757633797405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74884337989145838422531603 112326506983718757633797405)
  ·
    refine ⟨42122440118894534112674027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112326506983718757633797405 42122440118894534112674027)
    ·
      refine ⟨63183660178341801169011041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42122440118894534112674027 63183660178341801169011041)
      ·
        refine ⟨47387745133756350876758281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63183660178341801169011041 47387745133756350876758281)
        ·
          refine ⟨35540808850317263157568711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47387745133756350876758281 35540808850317263157568711)
          ·
            refine ⟨53311213275475894736353067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35540808850317263157568711 53311213275475894736353067)
            ·
              refine ⟨79966819913213842104529601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53311213275475894736353067 79966819913213842104529601)
              ·
                refine ⟨59975114934910381578397201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79966819913213842104529601 59975114934910381578397201)
                ·
                  refine ⟨44981336201182786183797901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59975114934910381578397201 44981336201182786183797901)
                  ·
                    refine ⟨16868001075443544818924213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44981336201182786183797901 16868001075443544818924213)
                    ·
                      refine ⟨1581375100822832326774145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16868001075443544818924213 1581375100822832326774145)
                      ·
                        rfl

theorem cell23_3079717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_3079717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079717 prefixEnd_3079717 := by exact prefixLift 3079717
  have htrace : WordTrace (prefixWord ++ tailWord_3079717) baseStart_3079717 baseEnd_3079717 := by
    simpa [prefixWord, tailWord_3079717, baseEnd_3079717] using wordTrace_append hprefix tailTrace_3079717
  have hstable : (prefixWord ++ tailWord_3079717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079717).length < 2 ^ (prefixWord ++ tailWord_3079717).sum := by decide
  have hdescent : baseEnd_3079717 < baseStart_3079717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079754 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 6]
def baseStart_3079754 : Nat := 118140960795 + 3079754 * 2 ^ 59
def prefixEnd_3079754 : Nat := 4983230072969 + 3 ^ 40 * 3079754 * 2
def baseEnd_3079754 : Nat := 175710455511894298001275

theorem tailTrace_3079754 : CollatzResearch.WordTrace tailWord_3079754 prefixEnd_3079754 175710455511894298001275 := by
  unfold tailWord_3079754
  simp only [CollatzResearch.WordTrace]
  refine ⟨28081964121146178238223579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74885237656389808635262877 28081964121146178238223579)
  ·
    refine ⟨42122946181719267357335369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28081964121146178238223579 42122946181719267357335369)
    ·
      refine ⟨31592209636289450518001527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42122946181719267357335369 31592209636289450518001527)
      ·
        refine ⟨47388314454434175777002291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31592209636289450518001527 47388314454434175777002291)
        ·
          refine ⟨71082471681651263665503437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47388314454434175777002291 71082471681651263665503437)
          ·
            refine ⟨26655926880619223874563789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71082471681651263665503437 26655926880619223874563789)
            ·
              refine ⟨9995972580232208952961421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26655926880619223874563789 9995972580232208952961421)
              ·
                refine ⟨3748489717587078357360533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9995972580232208952961421 3748489717587078357360533)
                ·
                  refine ⟨175710455511894298001275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3748489717587078357360533 175710455511894298001275)
                  ·
                    rfl

theorem cell23_3079754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_3079754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079754 prefixEnd_3079754 := by exact prefixLift 3079754
  have htrace : WordTrace (prefixWord ++ tailWord_3079754) baseStart_3079754 baseEnd_3079754 := by
    simpa [prefixWord, tailWord_3079754, baseEnd_3079754] using wordTrace_append hprefix tailTrace_3079754
  have hstable : (prefixWord ++ tailWord_3079754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079754).length < 2 ^ (prefixWord ++ tailWord_3079754).sum := by decide
  have hdescent : baseEnd_3079754 < baseStart_3079754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079844 : List Nat := [2, 3, 1, 2, 2, 3, 10]
def baseStart_3079844 : Nat := 118140960795 + 3079844 * 2 ^ 59
def prefixEnd_3079844 : Nat := 4983230072969 + 3 ^ 40 * 3079844 * 2
def baseEnd_3079844 : Nat := 19523954479826584319581

theorem tailTrace_3079844 : CollatzResearch.WordTrace tailWord_3079844 prefixEnd_3079844 19523954479826584319581 := by
  unfold tailWord_3079844
  simp only [CollatzResearch.WordTrace]
  refine ⟨56165569527129329161835293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74887426036172438882447057 56165569527129329161835293)
  ·
    refine ⟨21062088572673498435688235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56165569527129329161835293 21062088572673498435688235)
    ·
      refine ⟨31593132859010247653532353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21062088572673498435688235 31593132859010247653532353)
      ·
        refine ⟨23694849644257685740149265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31593132859010247653532353 23694849644257685740149265)
        ·
          refine ⟨17771137233193264305111949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23694849644257685740149265 17771137233193264305111949)
          ·
            refine ⟨6664176462447474114416981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17771137233193264305111949 6664176462447474114416981)
            ·
              refine ⟨19523954479826584319581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6664176462447474114416981 19523954479826584319581)
              ·
                rfl

theorem cell23_3079844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 10].length) (baseStart_3079844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079844 prefixEnd_3079844 := by exact prefixLift 3079844
  have htrace : WordTrace (prefixWord ++ tailWord_3079844) baseStart_3079844 baseEnd_3079844 := by
    simpa [prefixWord, tailWord_3079844, baseEnd_3079844] using wordTrace_append hprefix tailTrace_3079844
  have hstable : (prefixWord ++ tailWord_3079844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079844).length < 2 ^ (prefixWord ++ tailWord_3079844).sum := by decide
  have hdescent : baseEnd_3079844 < baseStart_3079844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079855 : List Nat := [1, 1, 2, 1, 2, 4, 1, 6, 1, 2, 2]
def baseStart_3079855 : Nat := 118140960795 + 3079855 * 2 ^ 59
def prefixEnd_3079855 : Nat := 4983230072969 + 3 ^ 40 * 3079855 * 2
def baseEnd_3079855 : Nat := 1581445961153152786848511

theorem tailTrace_3079855 : CollatzResearch.WordTrace tailWord_3079855 prefixEnd_3079855 1581445961153152786848511 := by
  unfold tailWord_3079855
  simp only [CollatzResearch.WordTrace]
  refine ⟨112331540257218807202321019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74887693504812538134880679 112331540257218807202321019)
  ·
    refine ⟨168497310385828210803481529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112331540257218807202321019 168497310385828210803481529)
    ·
      refine ⟨126372982789371158102611147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168497310385828210803481529 126372982789371158102611147)
      ·
        refine ⟨189559474184056737153916721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126372982789371158102611147 189559474184056737153916721)
        ·
          refine ⟨142169605638042552865437541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189559474184056737153916721 142169605638042552865437541)
          ·
            refine ⟨26656801057132978662269539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142169605638042552865437541 26656801057132978662269539)
            ·
              refine ⟨39985201585699467993404309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26656801057132978662269539 39985201585699467993404309)
              ·
                refine ⟨1874306324329662562190827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39985201585699467993404309 1874306324329662562190827)
                ·
                  refine ⟨2811459486494493843286241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874306324329662562190827 2811459486494493843286241)
                  ·
                    refine ⟨2108594614870870382464681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2811459486494493843286241 2108594614870870382464681)
                    ·
                      refine ⟨1581445961153152786848511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2108594614870870382464681 1581445961153152786848511)
                      ·
                        rfl

theorem cell23_3079855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 1, 2, 2].length) (baseStart_3079855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079855 prefixEnd_3079855 := by exact prefixLift 3079855
  have htrace : WordTrace (prefixWord ++ tailWord_3079855) baseStart_3079855 baseEnd_3079855 := by
    simpa [prefixWord, tailWord_3079855, baseEnd_3079855] using wordTrace_append hprefix tailTrace_3079855
  have hstable : (prefixWord ++ tailWord_3079855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079855).length < 2 ^ (prefixWord ++ tailWord_3079855).sum := by decide
  have hdescent : baseEnd_3079855 < baseStart_3079855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079868 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_3079868 : Nat := 118140960795 + 3079868 * 2 ^ 59
def prefixEnd_3079868 : Nat := 4983230072969 + 3 ^ 40 * 3079868 * 2
def baseEnd_3079868 : Nat := 1581452636401661235985951

theorem tailTrace_3079868 : CollatzResearch.WordTrace tailWord_3079868 prefixEnd_3079868 1581452636401661235985951 := by
  unfold tailWord_3079868
  simp only [CollatzResearch.WordTrace]
  refine ⟨56166007203085855211272129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74888009604114473615029505 56166007203085855211272129)
  ·
    refine ⟨42124505402314391408454097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56166007203085855211272129 42124505402314391408454097)
    ·
      refine ⟨31593379051735793556340573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42124505402314391408454097 31593379051735793556340573)
      ·
        refine ⟨11847517144400922583627715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31593379051735793556340573 11847517144400922583627715)
        ·
          refine ⟨17771275716601383875441573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11847517144400922583627715 17771275716601383875441573)
          ·
            refine ⟨3332114196862759476645295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17771275716601383875441573 3332114196862759476645295)
            ·
              refine ⟨4998171295294139214967943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3332114196862759476645295 4998171295294139214967943)
              ·
                refine ⟨7497256942941208822451915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4998171295294139214967943 7497256942941208822451915)
                ·
                  refine ⟨11245885414411813233677873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7497256942941208822451915 11245885414411813233677873)
                  ·
                    refine ⟨8434414060808859925258405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11245885414411813233677873 8434414060808859925258405)
                    ·
                      refine ⟨1581452636401661235985951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8434414060808859925258405 1581452636401661235985951)
                      ·
                        rfl

theorem cell23_3079868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_3079868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079868 prefixEnd_3079868 := by exact prefixLift 3079868
  have htrace : WordTrace (prefixWord ++ tailWord_3079868) baseStart_3079868 baseEnd_3079868 := by
    simpa [prefixWord, tailWord_3079868, baseEnd_3079868] using wordTrace_append hprefix tailTrace_3079868
  have hstable : (prefixWord ++ tailWord_3079868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079868).length < 2 ^ (prefixWord ++ tailWord_3079868).sum := by decide
  have hdescent : baseEnd_3079868 < baseStart_3079868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079904 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 4, 6]
def baseStart_3079904 : Nat := 118140960795 + 3079904 * 2 ^ 59
def prefixEnd_3079904 : Nat := 4983230072969 + 3 ^ 40 * 3079904 * 2
def baseEnd_3079904 : Nat := 527157040568407698378595

theorem tailTrace_3079904 : CollatzResearch.WordTrace tailWord_3079904 prefixEnd_3079904 527157040568407698378595 := by
  unfold tailWord_3079904
  simp only [CollatzResearch.WordTrace]
  refine ⟨56166663717020644285427383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74888884956027525713903177 56166663717020644285427383)
  ·
    refine ⟨84249995575530966428141075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56166663717020644285427383 84249995575530966428141075)
    ·
      refine ⟨126374993363296449642211613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84249995575530966428141075 126374993363296449642211613)
      ·
        refine ⟨47390622511236168615829355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126374993363296449642211613 47390622511236168615829355)
        ·
          refine ⟨71085933766854252923744033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47390622511236168615829355 71085933766854252923744033)
          ·
            refine ⟨53314450325140689692808025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71085933766854252923744033 53314450325140689692808025)
            ·
              refine ⟨39985837743855517269606019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53314450325140689692808025 39985837743855517269606019)
              ·
                refine ⟨59978756615783275904409029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39985837743855517269606019 59978756615783275904409029)
                ·
                  refine ⟨11246016865459364232076693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59978756615783275904409029 11246016865459364232076693)
                  ·
                    refine ⟨527157040568407698378595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11246016865459364232076693 527157040568407698378595)
                    ·
                      rfl

theorem cell23_3079904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_3079904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079904 prefixEnd_3079904 := by exact prefixLift 3079904
  have htrace : WordTrace (prefixWord ++ tailWord_3079904) baseStart_3079904 baseEnd_3079904 := by
    simpa [prefixWord, tailWord_3079904, baseEnd_3079904] using wordTrace_append hprefix tailTrace_3079904
  have hstable : (prefixWord ++ tailWord_3079904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079904).length < 2 ^ (prefixWord ++ tailWord_3079904).sum := by decide
  have hdescent : baseEnd_3079904 < baseStart_3079904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079928 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 6, 2, 2]
def baseStart_3079928 : Nat := 118140960795 + 3079928 * 2 ^ 59
def prefixEnd_3079928 : Nat := 4983230072969 + 3 ^ 40 * 3079928 * 2
def baseEnd_3079928 : Nat := 1581483445240931001235675

theorem tailTrace_3079928 : CollatzResearch.WordTrace tailWord_3079928 prefixEnd_3079928 1581483445240931001235675 := by
  unfold tailWord_3079928
  simp only [CollatzResearch.WordTrace]
  refine ⟨56167101392977170334864219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74889468523969560446485625 56167101392977170334864219)
  ·
    refine ⟨84250652089465755502296329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56167101392977170334864219 84250652089465755502296329)
    ·
      refine ⟨63187989067099316626722247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84250652089465755502296329 63187989067099316626722247)
      ·
        refine ⟨94781983600648974940083371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63187989067099316626722247 94781983600648974940083371)
        ·
          refine ⟨142172975400973462410125057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94781983600648974940083371 142172975400973462410125057)
          ·
            refine ⟨106629731550730096807593793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142172975400973462410125057 106629731550730096807593793)
            ·
              refine ⟨79972298663047572605695345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106629731550730096807593793 79972298663047572605695345)
              ·
                refine ⟨59979223997285679454271509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79972298663047572605695345 59979223997285679454271509)
                ·
                  refine ⟨2811526124872766224418977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59979223997285679454271509 2811526124872766224418977)
                  ·
                    refine ⟨2108644593654574668314233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2811526124872766224418977 2108644593654574668314233)
                    ·
                      refine ⟨1581483445240931001235675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2108644593654574668314233 1581483445240931001235675)
                      ·
                        rfl

theorem cell23_3079928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_3079928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079928 prefixEnd_3079928 := by exact prefixLift 3079928
  have htrace : WordTrace (prefixWord ++ tailWord_3079928) baseStart_3079928 baseEnd_3079928 := by
    simpa [prefixWord, tailWord_3079928, baseEnd_3079928] using wordTrace_append hprefix tailTrace_3079928
  have hstable : (prefixWord ++ tailWord_3079928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079928).length < 2 ^ (prefixWord ++ tailWord_3079928).sum := by decide
  have hdescent : baseEnd_3079928 < baseStart_3079928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079956 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3079956 : Nat := 118140960795 + 3079956 * 2 ^ 59
def prefixEnd_3079956 : Nat := 4983230072969 + 3 ^ 40 * 3079956 * 2
def baseEnd_3079956 : Nat := 1581497822699256891685547

theorem tailTrace_3079956 : CollatzResearch.WordTrace tailWord_3079956 prefixEnd_3079956 1581497822699256891685547 := by
  unfold tailWord_3079956
  simp only [CollatzResearch.WordTrace]
  refine ⟨56167612014926450725873861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74890149353235267634498481 56167612014926450725873861)
  ·
    refine ⟨10531427252798709511101349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56167612014926450725873861 10531427252798709511101349)
    ·
      refine ⟨1974642609899758033331503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10531427252798709511101349 1974642609899758033331503)
      ·
        refine ⟨2961963914849637049997255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974642609899758033331503 2961963914849637049997255)
        ·
          refine ⟨4442945872274455574995883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2961963914849637049997255 4442945872274455574995883)
          ·
            refine ⟨6664418808411683362493825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4442945872274455574995883 6664418808411683362493825)
            ·
              refine ⟨4998314106308762521870369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6664418808411683362493825 4998314106308762521870369)
              ·
                refine ⟨3748735579731571891402777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4998314106308762521870369 3748735579731571891402777)
                ·
                  refine ⟨2811551684798678918552083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3748735579731571891402777 2811551684798678918552083)
                  ·
                    refine ⟨4217327527198018377828125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2811551684798678918552083 4217327527198018377828125)
                    ·
                      refine ⟨1581497822699256891685547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4217327527198018377828125 1581497822699256891685547)
                      ·
                        rfl

theorem cell23_3079956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3079956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079956 prefixEnd_3079956 := by exact prefixLift 3079956
  have htrace : WordTrace (prefixWord ++ tailWord_3079956) baseStart_3079956 baseEnd_3079956 := by
    simpa [prefixWord, tailWord_3079956, baseEnd_3079956] using wordTrace_append hprefix tailTrace_3079956
  have hstable : (prefixWord ++ tailWord_3079956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079956).length < 2 ^ (prefixWord ++ tailWord_3079956).sum := by decide
  have hdescent : baseEnd_3079956 < baseStart_3079956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079962 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2]
def baseStart_3079962 : Nat := 118140960795 + 3079962 * 2 ^ 59
def prefixEnd_3079962 : Nat := 4983230072969 + 3 ^ 40 * 3079962 * 2
def baseEnd_3079962 : Nat := 1581500903583183868210519

theorem tailTrace_3079962 : CollatzResearch.WordTrace tailWord_3079962 prefixEnd_3079962 1581500903583183868210519 := by
  unfold tailWord_3079962
  simp only [CollatzResearch.WordTrace]
  refine ⟨28083860716957791119116535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74890295245220776317644093 28083860716957791119116535)
  ·
    refine ⟨42125791075436686678674803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28083860716957791119116535 42125791075436686678674803)
    ·
      refine ⟨63188686613155030018012205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42125791075436686678674803 63188686613155030018012205)
      ·
        refine ⟨23695757479933136256754577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63188686613155030018012205 23695757479933136256754577)
        ·
          refine ⟨17771818109949852192565933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23695757479933136256754577 17771818109949852192565933)
          ·
            refine ⟨6664431791231194572212225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17771818109949852192565933 6664431791231194572212225)
            ·
              refine ⟨4998323843423395929159169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6664431791231194572212225 4998323843423395929159169)
              ·
                refine ⟨3748742882567546946869377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4998323843423395929159169 3748742882567546946869377)
                ·
                  refine ⟨2811557161925660210152033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3748742882567546946869377 2811557161925660210152033)
                  ·
                    refine ⟨2108667871444245157614025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2811557161925660210152033 2108667871444245157614025)
                    ·
                      refine ⟨1581500903583183868210519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2108667871444245157614025 1581500903583183868210519)
                      ·
                        rfl

theorem cell23_3079962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_3079962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079962 prefixEnd_3079962 := by exact prefixLift 3079962
  have htrace : WordTrace (prefixWord ++ tailWord_3079962) baseStart_3079962 baseEnd_3079962 := by
    simpa [prefixWord, tailWord_3079962, baseEnd_3079962] using wordTrace_append hprefix tailTrace_3079962
  have hstable : (prefixWord ++ tailWord_3079962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079962).length < 2 ^ (prefixWord ++ tailWord_3079962).sum := by decide
  have hdescent : baseEnd_3079962 < baseStart_3079962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079968 : List Nat := [2, 1, 1, 5, 1, 1, 3, 4, 5]
def baseStart_3079968 : Nat := 118140960795 + 3079968 * 2 ^ 59
def prefixEnd_3079968 : Nat := 4983230072969 + 3 ^ 40 * 3079968 * 2
def baseEnd_3079968 : Nat := 175722664940790093859499

theorem tailTrace_3079968 : CollatzResearch.WordTrace tailWord_3079968 prefixEnd_3079968 175722664940790093859499 := by
  unfold tailWord_3079968
  simp only [CollatzResearch.WordTrace]
  refine ⟨56167830852904713750592279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74890441137206285000789705 56167830852904713750592279)
  ·
    refine ⟨84251746279357070625888419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56167830852904713750592279 84251746279357070625888419)
    ·
      refine ⟨126377619419035605938832629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84251746279357070625888419 126377619419035605938832629)
      ·
        refine ⟨11847901820534588056765559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126377619419035605938832629 11847901820534588056765559)
        ·
          refine ⟨17771852730801882085148339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11847901820534588056765559 17771852730801882085148339)
          ·
            refine ⟨26657779096202823127722509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17771852730801882085148339 26657779096202823127722509)
            ·
              refine ⟨9996667161076058672895941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26657779096202823127722509 9996667161076058672895941)
              ·
                refine ⟨1874375092701761001167989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9996667161076058672895941 1874375092701761001167989)
                ·
                  refine ⟨175722664940790093859499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1874375092701761001167989 175722664940790093859499)
                  ·
                    rfl

theorem cell23_3079968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 5].length) (baseStart_3079968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079968 prefixEnd_3079968 := by exact prefixLift 3079968
  have htrace : WordTrace (prefixWord ++ tailWord_3079968) baseStart_3079968 baseEnd_3079968 := by
    simpa [prefixWord, tailWord_3079968, baseEnd_3079968] using wordTrace_append hprefix tailTrace_3079968
  have hstable : (prefixWord ++ tailWord_3079968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079968).length < 2 ^ (prefixWord ++ tailWord_3079968).sum := by decide
  have hdescent : baseEnd_3079968 < baseStart_3079968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3079998 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_3079998 : Nat := 118140960795 + 3079998 * 2 ^ 59
def prefixEnd_3079998 : Nat := 4983230072969 + 3 ^ 40 * 3079998 * 2
def baseEnd_3079998 : Nat := 527173129628915242453451

theorem tailTrace_3079998 : CollatzResearch.WordTrace tailWord_3079998 prefixEnd_3079998 527173129628915242453451 := by
  unfold tailWord_3079998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14042094486962592828097081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74891170597133828416517765 14042094486962592828097081)
  ·
    refine ⟨10531570865221944621072811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14042094486962592828097081 10531570865221944621072811)
    ·
      refine ⟨15797356297832916931609217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10531570865221944621072811 15797356297832916931609217)
      ·
        refine ⟨11848017223374687698706913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15797356297832916931609217 11848017223374687698706913)
        ·
          refine ⟨8886012917531015774030185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11848017223374687698706913 8886012917531015774030185)
          ·
            refine ⟨6664509688148261830522639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8886012917531015774030185 6664509688148261830522639)
            ·
              refine ⟨9996764532222392745783959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6664509688148261830522639 9996764532222392745783959)
              ·
                refine ⟨14995146798333589118675939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9996764532222392745783959 14995146798333589118675939)
                ·
                  refine ⟨22492720197500383678013909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14995146798333589118675939 22492720197500383678013909)
                  ·
                    refine ⟨527173129628915242453451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22492720197500383678013909 527173129628915242453451)
                    ·
                      rfl

theorem cell23_3079998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_3079998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3079998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3079998 prefixEnd_3079998 := by exact prefixLift 3079998
  have htrace : WordTrace (prefixWord ++ tailWord_3079998) baseStart_3079998 baseEnd_3079998 := by
    simpa [prefixWord, tailWord_3079998, baseEnd_3079998] using wordTrace_append hprefix tailTrace_3079998
  have hstable : (prefixWord ++ tailWord_3079998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3079998).length < 2 ^ (prefixWord ++ tailWord_3079998).sum := by decide
  have hdescent : baseEnd_3079998 < baseStart_3079998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3079998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080041 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 6]
def baseStart_3080041 : Nat := 118140960795 + 3080041 * 2 ^ 59
def prefixEnd_3080041 : Nat := 4983230072969 + 3 ^ 40 * 3080041 * 2
def baseEnd_3080041 : Nat := 175726829839432117680295

theorem tailTrace_3080041 : CollatzResearch.WordTrace tailWord_3080041 prefixEnd_3080041 175726829839432117680295 := by
  unfold tailWord_3080041
  simp only [CollatzResearch.WordTrace]
  refine ⟨112338324234544960968591977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74892216156363307312394651 112338324234544960968591977)
  ·
    refine ⟨84253743175908720726443983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112338324234544960968591977 84253743175908720726443983)
    ·
      refine ⟨126380614763863081089665975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84253743175908720726443983 126380614763863081089665975)
      ·
        refine ⟨189570922145794621634498963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126380614763863081089665975 189570922145794621634498963)
        ·
          refine ⟨284356383218691932451748445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189570922145794621634498963 284356383218691932451748445)
          ·
            refine ⟨106633643707009474669405667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284356383218691932451748445 106633643707009474669405667)
            ·
              refine ⟨159950465560514212004108501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106633643707009474669405667 159950465560514212004108501)
              ·
                refine ⟨3748839036574551843846293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 159950465560514212004108501 3748839036574551843846293)
                ·
                  refine ⟨175726829839432117680295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3748839036574551843846293 175726829839432117680295)
                  ·
                    rfl

theorem cell23_3080041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 6].length) (baseStart_3080041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080041 prefixEnd_3080041 := by exact prefixLift 3080041
  have htrace : WordTrace (prefixWord ++ tailWord_3080041) baseStart_3080041 baseEnd_3080041 := by
    simpa [prefixWord, tailWord_3080041, baseEnd_3080041] using wordTrace_append hprefix tailTrace_3080041
  have hstable : (prefixWord ++ tailWord_3080041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080041).length < 2 ^ (prefixWord ++ tailWord_3080041).sum := by decide
  have hdescent : baseEnd_3080041 < baseStart_3080041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080051 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 3]
def baseStart_3080051 : Nat := 118140960795 + 3080051 * 2 ^ 59
def prefixEnd_3080051 : Nat := 4983230072969 + 3 ^ 40 * 3080051 * 2
def baseEnd_3080051 : Nat := 1581546603361434019997609

theorem tailTrace_3080051 : CollatzResearch.WordTrace tailWord_3080051 prefixEnd_3080051 1581546603361434019997609 := by
  unfold tailWord_3080051
  simp only [CollatzResearch.WordTrace]
  refine ⟨112338688964508732676456007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74892459309672488450970671 112338688964508732676456007)
  ·
    refine ⟨168508033446763099014684011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112338688964508732676456007 168508033446763099014684011)
    ·
      refine ⟨252762050170144648522026017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168508033446763099014684011 252762050170144648522026017)
      ·
        refine ⟨189571537627608486391519513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252762050170144648522026017 189571537627608486391519513)
        ·
          refine ⟨142178653220706364793639635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189571537627608486391519513 142178653220706364793639635)
          ·
            refine ⟨213267979831059547190459453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142178653220706364793639635 213267979831059547190459453)
            ·
              refine ⟨79975492436647330196422295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213267979831059547190459453 79975492436647330196422295)
              ·
                refine ⟨119963238654970995294633443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79975492436647330196422295 119963238654970995294633443)
                ·
                  refine ⟨179944857982456492941950165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119963238654970995294633443 179944857982456492941950165)
                  ·
                    refine ⟨4217457608963824053326957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 179944857982456492941950165 4217457608963824053326957)
                    ·
                      refine ⟨1581546603361434019997609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4217457608963824053326957 1581546603361434019997609)
                      ·
                        rfl

theorem cell23_3080051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 3].length) (baseStart_3080051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080051 prefixEnd_3080051 := by exact prefixLift 3080051
  have htrace : WordTrace (prefixWord ++ tailWord_3080051) baseStart_3080051 baseEnd_3080051 := by
    simpa [prefixWord, tailWord_3080051, baseEnd_3080051] using wordTrace_append hprefix tailTrace_3080051
  have hstable : (prefixWord ++ tailWord_3080051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080051).length < 2 ^ (prefixWord ++ tailWord_3080051).sum := by decide
  have hdescent : baseEnd_3080051 < baseStart_3080051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080092 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 6]
def baseStart_3080092 : Nat := 118140960795 + 3080092 * 2 ^ 59
def prefixEnd_3080092 : Nat := 4983230072969 + 3 ^ 40 * 3080092 * 2
def baseEnd_3080092 : Nat := 175729739563140928842769

theorem tailTrace_3080092 : CollatzResearch.WordTrace tailWord_3080092 prefixEnd_3080092 175729739563140928842769 := by
  unfold tailWord_3080092
  simp only [CollatzResearch.WordTrace]
  refine ⟨56170092178680098339349265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74893456238240131119132353 56170092178680098339349265)
  ·
    refine ⟨42127569134010073754511949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56170092178680098339349265 42127569134010073754511949)
    ·
      refine ⟨15797838425253777657941981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42127569134010073754511949 15797838425253777657941981)
      ·
        refine ⟨5924189409470166621728243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15797838425253777657941981 5924189409470166621728243)
        ·
          refine ⟨8886284114205249932592365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5924189409470166621728243 8886284114205249932592365)
          ·
            refine ⟨3332356542826968724722137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8886284114205249932592365 3332356542826968724722137)
            ·
              refine ⟨2499267407120226543541603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3332356542826968724722137 2499267407120226543541603)
              ·
                refine ⟨3748901110680339815312405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499267407120226543541603 3748901110680339815312405)
                ·
                  refine ⟨175729739563140928842769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3748901110680339815312405 175729739563140928842769)
                  ·
                    rfl

theorem cell23_3080092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_3080092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080092 prefixEnd_3080092 := by exact prefixLift 3080092
  have htrace : WordTrace (prefixWord ++ tailWord_3080092) baseStart_3080092 baseEnd_3080092 := by
    simpa [prefixWord, tailWord_3080092, baseEnd_3080092] using wordTrace_append hprefix tailTrace_3080092
  have hstable : (prefixWord ++ tailWord_3080092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080092).length < 2 ^ (prefixWord ++ tailWord_3080092).sum := by decide
  have hdescent : baseEnd_3080092 < baseStart_3080092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080101 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_3080101 : Nat := 118140960795 + 3080101 * 2 ^ 59
def prefixEnd_3080101 : Nat := 4983230072969 + 3 ^ 40 * 3080101 * 2
def baseEnd_3080101 : Nat := 527190759131386274790793

theorem tailTrace_3080101 : CollatzResearch.WordTrace tailWord_3080101 prefixEnd_3080101 527190759131386274790793 := by
  unfold tailWord_3080101
  simp only [CollatzResearch.WordTrace]
  refine ⟨112340512614327591215776157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74893675076218394143850771 112340512614327591215776157)
  ·
    refine ⟨42127692230372846705916059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112340512614327591215776157 42127692230372846705916059)
    ·
      refine ⟨63191538345559270058874089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42127692230372846705916059 63191538345559270058874089)
      ·
        refine ⟨47393653759169452544155567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63191538345559270058874089 47393653759169452544155567)
        ·
          refine ⟨71090480638754178816233351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47393653759169452544155567 71090480638754178816233351)
          ·
            refine ⟨106635720958131268224350027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71090480638754178816233351 106635720958131268224350027)
            ·
              refine ⟨159953581437196902336525041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106635720958131268224350027 159953581437196902336525041)
              ·
                refine ⟨119965186077897676752393781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159953581437196902336525041 119965186077897676752393781)
                ·
                  refine ⟨11246736194802907195536917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119965186077897676752393781 11246736194802907195536917)
                  ·
                    refine ⟨527190759131386274790793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11246736194802907195536917 527190759131386274790793)
                    ·
                      rfl

theorem cell23_3080101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_3080101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080101 prefixEnd_3080101 := by exact prefixLift 3080101
  have htrace : WordTrace (prefixWord ++ tailWord_3080101) baseStart_3080101 baseEnd_3080101 := by
    simpa [prefixWord, tailWord_3080101, baseEnd_3080101] using wordTrace_append hprefix tailTrace_3080101
  have hstable : (prefixWord ++ tailWord_3080101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080101).length < 2 ^ (prefixWord ++ tailWord_3080101).sum := by decide
  have hdescent : baseEnd_3080101 < baseStart_3080101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080136 : List Nat := [2, 1, 3, 1, 4, 3, 2, 2, 1, 1, 3]
def baseStart_3080136 : Nat := 118140960795 + 3080136 * 2 ^ 59
def prefixEnd_3080136 : Nat := 4983230072969 + 3 ^ 40 * 3080136 * 2
def baseEnd_3080136 : Nat := 1581590249217066187434719

theorem tailTrace_3080136 : CollatzResearch.WordTrace tailWord_3080136 prefixEnd_3080136 1581590249217066187434719 := by
  unfold tailWord_3080136
  simp only [CollatzResearch.WordTrace]
  refine ⟨56170894584600396096650131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74894526112800528128866841 56170894584600396096650131)
  ·
    refine ⟨84256341876900594144975197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56170894584600396096650131 84256341876900594144975197)
    ·
      refine ⟨31596128203837722804365699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84256341876900594144975197 31596128203837722804365699)
      ·
        refine ⟨47394192305756584206548549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31596128203837722804365699 47394192305756584206548549)
        ·
          refine ⟨8886411057329359538727853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47394192305756584206548549 8886411057329359538727853)
          ·
            refine ⟨3332404146498509827022945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8886411057329359538727853 3332404146498509827022945)
            ·
              refine ⟨2499303109873882370267209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3332404146498509827022945 2499303109873882370267209)
              ·
                refine ⟨1874477332405411777700407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499303109873882370267209 1874477332405411777700407)
                ·
                  refine ⟨2811715998608117666550611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874477332405411777700407 2811715998608117666550611)
                  ·
                    refine ⟨4217573997912176499825917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2811715998608117666550611 4217573997912176499825917)
                    ·
                      refine ⟨1581590249217066187434719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4217573997912176499825917 1581590249217066187434719)
                      ·
                        rfl

theorem cell23_3080136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_3080136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080136 prefixEnd_3080136 := by exact prefixLift 3080136
  have htrace : WordTrace (prefixWord ++ tailWord_3080136) baseStart_3080136 baseEnd_3080136 := by
    simpa [prefixWord, tailWord_3080136, baseEnd_3080136] using wordTrace_append hprefix tailTrace_3080136
  have hstable : (prefixWord ++ tailWord_3080136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080136).length < 2 ^ (prefixWord ++ tailWord_3080136).sum := by decide
  have hdescent : baseEnd_3080136 < baseStart_3080136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080142 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2]
def baseStart_3080142 : Nat := 118140960795 + 3080142 * 2 ^ 59
def prefixEnd_3080142 : Nat := 4983230072969 + 3 ^ 40 * 3080142 * 2
def baseEnd_3080142 : Nat := 1581593330100993163959691

theorem tailTrace_3080142 : CollatzResearch.WordTrace tailWord_3080142 prefixEnd_3080142 1581593330100993163959691 := by
  unfold tailWord_3080142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14042751000897381902252335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74894672004786036812012453 14042751000897381902252335)
  ·
    refine ⟨21064126501346072853378503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14042751000897381902252335 21064126501346072853378503)
    ·
      refine ⟨31596189752019109280067755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21064126501346072853378503 31596189752019109280067755)
      ·
        refine ⟨47394284628028663920101633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31596189752019109280067755 47394284628028663920101633)
        ·
          refine ⟨35545713471021497940076225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47394284628028663920101633 35545713471021497940076225)
          ·
            refine ⟨26659285103266123455057169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35545713471021497940076225 26659285103266123455057169)
            ·
              refine ⟨19994463827449592591292877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26659285103266123455057169 19994463827449592591292877)
              ·
                refine ⟨7497923935293597221734829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19994463827449592591292877 7497923935293597221734829)
                ·
                  refine ⟨2811721475735098958150561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7497923935293597221734829 2811721475735098958150561)
                  ·
                    refine ⟨2108791106801324218612921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2811721475735098958150561 2108791106801324218612921)
                    ·
                      refine ⟨1581593330100993163959691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2108791106801324218612921 1581593330100993163959691)
                      ·
                        rfl

theorem cell23_3080142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_3080142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080142 prefixEnd_3080142 := by exact prefixLift 3080142
  have htrace : WordTrace (prefixWord ++ tailWord_3080142) baseStart_3080142 baseEnd_3080142 := by
    simpa [prefixWord, tailWord_3080142, baseEnd_3080142] using wordTrace_append hprefix tailTrace_3080142
  have hstable : (prefixWord ++ tailWord_3080142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080142).length < 2 ^ (prefixWord ++ tailWord_3080142).sum := by decide
  have hdescent : baseEnd_3080142 < baseStart_3080142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080175 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 4, 1, 3]
def baseStart_3080175 : Nat := 118140960795 + 3080175 * 2 ^ 59
def prefixEnd_3080175 : Nat := 4983230072969 + 3 ^ 40 * 3080175 * 2
def baseEnd_3080175 : Nat := 1581610274962591534847039

theorem tailTrace_3080175 : CollatzResearch.WordTrace tailWord_3080175 prefixEnd_3080175 1581610274962591534847039 := by
  unfold tailWord_3080175
  simp only [CollatzResearch.WordTrace]
  refine ⟨112343211616059501853969979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74895474410706334569313319 112343211616059501853969979)
  ·
    refine ⟨168514817424089252780954969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112343211616059501853969979 168514817424089252780954969)
    ·
      refine ⟨126386113068066939585716227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168514817424089252780954969 126386113068066939585716227)
      ·
        refine ⟨189579169602100409378574341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126386113068066939585716227 189579169602100409378574341)
        ·
          refine ⟨35546094300393826758482689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189579169602100409378574341 35546094300393826758482689)
          ·
            refine ⟨26659570725295370068862017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35546094300393826758482689 26659570725295370068862017)
            ·
              refine ⟨19994678043971527551646513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26659570725295370068862017 19994678043971527551646513)
              ·
                refine ⟨14996008532978645663734885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19994678043971527551646513 14996008532978645663734885)
                ·
                  refine ⟨2811751599933496061950291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14996008532978645663734885 2811751599933496061950291)
                  ·
                    refine ⟨4217627399900244092925437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2811751599933496061950291 4217627399900244092925437)
                    ·
                      refine ⟨1581610274962591534847039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4217627399900244092925437 1581610274962591534847039)
                      ·
                        rfl

theorem cell23_3080175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 1, 3].length) (baseStart_3080175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080175 prefixEnd_3080175 := by exact prefixLift 3080175
  have htrace : WordTrace (prefixWord ++ tailWord_3080175) baseStart_3080175 baseEnd_3080175 := by
    simpa [prefixWord, tailWord_3080175, baseEnd_3080175] using wordTrace_append hprefix tailTrace_3080175
  have hstable : (prefixWord ++ tailWord_3080175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080175).length < 2 ^ (prefixWord ++ tailWord_3080175).sum := by decide
  have hdescent : baseEnd_3080175 < baseStart_3080175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080255 : List Nat := [1, 1, 2, 2, 3, 1, 2, 6, 5]
def baseStart_3080255 : Nat := 118140960795 + 3080255 * 2 ^ 59
def prefixEnd_3080255 : Nat := 4983230072969 + 3 ^ 40 * 3080255 * 2
def baseEnd_3080255 : Nat := 175739039268327913538519

theorem tailTrace_3080255 : CollatzResearch.WordTrace tailWord_3080255 prefixEnd_3080255 175739039268327913538519 := by
  unfold tailWord_3080255
  simp only [CollatzResearch.WordTrace]
  refine ⟨112346129455769675516882219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74897419637179783677921479 112346129455769675516882219)
  ·
    refine ⟨168519194183654513275323329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112346129455769675516882219 168519194183654513275323329)
    ·
      refine ⟨126389395637740884956492497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168519194183654513275323329 126389395637740884956492497)
      ·
        refine ⟨94792046728305663717369373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126389395637740884956492497 94792046728305663717369373)
        ·
          refine ⟨35547017523114623894013515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94792046728305663717369373 35547017523114623894013515)
          ·
            refine ⟨53320526284671935841020273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35547017523114623894013515 53320526284671935841020273)
            ·
              refine ⟨39990394713503951880765205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53320526284671935841020273 39990394713503951880765205)
              ·
                refine ⟨1874549752195497744410869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39990394713503951880765205 1874549752195497744410869)
                ·
                  refine ⟨175739039268327913538519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1874549752195497744410869 175739039268327913538519)
                  ·
                    rfl

theorem cell23_3080255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 5].length) (baseStart_3080255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080255 prefixEnd_3080255 := by exact prefixLift 3080255
  have htrace : WordTrace (prefixWord ++ tailWord_3080255) baseStart_3080255 baseEnd_3080255 := by
    simpa [prefixWord, tailWord_3080255, baseEnd_3080255] using wordTrace_append hprefix tailTrace_3080255
  have hstable : (prefixWord ++ tailWord_3080255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080255).length < 2 ^ (prefixWord ++ tailWord_3080255).sum := by decide
  have hdescent : baseEnd_3080255 < baseStart_3080255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080262 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3080262 : Nat := 118140960795 + 3080262 * 2 ^ 59
def prefixEnd_3080262 : Nat := 4983230072969 + 3 ^ 40 * 3080262 * 2
def baseEnd_3080262 : Nat := 1581654947779532694459139

theorem tailTrace_3080262 : CollatzResearch.WordTrace tailWord_3080262 prefixEnd_3080262 1581654947779532694459139 := by
  unfold tailWord_3080262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3510824523960759866012095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74897589844496210474924693 3510824523960759866012095)
  ·
    refine ⟨5266236785941139799018143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3510824523960759866012095 5266236785941139799018143)
    ·
      refine ⟨7899355178911709698527215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5266236785941139799018143 7899355178911709698527215)
      ·
        refine ⟨11849032768367564547790823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7899355178911709698527215 11849032768367564547790823)
        ·
          refine ⟨17773549152551346821686235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11849032768367564547790823 17773549152551346821686235)
          ·
            refine ⟨26660323728827020232529353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17773549152551346821686235 26660323728827020232529353)
            ·
              refine ⟨19995242796620265174397015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26660323728827020232529353 19995242796620265174397015)
              ·
                refine ⟨29992864194930397761595523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19995242796620265174397015 29992864194930397761595523)
                ·
                  refine ⟨44989296292395596642393285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29992864194930397761595523 44989296292395596642393285)
                  ·
                    refine ⟨8435493054824174370448741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44989296292395596642393285 8435493054824174370448741)
                    ·
                      refine ⟨1581654947779532694459139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8435493054824174370448741 1581654947779532694459139)
                      ·
                        rfl

theorem cell23_3080262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3080262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080262 prefixEnd_3080262 := by exact prefixLift 3080262
  have htrace : WordTrace (prefixWord ++ tailWord_3080262) baseStart_3080262 baseEnd_3080262 := by
    simpa [prefixWord, tailWord_3080262, baseEnd_3080262] using wordTrace_append hprefix tailTrace_3080262
  have hstable : (prefixWord ++ tailWord_3080262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080262).length < 2 ^ (prefixWord ++ tailWord_3080262).sum := by decide
  have hdescent : baseEnd_3080262 < baseStart_3080262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080268 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_3080268 : Nat := 118140960795 + 3080268 * 2 ^ 59
def prefixEnd_3080268 : Nat := 4983230072969 + 3 ^ 40 * 3080268 * 2
def baseEnd_3080268 : Nat := 527219342887819890328037

theorem tailTrace_3080268 : CollatzResearch.WordTrace tailWord_3080268 prefixEnd_3080268 527219342887819890328037 := by
  unfold tailWord_3080268
  simp only [CollatzResearch.WordTrace]
  refine ⟨56173301802361289368552729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74897735736481719158070305 56173301802361289368552729)
  ·
    refine ⟨42129976351770967026414547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56173301802361289368552729 42129976351770967026414547)
    ·
      refine ⟨63194964527656450539621821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42129976351770967026414547 63194964527656450539621821)
      ·
        refine ⟨23698111697871168952358183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63194964527656450539621821 23698111697871168952358183)
        ·
          refine ⟨35547167546806753428537275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23698111697871168952358183 35547167546806753428537275)
          ·
            refine ⟨53320751320210130142805913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35547167546806753428537275 53320751320210130142805913)
            ·
              refine ⟨39990563490157597607104435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53320751320210130142805913 39990563490157597607104435)
              ·
                refine ⟨59985845235236396410656653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39990563490157597607104435 59985845235236396410656653)
                ·
                  refine ⟨22494691963213648653996245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59985845235236396410656653 22494691963213648653996245)
                  ·
                    refine ⟨527219342887819890328037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22494691963213648653996245 527219342887819890328037)
                    ·
                      rfl

theorem cell23_3080268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_3080268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080268 prefixEnd_3080268 := by exact prefixLift 3080268
  have htrace : WordTrace (prefixWord ++ tailWord_3080268) baseStart_3080268 baseEnd_3080268 := by
    simpa [prefixWord, tailWord_3080268, baseEnd_3080268] using wordTrace_append hprefix tailTrace_3080268
  have hstable : (prefixWord ++ tailWord_3080268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080268).length < 2 ^ (prefixWord ++ tailWord_3080268).sum := by decide
  have hdescent : baseEnd_3080268 < baseStart_3080268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080305 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_3080305 : Nat := 118140960795 + 3080305 * 2 ^ 59
def prefixEnd_3080305 : Nat := 4983230072969 + 3 ^ 40 * 3080305 * 2
def baseEnd_3080305 : Nat := 1581677027447676026221441

theorem tailTrace_3080305 : CollatzResearch.WordTrace tailWord_3080305 prefixEnd_3080305 1581677027447676026221441 := by
  unfold tailWord_3080305
  simp only [CollatzResearch.WordTrace]
  refine ⟨112347953105588534056202369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74898635403725689370801579 112347953105588534056202369)
  ·
    refine ⟨84260964829191400542151777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112347953105588534056202369 84260964829191400542151777)
    ·
      refine ⟨63195723621893550406613833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84260964829191400542151777 63195723621893550406613833)
      ·
        refine ⟨47396792716420162804960375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63195723621893550406613833 47396792716420162804960375)
        ·
          refine ⟨71095189074630244207440563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47396792716420162804960375 71095189074630244207440563)
          ·
            refine ⟨106642783611945366311160845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71095189074630244207440563 106642783611945366311160845)
            ·
              refine ⟨39991043854479512366685317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106642783611945366311160845 39991043854479512366685317)
              ·
                refine ⟨7498320722714908568753497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39991043854479512366685317 7498320722714908568753497)
                ·
                  refine ⟨5623740542036181426565123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7498320722714908568753497 5623740542036181426565123)
                  ·
                    refine ⟨8435610813054272139847685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5623740542036181426565123 8435610813054272139847685)
                    ·
                      refine ⟨1581677027447676026221441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8435610813054272139847685 1581677027447676026221441)
                      ·
                        rfl

theorem cell23_3080305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_3080305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080305 prefixEnd_3080305 := by exact prefixLift 3080305
  have htrace : WordTrace (prefixWord ++ tailWord_3080305) baseStart_3080305 baseEnd_3080305 := by
    simpa [prefixWord, tailWord_3080305, baseEnd_3080305] using wordTrace_append hprefix tailTrace_3080305
  have hstable : (prefixWord ++ tailWord_3080305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080305).length < 2 ^ (prefixWord ++ tailWord_3080305).sum := by decide
  have hdescent : baseEnd_3080305 < baseStart_3080305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080349 : List Nat := [1, 4, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_3080349 : Nat := 118140960795 + 3080349 * 2 ^ 59
def prefixEnd_3080349 : Nat := 4983230072969 + 3 ^ 40 * 3080349 * 2
def baseEnd_3080349 : Nat := 527233206865491284690413

theorem tailTrace_3080349 : CollatzResearch.WordTrace tailWord_3080349 prefixEnd_3080349 527233206865491284690413 := by
  unfold tailWord_3080349
  simp only [CollatzResearch.WordTrace]
  refine ⟨112349557917429129570804101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74899705278286086380536067 112349557917429129570804101)
  ·
    refine ⟨21065542109517961794525769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112349557917429129570804101 21065542109517961794525769)
    ·
      refine ⟨15799156582138471345894327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21065542109517961794525769 15799156582138471345894327)
      ·
        refine ⟨23698734873207707018841491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15799156582138471345894327 23698734873207707018841491)
        ·
          refine ⟨35548102309811560528262237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23698734873207707018841491 35548102309811560528262237)
          ·
            refine ⟨13330538366179335198098339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35548102309811560528262237 13330538366179335198098339)
            ·
              refine ⟨19995807549269002797147509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13330538366179335198098339 19995807549269002797147509)
              ·
                refine ⟨1874606957743969012232579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19995807549269002797147509 1874606957743969012232579)
                ·
                  refine ⟨2811910436615953518348869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874606957743969012232579 2811910436615953518348869)
                  ·
                    refine ⟨527233206865491284690413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2811910436615953518348869 527233206865491284690413)
                    ·
                      rfl

theorem cell23_3080349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_3080349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080349 prefixEnd_3080349 := by exact prefixLift 3080349
  have htrace : WordTrace (prefixWord ++ tailWord_3080349) baseStart_3080349 baseEnd_3080349 := by
    simpa [prefixWord, tailWord_3080349, baseEnd_3080349] using wordTrace_append hprefix tailTrace_3080349
  have hstable : (prefixWord ++ tailWord_3080349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080349).length < 2 ^ (prefixWord ++ tailWord_3080349).sum := by decide
  have hdescent : baseEnd_3080349 < baseStart_3080349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080425 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_3080425 : Nat := 118140960795 + 3080425 * 2 ^ 59
def prefixEnd_3080425 : Nat := 4983230072969 + 3 ^ 40 * 3080425 * 2
def baseEnd_3080425 : Nat := 1581738645126215556720889

theorem tailTrace_3080425 : CollatzResearch.WordTrace tailWord_3080425 prefixEnd_3080425 1581738645126215556720889 := by
  unfold tailWord_3080425
  simp only [CollatzResearch.WordTrace]
  refine ⟨112352329865153794550570729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74901553243435863033713819 112352329865153794550570729)
  ·
    refine ⟨84264247398865345912928047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112352329865153794550570729 84264247398865345912928047)
    ·
      refine ⟨126396371098298018869392071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84264247398865345912928047 126396371098298018869392071)
      ·
        refine ⟨189594556647447028304088107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126396371098298018869392071 189594556647447028304088107)
        ·
          refine ⟨284391834971170542456132161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189594556647447028304088107 284391834971170542456132161)
          ·
            refine ⟨213293876228377906842099121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284391834971170542456132161 213293876228377906842099121)
            ·
              refine ⟨159970407171283430131574341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213293876228377906842099121 159970407171283430131574341)
              ·
                refine ⟨29994451344615643149670189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159970407171283430131574341 29994451344615643149670189)
                ·
                  refine ⟨11247919254230866181126321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29994451344615643149670189 11247919254230866181126321)
                  ·
                    refine ⟨8435939440673149635844741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11247919254230866181126321 8435939440673149635844741)
                    ·
                      refine ⟨1581738645126215556720889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8435939440673149635844741 1581738645126215556720889)
                      ·
                        rfl

theorem cell23_3080425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_3080425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080425 prefixEnd_3080425 := by exact prefixLift 3080425
  have htrace : WordTrace (prefixWord ++ tailWord_3080425) baseStart_3080425 baseEnd_3080425 := by
    simpa [prefixWord, tailWord_3080425, baseEnd_3080425] using wordTrace_append hprefix tailTrace_3080425
  have hstable : (prefixWord ++ tailWord_3080425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080425).length < 2 ^ (prefixWord ++ tailWord_3080425).sum := by decide
  have hdescent : baseEnd_3080425 < baseStart_3080425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080435 : List Nat := [1, 1, 1, 2, 2, 4, 4, 8]
def baseStart_3080435 : Nat := 118140960795 + 3080435 * 2 ^ 59
def prefixEnd_3080435 : Nat := 4983230072969 + 3 ^ 40 * 3080435 * 2
def baseEnd_3080435 : Nat := 58583102960472611762809

theorem tailTrace_3080435 : CollatzResearch.WordTrace tailWord_3080435 prefixEnd_3080435 58583102960472611762809 := by
  unfold tailWord_3080435
  simp only [CollatzResearch.WordTrace]
  refine ⟨112352694595117566258434759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74901796396745044172289839 112352694595117566258434759)
  ·
    refine ⟨168529041892676349387652139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112352694595117566258434759 168529041892676349387652139)
    ·
      refine ⟨252793562839014524081478209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168529041892676349387652139 252793562839014524081478209)
      ·
        refine ⟨189595172129260893061108657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252793562839014524081478209 189595172129260893061108657)
        ·
          refine ⟨142196379096945669795831493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189595172129260893061108657 142196379096945669795831493)
          ·
            refine ⟨26661821080677313086718405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142196379096945669795831493 26661821080677313086718405)
            ·
              refine ⟨4999091452626996203759701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26661821080677313086718405 4999091452626996203759701)
              ·
                refine ⟨58583102960472611762809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4999091452626996203759701 58583102960472611762809)
                ·
                  rfl

theorem cell23_3080435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 8].length) (baseStart_3080435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080435 prefixEnd_3080435 := by exact prefixLift 3080435
  have htrace : WordTrace (prefixWord ++ tailWord_3080435) baseStart_3080435 baseEnd_3080435 := by
    simpa [prefixWord, tailWord_3080435, baseEnd_3080435] using wordTrace_append hprefix tailTrace_3080435
  have hstable : (prefixWord ++ tailWord_3080435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080435).length < 2 ^ (prefixWord ++ tailWord_3080435).sum := by decide
  have hdescent : baseEnd_3080435 < baseStart_3080435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080446 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_3080446 : Nat := 118140960795 + 3080446 * 2 ^ 59
def prefixEnd_3080446 : Nat := 4983230072969 + 3 ^ 40 * 3080446 * 2
def baseEnd_3080446 : Nat := 1581749428219959974558293

theorem tailTrace_3080446 : CollatzResearch.WordTrace tailWord_3080446 prefixEnd_3080446 1581749428219959974558293 := by
  unfold tailWord_3080446
  simp only [CollatzResearch.WordTrace]
  refine ⟨14044136974759714392135649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74902063865385143424723461 14044136974759714392135649)
  ·
    refine ⟨10533102731069785794101737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14044136974759714392135649 10533102731069785794101737)
    ·
      refine ⟨7899827048302339345576303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10533102731069785794101737 7899827048302339345576303)
      ·
        refine ⟨11849740572453509018364455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7899827048302339345576303 11849740572453509018364455)
        ·
          refine ⟨17774610858680263527546683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11849740572453509018364455 17774610858680263527546683)
          ·
            refine ⟨26661916288020395291320025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17774610858680263527546683 26661916288020395291320025)
            ·
              refine ⟨19996437216015296468490019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26661916288020395291320025 19996437216015296468490019)
              ·
                refine ⟨29994655824022944702735029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19996437216015296468490019 29994655824022944702735029)
                ·
                  refine ⟨2811998983502151065881409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29994655824022944702735029 2811998983502151065881409)
                  ·
                    refine ⟨2108999237626613299411057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2811998983502151065881409 2108999237626613299411057)
                    ·
                      refine ⟨1581749428219959974558293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2108999237626613299411057 1581749428219959974558293)
                      ·
                        rfl

theorem cell23_3080446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_3080446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080446 prefixEnd_3080446 := by exact prefixLift 3080446
  have htrace : WordTrace (prefixWord ++ tailWord_3080446) baseStart_3080446 baseEnd_3080446 := by
    simpa [prefixWord, tailWord_3080446, baseEnd_3080446] using wordTrace_append hprefix tailTrace_3080446
  have hstable : (prefixWord ++ tailWord_3080446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080446).length < 2 ^ (prefixWord ++ tailWord_3080446).sum := by decide
  have hdescent : baseEnd_3080446 < baseStart_3080446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080475 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 5]
def baseStart_3080475 : Nat := 118140960795 + 3080475 * 2 ^ 59
def prefixEnd_3080475 : Nat := 4983230072969 + 3 ^ 40 * 3080475 * 2
def baseEnd_3080475 : Nat := 1581764319158940361095659

theorem tailTrace_3080475 : CollatzResearch.WordTrace tailWord_3080475 prefixEnd_3080475 1581764319158940361095659 := by
  unfold tailWord_3080475
  simp only [CollatzResearch.WordTrace]
  refine ⟨112354153514972653089890879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74902769009981768726593919 112354153514972653089890879)
  ·
    refine ⟨168531230272458979634836319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112354153514972653089890879 168531230272458979634836319)
    ·
      refine ⟨252796845408688469452254479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168531230272458979634836319 252796845408688469452254479)
      ·
        refine ⟨379195268113032704178381719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252796845408688469452254479 379195268113032704178381719)
        ·
          refine ⟨568792902169549056267572579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379195268113032704178381719 568792902169549056267572579)
          ·
            refine ⟨853189353254323584401358869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568792902169549056267572579 853189353254323584401358869)
            ·
              refine ⟨39993250933796418018813697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 853189353254323584401358869 39993250933796418018813697)
              ·
                refine ⟨29994938200347313514110273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39993250933796418018813697 29994938200347313514110273)
                ·
                  refine ⟨22496203650260485135582705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29994938200347313514110273 22496203650260485135582705)
                  ·
                    refine ⟨16872152737695363851687029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22496203650260485135582705 16872152737695363851687029)
                    ·
                      refine ⟨1581764319158940361095659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16872152737695363851687029 1581764319158940361095659)
                      ·
                        rfl

theorem cell23_3080475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_3080475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080475 prefixEnd_3080475 := by exact prefixLift 3080475
  have htrace : WordTrace (prefixWord ++ tailWord_3080475) baseStart_3080475 baseEnd_3080475 := by
    simpa [prefixWord, tailWord_3080475, baseEnd_3080475] using wordTrace_append hprefix tailTrace_3080475
  have hstable : (prefixWord ++ tailWord_3080475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080475).length < 2 ^ (prefixWord ++ tailWord_3080475).sum := by decide
  have hdescent : baseEnd_3080475 < baseStart_3080475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080480 : List Nat := [2, 1, 1, 5, 2, 1, 4, 2, 1, 2, 2]
def baseStart_3080480 : Nat := 118140960795 + 3080480 * 2 ^ 59
def prefixEnd_3080480 : Nat := 4983230072969 + 3 ^ 40 * 3080480 * 2
def baseEnd_3080480 : Nat := 1581766886562212841533137

theorem tailTrace_3080480 : CollatzResearch.WordTrace tailWord_3080480 prefixEnd_3080480 1581766886562212841533137 := by
  unfold tailWord_3080480
  simp only [CollatzResearch.WordTrace]
  refine ⟨56177167939977269471911447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74902890586636359295881929 56177167939977269471911447)
  ·
    refine ⟨84265751909965904207867171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56177167939977269471911447 84265751909965904207867171)
    ·
      refine ⟨126398627864948856311800757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84265751909965904207867171 126398627864948856311800757)
      ·
        refine ⟨11849871362338955279231321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126398627864948856311800757 11849871362338955279231321)
        ·
          refine ⟨8887403521754216459423491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11849871362338955279231321 8887403521754216459423491)
          ·
            refine ⟨13331105282631324689135237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8887403521754216459423491 13331105282631324689135237)
            ·
              refine ⟨2499582240493373379212857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13331105282631324689135237 2499582240493373379212857)
              ·
                refine ⟨1874686680370030034409643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499582240493373379212857 1874686680370030034409643)
                ·
                  refine ⟨2812030020555045051614465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874686680370030034409643 2812030020555045051614465)
                  ·
                    refine ⟨2109022515416283788710849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2812030020555045051614465 2109022515416283788710849)
                    ·
                      refine ⟨1581766886562212841533137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109022515416283788710849 1581766886562212841533137)
                      ·
                        rfl

theorem cell23_3080480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_3080480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080480 prefixEnd_3080480 := by exact prefixLift 3080480
  have htrace : WordTrace (prefixWord ++ tailWord_3080480) baseStart_3080480 baseEnd_3080480 := by
    simpa [prefixWord, tailWord_3080480, baseEnd_3080480] using wordTrace_append hprefix tailTrace_3080480
  have hstable : (prefixWord ++ tailWord_3080480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080480).length < 2 ^ (prefixWord ++ tailWord_3080480).sum := by decide
  have hdescent : baseEnd_3080480 < baseStart_3080480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080482 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3080482 : Nat := 118140960795 + 3080482 * 2 ^ 59
def prefixEnd_3080482 : Nat := 4983230072969 + 3 ^ 40 * 3080482 * 2
def baseEnd_3080482 : Nat := 527255971174507277902709

theorem tailTrace_3080482 : CollatzResearch.WordTrace tailWord_3080482 prefixEnd_3080482 527255971174507277902709 := by
  unfold tailWord_3080482
  simp only [CollatzResearch.WordTrace]
  refine ⟨28088602206486823321348925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74902939217298195523597133 28088602206486823321348925)
  ·
    refine ⟨10533225827432558745505847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28088602206486823321348925 10533225827432558745505847)
    ·
      refine ⟨15799838741148838118258771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10533225827432558745505847 15799838741148838118258771)
      ·
        refine ⟨23699758111723257177388157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15799838741148838118258771 23699758111723257177388157)
        ·
          refine ⟨8887409291896221441520559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23699758111723257177388157 8887409291896221441520559)
          ·
            refine ⟨13331113937844332162280839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8887409291896221441520559 13331113937844332162280839)
            ·
              refine ⟨19996670906766498243421259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13331113937844332162280839 19996670906766498243421259)
              ·
                refine ⟨29995006360149747365131889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19996670906766498243421259 29995006360149747365131889)
                ·
                  refine ⟨22496254770112310523848917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29995006360149747365131889 22496254770112310523848917)
                  ·
                    refine ⟨527255971174507277902709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22496254770112310523848917 527255971174507277902709)
                    ·
                      rfl

theorem cell23_3080482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3080482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080482 prefixEnd_3080482 := by exact prefixLift 3080482
  have htrace : WordTrace (prefixWord ++ tailWord_3080482) baseStart_3080482 baseEnd_3080482 := by
    simpa [prefixWord, tailWord_3080482, baseEnd_3080482] using wordTrace_append hprefix tailTrace_3080482
  have hstable : (prefixWord ++ tailWord_3080482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080482).length < 2 ^ (prefixWord ++ tailWord_3080482).sum := by decide
  have hdescent : baseEnd_3080482 < baseStart_3080482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080495 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 1, 8]
def baseStart_3080495 : Nat := 118140960795 + 3080495 * 2 ^ 59
def prefixEnd_3080495 : Nat := 4983230072969 + 3 ^ 40 * 3080495 * 2
def baseEnd_3080495 : Nat := 527258196257343427615189

theorem tailTrace_3080495 : CollatzResearch.WordTrace tailWord_3080495 prefixEnd_3080495 527258196257343427615189 := by
  unfold tailWord_3080495
  simp only [CollatzResearch.WordTrace]
  refine ⟨112354882974900196505618939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74903255316600131003745959 112354882974900196505618939)
  ·
    refine ⟨168532324462350294758428409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112354882974900196505618939 168532324462350294758428409)
    ·
      refine ⟨126399243346762721068821307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168532324462350294758428409 126399243346762721068821307)
      ·
        refine ⟨189598865020144081603231961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126399243346762721068821307 189598865020144081603231961)
        ·
          refine ⟨142199148765108061202423971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189598865020144081603231961 142199148765108061202423971)
          ·
            refine ⟨213298723147662091803635957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142199148765108061202423971 213298723147662091803635957)
            ·
              refine ⟨19996755295093321106590871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213298723147662091803635957 19996755295093321106590871)
              ·
                refine ⟨29995132942639981659886307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19996755295093321106590871 29995132942639981659886307)
                ·
                  refine ⟨44992699413959972489829461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29995132942639981659886307 44992699413959972489829461)
                  ·
                    refine ⟨527258196257343427615189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44992699413959972489829461 527258196257343427615189)
                    ·
                      rfl

theorem cell23_3080495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_3080495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080495 prefixEnd_3080495 := by exact prefixLift 3080495
  have htrace : WordTrace (prefixWord ++ tailWord_3080495) baseStart_3080495 baseEnd_3080495 := by
    simpa [prefixWord, tailWord_3080495, baseEnd_3080495] using wordTrace_append hprefix tailTrace_3080495
  have hstable : (prefixWord ++ tailWord_3080495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080495).length < 2 ^ (prefixWord ++ tailWord_3080495).sum := by decide
  have hdescent : baseEnd_3080495 < baseStart_3080495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080519 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 1, 4, 2]
def baseStart_3080519 : Nat := 118140960795 + 3080519 * 2 ^ 59
def prefixEnd_3080519 : Nat := 4983230072969 + 3 ^ 40 * 3080519 * 2
def baseEnd_3080519 : Nat := 1581786912307738188945457

theorem tailTrace_3080519 : CollatzResearch.WordTrace tailWord_3080519 prefixEnd_3080519 1581786912307738188945457 := by
  unfold tailWord_3080519
  simp only [CollatzResearch.WordTrace]
  refine ⟨112355758326813248604492611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74903838884542165736328407 112355758326813248604492611)
  ·
    refine ⟨168533637490219872906738917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112355758326813248604492611 168533637490219872906738917)
    ·
      refine ⟨31600057029416226170013547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168533637490219872906738917 31600057029416226170013547)
      ·
        refine ⟨47400085544124339255020321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31600057029416226170013547 47400085544124339255020321)
        ·
          refine ⟨35550064158093254441265241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47400085544124339255020321 35550064158093254441265241)
          ·
            refine ⟨26662548118569940830948931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35550064158093254441265241 26662548118569940830948931)
            ·
              refine ⟨39993822177854911246423397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26662548118569940830948931 39993822177854911246423397)
              ·
                refine ⟨7498841658347795858704387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39993822177854911246423397 7498841658347795858704387)
                ·
                  refine ⟨11248262487521693788056581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7498841658347795858704387 11248262487521693788056581)
                  ·
                    refine ⟨2109049216410317585260609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11248262487521693788056581 2109049216410317585260609)
                    ·
                      refine ⟨1581786912307738188945457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109049216410317585260609 1581786912307738188945457)
                      ·
                        rfl

theorem cell23_3080519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_3080519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080519 prefixEnd_3080519 := by exact prefixLift 3080519
  have htrace : WordTrace (prefixWord ++ tailWord_3080519) baseStart_3080519 baseEnd_3080519 := by
    simpa [prefixWord, tailWord_3080519, baseEnd_3080519] using wordTrace_append hprefix tailTrace_3080519
  have hstable : (prefixWord ++ tailWord_3080519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080519).length < 2 ^ (prefixWord ++ tailWord_3080519).sum := by decide
  have hdescent : baseEnd_3080519 < baseStart_3080519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
