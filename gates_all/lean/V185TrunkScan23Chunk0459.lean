import V185TrunkScan23Chunk0458

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2715733 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 8]
def baseStart_2715733 : Nat := 118140960795 + 2715733 * 2 ^ 59
def prefixEnd_2715733 : Nat := 4983230072969 + 3 ^ 40 * 2715733 * 2
def baseEnd_2715733 : Nat := 154941817586303157316453

theorem tailTrace_2715733 : CollatzResearch.WordTrace tailWord_2715733 prefixEnd_2715733 154941817586303157316453 := by
  unfold tailWord_2715733
  simp only [CollatzResearch.WordTrace]
  refine ⟨99050919870370626115687853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66033946580247084077125235 99050919870370626115687853)
  ·
    refine ⟨37144094951388984793382945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99050919870370626115687853 37144094951388984793382945)
    ·
      refine ⟨27858071213541738595037209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37144094951388984793382945 27858071213541738595037209)
      ·
        refine ⟨20893553410156303946277907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27858071213541738595037209 20893553410156303946277907)
        ·
          refine ⟨31340330115234455919416861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20893553410156303946277907 31340330115234455919416861)
          ·
            refine ⟨11752623793212920969781323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31340330115234455919416861 11752623793212920969781323)
            ·
              refine ⟨17628935689819381454671985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11752623793212920969781323 17628935689819381454671985)
              ·
                refine ⟨13221701767364536091003989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17628935689819381454671985 13221701767364536091003989)
                ·
                  refine ⟨154941817586303157316453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13221701767364536091003989 154941817586303157316453)
                  ·
                    rfl

theorem cell23_2715733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_2715733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715733 prefixEnd_2715733 := by exact prefixLift 2715733
  have htrace : WordTrace (prefixWord ++ tailWord_2715733) baseStart_2715733 baseEnd_2715733 := by
    simpa [prefixWord, tailWord_2715733, baseEnd_2715733] using wordTrace_append hprefix tailTrace_2715733
  have hstable : (prefixWord ++ tailWord_2715733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715733).length < 2 ^ (prefixWord ++ tailWord_2715733).sum := by decide
  have hdescent : baseEnd_2715733 < baseStart_2715733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715754 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_2715754 : Nat := 118140960795 + 2715754 * 2 ^ 59
def prefixEnd_2715754 : Nat := 4983230072969 + 3 ^ 40 * 2715754 * 2
def baseEnd_2715754 : Nat := 464829047123490944561827

theorem tailTrace_2715754 : CollatzResearch.WordTrace tailWord_2715754 prefixEnd_2715754 464829047123490944561827 := by
  unfold tailWord_2715754
  simp only [CollatzResearch.WordTrace]
  refine ⟨24762921450823636675550579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66034457202196364468134877 24762921450823636675550579)
  ·
    refine ⟨37144382176235455013325869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24762921450823636675550579 37144382176235455013325869)
    ·
      refine ⟨13929143316088295629997201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37144382176235455013325869 13929143316088295629997201)
      ·
        refine ⟨10446857487066221722497901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13929143316088295629997201 10446857487066221722497901)
        ·
          refine ⟨3917571557649833145936713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10446857487066221722497901 3917571557649833145936713)
          ·
            refine ⟨2938178668237374859452535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3917571557649833145936713 2938178668237374859452535)
            ·
              refine ⟨4407268002356062289178803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2938178668237374859452535 4407268002356062289178803)
              ·
                refine ⟨6610902003534093433768205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4407268002356062289178803 6610902003534093433768205)
                ·
                  refine ⟨2479088251325285037663077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6610902003534093433768205 2479088251325285037663077)
                  ·
                    refine ⟨464829047123490944561827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2479088251325285037663077 464829047123490944561827)
                    ·
                      rfl

theorem cell23_2715754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_2715754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715754 prefixEnd_2715754 := by exact prefixLift 2715754
  have htrace : WordTrace (prefixWord ++ tailWord_2715754) baseStart_2715754 baseEnd_2715754 := by
    simpa [prefixWord, tailWord_2715754, baseEnd_2715754] using wordTrace_append hprefix tailTrace_2715754
  have hstable : (prefixWord ++ tailWord_2715754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715754).length < 2 ^ (prefixWord ++ tailWord_2715754).sum := by decide
  have hdescent : baseEnd_2715754 < baseStart_2715754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715767 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 6]
def baseStart_2715767 : Nat := 118140960795 + 2715767 * 2 ^ 59
def prefixEnd_2715767 : Nat := 4983230072969 + 3 ^ 40 * 2715767 * 2
def baseEnd_2715767 : Nat := 154943757402109031424769

theorem tailTrace_2715767 : CollatzResearch.WordTrace tailWord_2715767 prefixEnd_2715767 154943757402109031424769 := by
  unfold tailWord_2715767
  simp only [CollatzResearch.WordTrace]
  refine ⟨99052159952247449922425555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66034773301498299948283703 99052159952247449922425555)
  ·
    refine ⟨148578239928371174883638333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99052159952247449922425555 148578239928371174883638333)
    ·
      refine ⟨55716839973139190581364375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148578239928371174883638333 55716839973139190581364375)
      ·
        refine ⟨83575259959708785872046563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55716839973139190581364375 83575259959708785872046563)
        ·
          refine ⟨125362889939563178808069845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83575259959708785872046563 125362889939563178808069845)
          ·
            refine ⟨2938192732958512003314137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 125362889939563178808069845 2938192732958512003314137)
            ·
              refine ⟨2203644549718884002485603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2938192732958512003314137 2203644549718884002485603)
              ·
                refine ⟨3305466824578326003728405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203644549718884002485603 3305466824578326003728405)
                ·
                  refine ⟨154943757402109031424769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3305466824578326003728405 154943757402109031424769)
                  ·
                    rfl

theorem cell23_2715767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 6].length) (baseStart_2715767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715767 prefixEnd_2715767 := by exact prefixLift 2715767
  have htrace : WordTrace (prefixWord ++ tailWord_2715767) baseStart_2715767 baseEnd_2715767 := by
    simpa [prefixWord, tailWord_2715767, baseEnd_2715767] using wordTrace_append hprefix tailTrace_2715767
  have hstable : (prefixWord ++ tailWord_2715767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715767).length < 2 ^ (prefixWord ++ tailWord_2715767).sum := by decide
  have hdescent : baseEnd_2715767 < baseStart_2715767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715780 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_2715780 : Nat := 118140960795 + 2715780 * 2 ^ 59
def prefixEnd_2715780 : Nat := 4983230072969 + 3 ^ 40 * 2715780 * 2
def baseEnd_2715780 : Nat := 464833497289163243986787

theorem tailTrace_2715780 : CollatzResearch.WordTrace tailWord_2715780 prefixEnd_2715780 464833497289163243986787 := by
  unfold tailWord_2715780
  simp only [CollatzResearch.WordTrace]
  refine ⟨49526317050600176571324397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66035089400800235428432529 49526317050600176571324397)
  ·
    refine ⟨18572368893975066214246649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49526317050600176571324397 18572368893975066214246649)
    ·
      refine ⟨13929276670481299660684987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18572368893975066214246649 13929276670481299660684987)
      ·
        refine ⟨20893915005721949491027481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13929276670481299660684987 20893915005721949491027481)
        ·
          refine ⟨15670436254291462118270611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20893915005721949491027481 15670436254291462118270611)
          ·
            refine ⟨23505654381437193177405917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15670436254291462118270611 23505654381437193177405917)
            ·
              refine ⟨8814620393038947441527219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23505654381437193177405917 8814620393038947441527219)
              ·
                refine ⟨13221930589558421162290829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8814620393038947441527219 13221930589558421162290829)
                ·
                  refine ⟨4958223971084407935859061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13221930589558421162290829 4958223971084407935859061)
                  ·
                    refine ⟨464833497289163243986787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4958223971084407935859061 464833497289163243986787)
                    ·
                      rfl

theorem cell23_2715780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_2715780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715780 prefixEnd_2715780 := by exact prefixLift 2715780
  have htrace : WordTrace (prefixWord ++ tailWord_2715780) baseStart_2715780 baseEnd_2715780 := by
    simpa [prefixWord, tailWord_2715780, baseEnd_2715780] using wordTrace_append hprefix tailTrace_2715780
  have hstable : (prefixWord ++ tailWord_2715780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715780).length < 2 ^ (prefixWord ++ tailWord_2715780).sum := by decide
  have hdescent : baseEnd_2715780 < baseStart_2715780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715797 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 1, 5]
def baseStart_2715797 : Nat := 118140960795 + 2715797 * 2 ^ 59
def prefixEnd_2715797 : Nat := 4983230072969 + 3 ^ 40 * 2715797 * 2
def baseEnd_2715797 : Nat := 464836407012872055149261

theorem tailTrace_2715797 : CollatzResearch.WordTrace tailWord_2715797 prefixEnd_2715797 464836407012872055149261 := by
  unfold tailWord_2715797
  simp only [CollatzResearch.WordTrace]
  refine ⟨99053254142138765046017645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66035502761425843364011763 99053254142138765046017645)
  ·
    refine ⟨37144970303302036892256617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99053254142138765046017645 37144970303302036892256617)
    ·
      refine ⟨27858727727476527669192463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37144970303302036892256617 27858727727476527669192463)
      ·
        refine ⟨41788091591214791503788695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27858727727476527669192463 41788091591214791503788695)
        ·
          refine ⟨62682137386822187255683043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41788091591214791503788695 62682137386822187255683043)
          ·
            refine ⟨94023206080233280883524565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62682137386822187255683043 94023206080233280883524565)
            ·
              refine ⟨2203668892505467520707607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94023206080233280883524565 2203668892505467520707607)
              ·
                refine ⟨3305503338758201281061411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203668892505467520707607 3305503338758201281061411)
                ·
                  refine ⟨4958255008137301921592117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305503338758201281061411 4958255008137301921592117)
                  ·
                    refine ⟨464836407012872055149261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4958255008137301921592117 464836407012872055149261)
                    ·
                      rfl

theorem cell23_2715797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_2715797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715797 prefixEnd_2715797 := by exact prefixLift 2715797
  have htrace : WordTrace (prefixWord ++ tailWord_2715797) baseStart_2715797 baseEnd_2715797 := by
    simpa [prefixWord, tailWord_2715797, baseEnd_2715797] using wordTrace_append hprefix tailTrace_2715797
  have hstable : (prefixWord ++ tailWord_2715797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715797).length < 2 ^ (prefixWord ++ tailWord_2715797).sum := by decide
  have hdescent : baseEnd_2715797 < baseStart_2715797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715803 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 5]
def baseStart_2715803 : Nat := 118140960795 + 2715803 * 2 ^ 59
def prefixEnd_2715803 : Nat := 4983230072969 + 3 ^ 40 * 2715803 * 2
def baseEnd_2715803 : Nat := 1394512301922543141972755

theorem tailTrace_2715803 : CollatzResearch.WordTrace tailWord_2715803 prefixEnd_2715803 1394512301922543141972755 := by
  unfold tailWord_2715803
  simp only [CollatzResearch.WordTrace]
  refine ⟨99053472980117028070736063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66035648653411352047157375 99053472980117028070736063)
  ·
    refine ⟨148580209470175542106104095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99053472980117028070736063 148580209470175542106104095)
    ·
      refine ⟨222870314205263313159156143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148580209470175542106104095 222870314205263313159156143)
      ·
        refine ⟨334305471307894969738734215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222870314205263313159156143 334305471307894969738734215)
        ·
          refine ⟨501458206961842454608101323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334305471307894969738734215 501458206961842454608101323)
          ·
            refine ⟨752187310442763681912151985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501458206961842454608101323 752187310442763681912151985)
            ·
              refine ⟨564140482832072761434113989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752187310442763681912151985 564140482832072761434113989)
              ·
                refine ⟨105776340531013642768896373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564140482832072761434113989 105776340531013642768896373)
                ·
                  refine ⟨9916531924782529009584035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105776340531013642768896373 9916531924782529009584035)
                  ·
                    refine ⟨14874797887173793514376053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9916531924782529009584035 14874797887173793514376053)
                    ·
                      refine ⟨1394512301922543141972755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14874797887173793514376053 1394512301922543141972755)
                      ·
                        rfl

theorem cell23_2715803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 5].length) (baseStart_2715803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715803 prefixEnd_2715803 := by exact prefixLift 2715803
  have htrace : WordTrace (prefixWord ++ tailWord_2715803) baseStart_2715803 baseEnd_2715803 := by
    simpa [prefixWord, tailWord_2715803, baseEnd_2715803] using wordTrace_append hprefix tailTrace_2715803
  have hstable : (prefixWord ++ tailWord_2715803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715803).length < 2 ^ (prefixWord ++ tailWord_2715803).sum := by decide
  have hdescent : baseEnd_2715803 < baseStart_2715803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715837 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_2715837 : Nat := 118140960795 + 2715837 * 2 ^ 59
def prefixEnd_2715837 : Nat := 4983230072969 + 3 ^ 40 * 2715837 * 2
def baseEnd_2715837 : Nat := 1394529760264796008947599

theorem tailTrace_2715837 : CollatzResearch.WordTrace tailWord_2715837 prefixEnd_2715837 1394529760264796008947599 := by
  unfold tailWord_2715837
  simp only [CollatzResearch.WordTrace]
  refine ⟨99054713061993851877473765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66036475374662567918315843 99054713061993851877473765)
  ·
    refine ⟨18572758699123847227026331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99054713061993851877473765 18572758699123847227026331)
    ·
      refine ⟨27859138048685770840539497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18572758699123847227026331 27859138048685770840539497)
      ·
        refine ⟨20894353536514328130404623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27859138048685770840539497 20894353536514328130404623)
        ·
          refine ⟨31341530304771492195606935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20894353536514328130404623 31341530304771492195606935)
          ·
            refine ⟨47012295457157238293410403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31341530304771492195606935 47012295457157238293410403)
            ·
              refine ⟨70518443185735857440115605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47012295457157238293410403 70518443185735857440115605)
              ·
                refine ⟨3305552024331368317505419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70518443185735857440115605 3305552024331368317505419)
                ·
                  refine ⟨4958328036497052476258129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305552024331368317505419 4958328036497052476258129)
                  ·
                    refine ⟨3718746027372789357193597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4958328036497052476258129 3718746027372789357193597)
                    ·
                      refine ⟨1394529760264796008947599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3718746027372789357193597 1394529760264796008947599)
                      ·
                        rfl

theorem cell23_2715837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_2715837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715837 prefixEnd_2715837 := by exact prefixLift 2715837
  have htrace : WordTrace (prefixWord ++ tailWord_2715837) baseStart_2715837 baseEnd_2715837 := by
    simpa [prefixWord, tailWord_2715837, baseEnd_2715837] using wordTrace_append hprefix tailTrace_2715837
  have hstable : (prefixWord ++ tailWord_2715837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715837).length < 2 ^ (prefixWord ++ tailWord_2715837).sum := by decide
  have hdescent : baseEnd_2715837 < baseStart_2715837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715838 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_2715838 : Nat := 118140960795 + 2715838 * 2 ^ 59
def prefixEnd_2715838 : Nat := 4983230072969 + 3 ^ 40 * 2715838 * 2
def baseEnd_2715838 : Nat := 1394530273745450505035095

theorem tailTrace_2715838 : CollatzResearch.WordTrace tailWord_2715838 prefixEnd_2715838 1394530273745450505035095 := by
  unfold tailWord_2715838
  simp only [CollatzResearch.WordTrace]
  refine ⟨12381843691873778631032521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66036499689993486032173445 12381843691873778631032521)
  ·
    refine ⟨9286382768905333973274391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12381843691873778631032521 9286382768905333973274391)
    ·
      refine ⟨13929574153358000959911587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9286382768905333973274391 13929574153358000959911587)
      ·
        refine ⟨20894361230037001439867381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13929574153358000959911587 20894361230037001439867381)
        ·
          refine ⟨1958846365315968884987567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20894361230037001439867381 1958846365315968884987567)
          ·
            refine ⟨2938269547973953327481351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958846365315968884987567 2938269547973953327481351)
            ·
              refine ⟨4407404321960929991222027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2938269547973953327481351 4407404321960929991222027)
              ·
                refine ⟨6611106482941394986833041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4407404321960929991222027 6611106482941394986833041)
                ·
                  refine ⟨4958329862206046240124781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6611106482941394986833041 4958329862206046240124781)
                  ·
                    refine ⟨1859373698327267340046793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4958329862206046240124781 1859373698327267340046793)
                    ·
                      refine ⟨1394530273745450505035095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859373698327267340046793 1394530273745450505035095)
                      ·
                        rfl

theorem cell23_2715838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_2715838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715838 prefixEnd_2715838 := by exact prefixLift 2715838
  have htrace : WordTrace (prefixWord ++ tailWord_2715838) baseStart_2715838 baseEnd_2715838 := by
    simpa [prefixWord, tailWord_2715838, baseEnd_2715838] using wordTrace_append hprefix tailTrace_2715838
  have hstable : (prefixWord ++ tailWord_2715838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715838).length < 2 ^ (prefixWord ++ tailWord_2715838).sum := by decide
  have hdescent : baseEnd_2715838 < baseStart_2715838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715843 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 6]
def baseStart_2715843 : Nat := 118140960795 + 2715843 * 2 ^ 59
def prefixEnd_2715843 : Nat := 4983230072969 + 3 ^ 40 * 2715843 * 2
def baseEnd_2715843 : Nat := 1394532841148722985472571

theorem tailTrace_2715843 : CollatzResearch.WordTrace tailWord_2715843 prefixEnd_2715843 1394532841148722985472571 := by
  unfold tailWord_2715843
  simp only [CollatzResearch.WordTrace]
  refine ⟨99054931899972114902192183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66036621266648076601461455 99054931899972114902192183)
  ·
    refine ⟨148582397849958172353288275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99054931899972114902192183 148582397849958172353288275)
    ·
      refine ⟨222873596774937258529932413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148582397849958172353288275 222873596774937258529932413)
      ·
        refine ⟨83577598790601471948724655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222873596774937258529932413 83577598790601471948724655)
        ·
          refine ⟨125366398185902207923086983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83577598790601471948724655 125366398185902207923086983)
          ·
            refine ⟨188049597278853311884630475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125366398185902207923086983 188049597278853311884630475)
            ·
              refine ⟨282074395918279967826945713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188049597278853311884630475 282074395918279967826945713)
              ·
                refine ⟨211555796938709975870209285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282074395918279967826945713 211555796938709975870209285)
                ·
                  refine ⟨39666711926008120475664241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211555796938709975870209285 39666711926008120475664241)
                  ·
                    refine ⟨29750033944506090356748181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39666711926008120475664241 29750033944506090356748181)
                    ·
                      refine ⟨1394532841148722985472571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29750033944506090356748181 1394532841148722985472571)
                      ·
                        rfl

theorem cell23_2715843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_2715843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715843 prefixEnd_2715843 := by exact prefixLift 2715843
  have htrace : WordTrace (prefixWord ++ tailWord_2715843) baseStart_2715843 baseEnd_2715843 := by
    simpa [prefixWord, tailWord_2715843, baseEnd_2715843] using wordTrace_append hprefix tailTrace_2715843
  have hstable : (prefixWord ++ tailWord_2715843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715843).length < 2 ^ (prefixWord ++ tailWord_2715843).sum := by decide
  have hdescent : baseEnd_2715843 < baseStart_2715843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715851 : List Nat := [1, 1, 1, 1, 3, 2, 6, 3, 1, 2, 2]
def baseStart_2715851 : Nat := 118140960795 + 2715851 * 2 ^ 59
def prefixEnd_2715851 : Nat := 4983230072969 + 3 ^ 40 * 2715851 * 2
def baseEnd_2715851 : Nat := 1394536948993958954172535

theorem tailTrace_2715851 : CollatzResearch.WordTrace tailWord_2715851 prefixEnd_2715851 1394536948993958954172535 := by
  unfold tailWord_2715851
  simp only [CollatzResearch.WordTrace]
  refine ⟨99055223683943132268483407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66036815789295421512322271 99055223683943132268483407)
  ·
    refine ⟨148582835525914698402725111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99055223683943132268483407 148582835525914698402725111)
    ·
      refine ⟨222874253288872047604087667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148582835525914698402725111 222874253288872047604087667)
      ·
        refine ⟨334311379933308071406131501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222874253288872047604087667 334311379933308071406131501)
        ·
          refine ⟨125366767474990526777299313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334311379933308071406131501 125366767474990526777299313)
          ·
            refine ⟨94025075606242895082974485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125366767474990526777299313 94025075606242895082974485)
            ·
              refine ⟨4407425419042635707014429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94025075606242895082974485 4407425419042635707014429)
              ·
                refine ⟨1652784532140988390130411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4407425419042635707014429 1652784532140988390130411)
                ·
                  refine ⟨2479176798211482585195617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652784532140988390130411 2479176798211482585195617)
                  ·
                    refine ⟨1859382598658611938896713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2479176798211482585195617 1859382598658611938896713)
                    ·
                      refine ⟨1394536948993958954172535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859382598658611938896713 1394536948993958954172535)
                      ·
                        rfl

theorem cell23_2715851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 1, 2, 2].length) (baseStart_2715851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715851 prefixEnd_2715851 := by exact prefixLift 2715851
  have htrace : WordTrace (prefixWord ++ tailWord_2715851) baseStart_2715851 baseEnd_2715851 := by
    simpa [prefixWord, tailWord_2715851, baseEnd_2715851] using wordTrace_append hprefix tailTrace_2715851
  have hstable : (prefixWord ++ tailWord_2715851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715851).length < 2 ^ (prefixWord ++ tailWord_2715851).sum := by decide
  have hdescent : baseEnd_2715851 < baseStart_2715851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715854 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_2715854 : Nat := 118140960795 + 2715854 * 2 ^ 59
def prefixEnd_2715854 : Nat := 4983230072969 + 3 ^ 40 * 2715854 * 2
def baseEnd_2715854 : Nat := 1394538489435922442435021

theorem tailTrace_2715854 : CollatzResearch.WordTrace tailWord_2715854 prefixEnd_2715854 1394538489435922442435021 := by
  unfold tailWord_2715854
  simp only [CollatzResearch.WordTrace]
  refine ⟨12381916637866532972605327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66036888735288175853895077 12381916637866532972605327)
  ·
    refine ⟨18572874956799799458907991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12381916637866532972605327 18572874956799799458907991)
    ·
      refine ⟨27859312435199699188361987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18572874956799799458907991 27859312435199699188361987)
      ·
        refine ⟨41788968652799548782542981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27859312435199699188361987 41788968652799548782542981)
        ·
          refine ⟨7835431622399915396726809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41788968652799548782542981 7835431622399915396726809)
          ·
            refine ⟨5876573716799936547545107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7835431622399915396726809 5876573716799936547545107)
            ·
              refine ⟨8814860575199904821317661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5876573716799936547545107 8814860575199904821317661)
              ·
                refine ⟨3305572715699964307994123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8814860575199904821317661 3305572715699964307994123)
                ·
                  refine ⟨4958359073549946461991185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305572715699964307994123 4958359073549946461991185)
                  ·
                    refine ⟨3718769305162459846493389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4958359073549946461991185 3718769305162459846493389)
                    ·
                      refine ⟨1394538489435922442435021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3718769305162459846493389 1394538489435922442435021)
                      ·
                        rfl

theorem cell23_2715854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_2715854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715854 prefixEnd_2715854 := by exact prefixLift 2715854
  have htrace : WordTrace (prefixWord ++ tailWord_2715854) baseStart_2715854 baseEnd_2715854 := by
    simpa [prefixWord, tailWord_2715854, baseEnd_2715854] using wordTrace_append hprefix tailTrace_2715854
  have hstable : (prefixWord ++ tailWord_2715854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715854).length < 2 ^ (prefixWord ++ tailWord_2715854).sum := by decide
  have hdescent : baseEnd_2715854 < baseStart_2715854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715861 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_2715861 : Nat := 118140960795 + 2715861 * 2 ^ 59
def prefixEnd_2715861 : Nat := 4983230072969 + 3 ^ 40 * 2715861 * 2
def baseEnd_2715861 : Nat := 464847361266834638349163

theorem tailTrace_2715861 : CollatzResearch.WordTrace tailWord_2715861 prefixEnd_2715861 464847361266834638349163 := by
  unfold tailWord_2715861
  simp only [CollatzResearch.WordTrace]
  refine ⟨99055588413906903976347437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66037058942604602650898291 99055588413906903976347437)
  ·
    refine ⟨37145845655215088991130289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99055588413906903976347437 37145845655215088991130289)
    ·
      refine ⟨27859384241411316743347717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37145845655215088991130289 27859384241411316743347717)
      ·
        refine ⟨5223634545264621889377697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27859384241411316743347717 5223634545264621889377697)
        ·
          refine ⟨3917725908948466417033273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5223634545264621889377697 3917725908948466417033273)
          ·
            refine ⟨2938294431711349812774955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3917725908948466417033273 2938294431711349812774955)
            ·
              refine ⟨4407441647567024719162433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2938294431711349812774955 4407441647567024719162433)
              ·
                refine ⟨3305581235675268539371825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4407441647567024719162433 3305581235675268539371825)
                ·
                  refine ⟨2479185926756451404528869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3305581235675268539371825 2479185926756451404528869)
                  ·
                    refine ⟨464847361266834638349163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2479185926756451404528869 464847361266834638349163)
                    ·
                      rfl

theorem cell23_2715861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_2715861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715861 prefixEnd_2715861 := by exact prefixLift 2715861
  have htrace : WordTrace (prefixWord ++ tailWord_2715861) baseStart_2715861 baseEnd_2715861 := by
    simpa [prefixWord, tailWord_2715861, baseEnd_2715861] using wordTrace_append hprefix tailTrace_2715861
  have hstable : (prefixWord ++ tailWord_2715861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715861).length < 2 ^ (prefixWord ++ tailWord_2715861).sum := by decide
  have hdescent : baseEnd_2715861 < baseStart_2715861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715894 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_2715894 : Nat := 118140960795 + 2715894 * 2 ^ 59
def prefixEnd_2715894 : Nat := 4983230072969 + 3 ^ 40 * 2715894 * 2
def baseEnd_2715894 : Nat := 1394559028662102285934837

theorem tailTrace_2715894 : CollatzResearch.WordTrace tailWord_2715894 prefixEnd_2715894 1394559028662102285934837 := by
  unfold tailWord_2715894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6191049501424209413268671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66037861348524900408199157 6191049501424209413268671)
  ·
    refine ⟨9286574252136314119903007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6191049501424209413268671 9286574252136314119903007)
    ·
      refine ⟨13929861378204471179854511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9286574252136314119903007 13929861378204471179854511)
      ·
        refine ⟨20894792067306706769781767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13929861378204471179854511 20894792067306706769781767)
        ·
          refine ⟨31342188100960060154672651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20894792067306706769781767 31342188100960060154672651)
          ·
            refine ⟨47013282151440090232008977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31342188100960060154672651 47013282151440090232008977)
            ·
              refine ⟨35259961613580067674006733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47013282151440090232008977 35259961613580067674006733)
              ·
                refine ⟨13222485605092525377752525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35259961613580067674006733 13222485605092525377752525)
                ·
                  refine ⟨4958432101909697016657197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13222485605092525377752525 4958432101909697016657197)
                  ·
                    refine ⟨1859412038216136381246449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4958432101909697016657197 1859412038216136381246449)
                    ·
                      refine ⟨1394559028662102285934837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859412038216136381246449 1394559028662102285934837)
                      ·
                        rfl

theorem cell23_2715894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_2715894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715894 prefixEnd_2715894 := by exact prefixLift 2715894
  have htrace : WordTrace (prefixWord ++ tailWord_2715894) baseStart_2715894 baseEnd_2715894 := by
    simpa [prefixWord, tailWord_2715894, baseEnd_2715894] using wordTrace_append hprefix tailTrace_2715894
  have hstable : (prefixWord ++ tailWord_2715894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715894).length < 2 ^ (prefixWord ++ tailWord_2715894).sum := by decide
  have hdescent : baseEnd_2715894 < baseStart_2715894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715907 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 3, 4, 2]
def baseStart_2715907 : Nat := 118140960795 + 2715907 * 2 ^ 59
def prefixEnd_2715907 : Nat := 4983230072969 + 3 ^ 40 * 2715907 * 2
def baseEnd_2715907 : Nat := 1394565703910610735072277

theorem tailTrace_2715907 : CollatzResearch.WordTrace tailWord_2715907 prefixEnd_2715907 1394565703910610735072277 := by
  unfold tailWord_2715907
  simp only [CollatzResearch.WordTrace]
  refine ⟨99057266171740253832521975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66038177447826835888347983 99057266171740253832521975)
  ·
    refine ⟨148585899257610380748782963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99057266171740253832521975 148585899257610380748782963)
    ·
      refine ⟨222878848886415571123174445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148585899257610380748782963 222878848886415571123174445)
      ·
        refine ⟨83579568332405839171190417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222878848886415571123174445 83579568332405839171190417)
        ·
          refine ⟨62684676249304379378392813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83579568332405839171190417 62684676249304379378392813)
          ·
            refine ⟨23506753593489142266897305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62684676249304379378392813 23506753593489142266897305)
            ·
              refine ⟨17630065195116856700172979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23506753593489142266897305 17630065195116856700172979)
              ·
                refine ⟨26445097792675285050259469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17630065195116856700172979 26445097792675285050259469)
                ·
                  refine ⟨9916911672253231893847301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26445097792675285050259469 9916911672253231893847301)
                  ·
                    refine ⟨1859420938547480980096369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9916911672253231893847301 1859420938547480980096369)
                    ·
                      refine ⟨1394565703910610735072277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859420938547480980096369 1394565703910610735072277)
                      ·
                        rfl

theorem cell23_2715907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_2715907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715907 prefixEnd_2715907 := by exact prefixLift 2715907
  have htrace : WordTrace (prefixWord ++ tailWord_2715907) baseStart_2715907 baseEnd_2715907 := by
    simpa [prefixWord, tailWord_2715907, baseEnd_2715907] using wordTrace_append hprefix tailTrace_2715907
  have hstable : (prefixWord ++ tailWord_2715907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715907).length < 2 ^ (prefixWord ++ tailWord_2715907).sum := by decide
  have hdescent : baseEnd_2715907 < baseStart_2715907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715960 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 1, 7]
def baseStart_2715960 : Nat := 118140960795 + 2715960 * 2 ^ 59
def prefixEnd_2715960 : Nat := 4983230072969 + 3 ^ 40 * 2715960 * 2
def baseEnd_2715960 : Nat := 464864306128433009236511

theorem tailTrace_2715960 : CollatzResearch.WordTrace tailWord_2715960 prefixEnd_2715960 464864306128433009236511 := by
  unfold tailWord_2715960
  simp only [CollatzResearch.WordTrace]
  refine ⟨49529599620274121942100667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66039466160365495922800889 49529599620274121942100667)
  ·
    refine ⟨74294399430411182913151001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49529599620274121942100667 74294399430411182913151001)
    ·
      refine ⟨55720799572808387184863251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74294399430411182913151001 55720799572808387184863251)
      ·
        refine ⟨83581199359212580777294877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55720799572808387184863251 83581199359212580777294877)
        ·
          refine ⟨31342949759704717791485579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83581199359212580777294877 31342949759704717791485579)
          ·
            refine ⟨47014424639557076687228369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31342949759704717791485579 47014424639557076687228369)
            ·
              refine ⟨35260818479667807515421277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47014424639557076687228369 35260818479667807515421277)
              ·
                refine ⟨13222806929875427818282979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35260818479667807515421277 13222806929875427818282979)
                ·
                  refine ⟨19834210394813141727424469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13222806929875427818282979 19834210394813141727424469)
                  ·
                    refine ⟨464864306128433009236511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19834210394813141727424469 464864306128433009236511)
                    ·
                      rfl

theorem cell23_2715960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_2715960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2715960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2715960 prefixEnd_2715960 := by exact prefixLift 2715960
  have htrace : WordTrace (prefixWord ++ tailWord_2715960) baseStart_2715960 baseEnd_2715960 := by
    simpa [prefixWord, tailWord_2715960, baseEnd_2715960] using wordTrace_append hprefix tailTrace_2715960
  have hstable : (prefixWord ++ tailWord_2715960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715960).length < 2 ^ (prefixWord ++ tailWord_2715960).sum := by decide
  have hdescent : baseEnd_2715960 < baseStart_2715960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716041 : List Nat := [1, 2, 1, 1, 6, 1, 2, 4, 1, 4]
def baseStart_2716041 : Nat := 118140960795 + 2716041 * 2 ^ 59
def prefixEnd_2716041 : Nat := 4983230072969 + 3 ^ 40 * 2716041 * 2
def baseEnd_2716041 : Nat := 464878170106104403598887

theorem tailTrace_2716041 : CollatzResearch.WordTrace tailWord_2716041 prefixEnd_2716041 464878170106104403598887 := by
  unfold tailWord_2716041
  simp only [CollatzResearch.WordTrace]
  refine ⟨99062153553254794717899977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66041435702169863145266651 99062153553254794717899977)
  ·
    refine ⟨74296615164941096038424983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99062153553254794717899977 74296615164941096038424983)
    ·
      refine ⟨111444922747411644057637475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74296615164941096038424983 111444922747411644057637475)
      ·
        refine ⟨167167384121117466086456213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111444922747411644057637475 167167384121117466086456213)
        ·
          refine ⟨7835971130677381222802635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 167167384121117466086456213 7835971130677381222802635)
          ·
            refine ⟨11753956696016071834203953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7835971130677381222802635 11753956696016071834203953)
            ·
              refine ⟨8815467522012053875652965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11753956696016071834203953 8815467522012053875652965)
              ·
                refine ⟨1652900160377260101684931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8815467522012053875652965 1652900160377260101684931)
                ·
                  refine ⟨2479350240565890152527397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652900160377260101684931 2479350240565890152527397)
                  ·
                    refine ⟨464878170106104403598887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2479350240565890152527397 464878170106104403598887)
                    ·
                      rfl

theorem cell23_2716041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 1, 4].length) (baseStart_2716041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716041 prefixEnd_2716041 := by exact prefixLift 2716041
  have htrace : WordTrace (prefixWord ++ tailWord_2716041) baseStart_2716041 baseEnd_2716041 := by
    simpa [prefixWord, tailWord_2716041, baseEnd_2716041] using wordTrace_append hprefix tailTrace_2716041
  have hstable : (prefixWord ++ tailWord_2716041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716041).length < 2 ^ (prefixWord ++ tailWord_2716041).sum := by decide
  have hdescent : baseEnd_2716041 < baseStart_2716041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716107 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 3]
def baseStart_2716107 : Nat := 118140960795 + 2716107 * 2 ^ 59
def prefixEnd_2716107 : Nat := 4983230072969 + 3 ^ 40 * 2716107 * 2
def baseEnd_2716107 : Nat := 1394668400041509952571357

theorem tailTrace_2716107 : CollatzResearch.WordTrace tailWord_2716107 prefixEnd_2716107 1394668400041509952571357 := by
  unfold tailWord_2716107
  simp only [CollatzResearch.WordTrace]
  refine ⟨99064560771015687989802575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66043040514010458659868383 99064560771015687989802575)
  ·
    refine ⟨148596841156523531984703863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99064560771015687989802575 148596841156523531984703863)
    ·
      refine ⟨222895261734785297977055795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148596841156523531984703863 222895261734785297977055795)
      ·
        refine ⟨334342892602177946965583693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222895261734785297977055795 334342892602177946965583693)
        ·
          refine ⟨125378584725816730112093885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334342892602177946965583693 125378584725816730112093885)
          ·
            refine ⟨47016969272181273792035207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125378584725816730112093885 47016969272181273792035207)
            ·
              refine ⟨70525453908271910688052811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47016969272181273792035207 70525453908271910688052811)
              ·
                refine ⟨105788180862407866032079217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70525453908271910688052811 105788180862407866032079217)
                ·
                  refine ⟨79341135646805899524059413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105788180862407866032079217 79341135646805899524059413)
                  ·
                    refine ⟨3719115733444026540190285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79341135646805899524059413 3719115733444026540190285)
                    ·
                      refine ⟨1394668400041509952571357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719115733444026540190285 1394668400041509952571357)
                      ·
                        rfl

theorem cell23_2716107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 3].length) (baseStart_2716107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716107 prefixEnd_2716107 := by exact prefixLift 2716107
  have htrace : WordTrace (prefixWord ++ tailWord_2716107) baseStart_2716107 baseEnd_2716107 := by
    simpa [prefixWord, tailWord_2716107, baseEnd_2716107] using wordTrace_append hprefix tailTrace_2716107
  have hstable : (prefixWord ++ tailWord_2716107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716107).length < 2 ^ (prefixWord ++ tailWord_2716107).sum := by decide
  have hdescent : baseEnd_2716107 < baseStart_2716107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716121 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 5, 2, 2]
def baseStart_2716121 : Nat := 118140960795 + 2716121 * 2 ^ 59
def prefixEnd_2716121 : Nat := 4983230072969 + 3 ^ 40 * 2716121 * 2
def baseEnd_2716121 : Nat := 1394675588770672897796293

theorem tailTrace_2716121 : CollatzResearch.WordTrace tailWord_2716121 prefixEnd_2716121 1394675588770672897796293 := by
  unfold tailWord_2716121
  simp only [CollatzResearch.WordTrace]
  refine ⟨99065071392964968380812217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66043380928643312253874811 99065071392964968380812217)
  ·
    refine ⟨74298803544723726285609163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99065071392964968380812217 74298803544723726285609163)
    ·
      refine ⟨111448205317085589428413745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74298803544723726285609163 111448205317085589428413745)
      ·
        refine ⟨83586153987814192071310309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111448205317085589428413745 83586153987814192071310309)
        ·
          refine ⟨15672403872715161013370683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83586153987814192071310309 15672403872715161013370683)
          ·
            refine ⟨23508605809072741520056025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15672403872715161013370683 23508605809072741520056025)
            ·
              refine ⟨17631454356804556140042019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23508605809072741520056025 17631454356804556140042019)
              ·
                refine ⟨26447181535206834210063029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17631454356804556140042019 26447181535206834210063029)
                ·
                  refine ⟨2479423268925640707193409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26447181535206834210063029 2479423268925640707193409)
                  ·
                    refine ⟨1859567451694230530395057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2479423268925640707193409 1859567451694230530395057)
                    ·
                      refine ⟨1394675588770672897796293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859567451694230530395057 1394675588770672897796293)
                      ·
                        rfl

theorem cell23_2716121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_2716121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716121 prefixEnd_2716121 := by exact prefixLift 2716121
  have htrace : WordTrace (prefixWord ++ tailWord_2716121) baseStart_2716121 baseEnd_2716121 := by
    simpa [prefixWord, tailWord_2716121, baseEnd_2716121] using wordTrace_append hprefix tailTrace_2716121
  have hstable : (prefixWord ++ tailWord_2716121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716121).length < 2 ^ (prefixWord ++ tailWord_2716121).sum := by decide
  have hdescent : baseEnd_2716121 < baseStart_2716121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716127 : List Nat := [1, 1, 2, 3, 3, 2, 2, 9]
def baseStart_2716127 : Nat := 118140960795 + 2716127 * 2 ^ 59
def prefixEnd_2716127 : Nat := 4983230072969 + 3 ^ 40 * 2716127 * 2
def baseEnd_2716127 : Nat := 51654765542762958308195

theorem tailTrace_2716127 : CollatzResearch.WordTrace tailWord_2716127 prefixEnd_2716127 51654765542762958308195 := by
  unfold tailWord_2716127
  simp only [CollatzResearch.WordTrace]
  refine ⟨99065290230943231405530635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66043526820628820937020423 99065290230943231405530635)
  ·
    refine ⟨148597935346414847108295953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99065290230943231405530635 148597935346414847108295953)
    ·
      refine ⟨111448451509811135331221965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148597935346414847108295953 111448451509811135331221965)
      ·
        refine ⟨41793169316179175749208237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111448451509811135331221965 41793169316179175749208237)
        ·
          refine ⟨15672438493567190905953089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41793169316179175749208237 15672438493567190905953089)
          ·
            refine ⟨11754328870175393179464817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15672438493567190905953089 11754328870175393179464817)
            ·
              refine ⟨8815746652631544884598613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11754328870175393179464817 8815746652631544884598613)
              ·
                refine ⟨51654765542762958308195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8815746652631544884598613 51654765542762958308195)
                ·
                  rfl

theorem cell23_2716127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 9].length) (baseStart_2716127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716127 prefixEnd_2716127 := by exact prefixLift 2716127
  have htrace : WordTrace (prefixWord ++ tailWord_2716127) baseStart_2716127 baseEnd_2716127 := by
    simpa [prefixWord, tailWord_2716127, baseEnd_2716127] using wordTrace_append hprefix tailTrace_2716127
  have hstable : (prefixWord ++ tailWord_2716127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716127).length < 2 ^ (prefixWord ++ tailWord_2716127).sum := by decide
  have hdescent : baseEnd_2716127 < baseStart_2716127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716138 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_2716138 : Nat := 118140960795 + 2716138 * 2 ^ 59
def prefixEnd_2716138 : Nat := 4983230072969 + 3 ^ 40 * 2716138 * 2
def baseEnd_2716138 : Nat := 1394684317941799331283715

theorem tailTrace_2716138 : CollatzResearch.WordTrace tailWord_2716138 prefixEnd_2716138 1394684317941799331283715 := by
  unfold tailWord_2716138
  simp only [CollatzResearch.WordTrace]
  refine ⟨24766422858475845071045267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66043794289268920189454045 24766422858475845071045267)
  ·
    refine ⟨37149634287713767606567901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24766422858475845071045267 37149634287713767606567901)
    ·
      refine ⟨13931112857892662852462963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37149634287713767606567901 13931112857892662852462963)
      ·
        refine ⟨20896669286838994278694445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13931112857892662852462963 20896669286838994278694445)
        ·
          refine ⟨7836250982564622854510417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20896669286838994278694445 7836250982564622854510417)
          ·
            refine ⟨5877188236923467140882813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7836250982564622854510417 5877188236923467140882813)
            ·
              refine ⟨2203945588846300177831055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5877188236923467140882813 2203945588846300177831055)
              ·
                refine ⟨3305918383269450266746583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203945588846300177831055 3305918383269450266746583)
                ·
                  refine ⟨4958877574904175400119875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305918383269450266746583 4958877574904175400119875)
                  ·
                    refine ⟨7438316362356263100179813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4958877574904175400119875 7438316362356263100179813)
                    ·
                      refine ⟨1394684317941799331283715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7438316362356263100179813 1394684317941799331283715)
                      ·
                        rfl

theorem cell23_2716138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_2716138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716138 prefixEnd_2716138 := by exact prefixLift 2716138
  have htrace : WordTrace (prefixWord ++ tailWord_2716138) baseStart_2716138 baseEnd_2716138 := by
    simpa [prefixWord, tailWord_2716138, baseEnd_2716138] using wordTrace_append hprefix tailTrace_2716138
  have hstable : (prefixWord ++ tailWord_2716138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716138).length < 2 ^ (prefixWord ++ tailWord_2716138).sum := by decide
  have hdescent : baseEnd_2716138 < baseStart_2716138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716141 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2716141 : Nat := 118140960795 + 2716141 * 2 ^ 59
def prefixEnd_2716141 : Nat := 4983230072969 + 3 ^ 40 * 2716141 * 2
def baseEnd_2716141 : Nat := 1394685858383762819546201

theorem tailTrace_2716141 : CollatzResearch.WordTrace tailWord_2716141 prefixEnd_2716141 1394685858383762819546201 := by
  unfold tailWord_2716141
  simp only [CollatzResearch.WordTrace]
  refine ⟨99065800852892511796540277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66043867235261674531026851 99065800852892511796540277)
  ·
    refine ⟨9287418829958672980925651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99065800852892511796540277 9287418829958672980925651)
    ·
      refine ⟨13931128244938009471388477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9287418829958672980925651 13931128244938009471388477)
      ·
        refine ⟨5224173091851753551770679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13931128244938009471388477 5224173091851753551770679)
        ·
          refine ⟨7836259637777630327656019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5224173091851753551770679 7836259637777630327656019)
          ·
            refine ⟨11754389456666445491484029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7836259637777630327656019 11754389456666445491484029)
            ·
              refine ⟨4407896046249917059306511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11754389456666445491484029 4407896046249917059306511)
              ·
                refine ⟨6611844069374875588959767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4407896046249917059306511 6611844069374875588959767)
                ·
                  refine ⟨9917766104062313383439651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6611844069374875588959767 9917766104062313383439651)
                  ·
                    refine ⟨14876649156093470075159477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9917766104062313383439651 14876649156093470075159477)
                    ·
                      refine ⟨1394685858383762819546201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14876649156093470075159477 1394685858383762819546201)
                      ·
                        rfl

theorem cell23_2716141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2716141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716141 prefixEnd_2716141 := by exact prefixLift 2716141
  have htrace : WordTrace (prefixWord ++ tailWord_2716141) baseStart_2716141 baseEnd_2716141 := by
    simpa [prefixWord, tailWord_2716141, baseEnd_2716141] using wordTrace_append hprefix tailTrace_2716141
  have hstable : (prefixWord ++ tailWord_2716141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716141).length < 2 ^ (prefixWord ++ tailWord_2716141).sum := by decide
  have hdescent : baseEnd_2716141 < baseStart_2716141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716149 : List Nat := [1, 3, 5, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_2716149 : Nat := 118140960795 + 2716149 * 2 ^ 59
def prefixEnd_2716149 : Nat := 4983230072969 + 3 ^ 40 * 2716149 * 2
def baseEnd_2716149 : Nat := 1394689966228998788246165

theorem tailTrace_2716149 : CollatzResearch.WordTrace tailWord_2716149 prefixEnd_2716149 1394689966228998788246165 := by
  unfold tailWord_2716149
  simp only [CollatzResearch.WordTrace]
  refine ⟨99066092636863529162831501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66044061757909019441887667 99066092636863529162831501)
  ·
    refine ⟨37149784738823823436061813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99066092636863529162831501 37149784738823823436061813)
    ·
      refine ⟨3482792319264733447130795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37149784738823823436061813 3482792319264733447130795)
      ·
        refine ⟨5224188478897100170696193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3482792319264733447130795 5224188478897100170696193)
        ·
          refine ⟨3918141359172825128022145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5224188478897100170696193 3918141359172825128022145)
          ·
            refine ⟨2938606019379618846016609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3918141359172825128022145 2938606019379618846016609)
            ·
              refine ⟨2203954514534714134512457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2938606019379618846016609 2203954514534714134512457)
              ·
                refine ⟨1652965885901035600884343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2203954514534714134512457 1652965885901035600884343)
                ·
                  refine ⟨2479448828851553401326515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652965885901035600884343 2479448828851553401326515)
                  ·
                    refine ⟨3719173243277330101989773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2479448828851553401326515 3719173243277330101989773)
                    ·
                      refine ⟨1394689966228998788246165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719173243277330101989773 1394689966228998788246165)
                      ·
                        rfl

theorem cell23_2716149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_2716149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716149 prefixEnd_2716149 := by exact prefixLift 2716149
  have htrace : WordTrace (prefixWord ++ tailWord_2716149) baseStart_2716149 baseEnd_2716149 := by
    simpa [prefixWord, tailWord_2716149, baseEnd_2716149] using wordTrace_append hprefix tailTrace_2716149
  have hstable : (prefixWord ++ tailWord_2716149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716149).length < 2 ^ (prefixWord ++ tailWord_2716149).sum := by decide
  have hdescent : baseEnd_2716149 < baseStart_2716149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716157 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_2716157 : Nat := 118140960795 + 2716157 * 2 ^ 59
def prefixEnd_2716157 : Nat := 4983230072969 + 3 ^ 40 * 2716157 * 2
def baseEnd_2716157 : Nat := 464898024691411585648709

theorem tailTrace_2716157 : CollatzResearch.WordTrace tailWord_2716157 prefixEnd_2716157 464898024691411585648709 := by
  unfold tailWord_2716157
  simp only [CollatzResearch.WordTrace]
  refine ⟨99066384420834546529122725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66044256280556364352748483 99066384420834546529122725)
  ·
    refine ⟨18574947078906477474210511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99066384420834546529122725 18574947078906477474210511)
    ·
      refine ⟨27862420618359716211315767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18574947078906477474210511 27862420618359716211315767)
      ·
        refine ⟨41793630927539574316973651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27862420618359716211315767 41793630927539574316973651)
        ·
          refine ⟨62690446391309361475460477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41793630927539574316973651 62690446391309361475460477)
          ·
            refine ⟨23508917396741010553297679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62690446391309361475460477 23508917396741010553297679)
            ·
              refine ⟨35263376095111515829946519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23508917396741010553297679 35263376095111515829946519)
              ·
                refine ⟨52895064142667273744919779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35263376095111515829946519 52895064142667273744919779)
                ·
                  refine ⟨79342596214000910617379669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52895064142667273744919779 79342596214000910617379669)
                  ·
                    refine ⟨464898024691411585648709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79342596214000910617379669 464898024691411585648709)
                    ·
                      rfl

theorem cell23_2716157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_2716157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716157 prefixEnd_2716157 := by exact prefixLift 2716157
  have htrace : WordTrace (prefixWord ++ tailWord_2716157) baseStart_2716157 baseEnd_2716157 := by
    simpa [prefixWord, tailWord_2716157, baseEnd_2716157] using wordTrace_append hprefix tailTrace_2716157
  have hstable : (prefixWord ++ tailWord_2716157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716157).length < 2 ^ (prefixWord ++ tailWord_2716157).sum := by decide
  have hdescent : baseEnd_2716157 < baseStart_2716157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716171 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 3]
def baseStart_2716171 : Nat := 118140960795 + 2716171 * 2 ^ 59
def prefixEnd_2716171 : Nat := 4983230072969 + 3 ^ 40 * 2716171 * 2
def baseEnd_2716171 : Nat := 1394701262803397702171063

theorem tailTrace_2716171 : CollatzResearch.WordTrace tailWord_2716171 prefixEnd_2716171 1394701262803397702171063 := by
  unfold tailWord_2716171
  simp only [CollatzResearch.WordTrace]
  refine ⟨99066895042783826920132367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66044596695189217946754911 99066895042783826920132367)
  ·
    refine ⟨148600342564175740380198551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99066895042783826920132367 148600342564175740380198551)
    ·
      refine ⟨222900513846263610570297827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148600342564175740380198551 222900513846263610570297827)
      ·
        refine ⟨334350770769395415855446741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222900513846263610570297827 334350770769395415855446741)
        ·
          refine ⟨7836346189907705059112033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 334350770769395415855446741 7836346189907705059112033)
          ·
            refine ⟨5877259642430778794334025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7836346189907705059112033 5877259642430778794334025)
            ·
              refine ⟨4407944731823084095750519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5877259642430778794334025 4407944731823084095750519)
              ·
                refine ⟨6611917097734626143625779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4407944731823084095750519 6611917097734626143625779)
                ·
                  refine ⟨9917875646601939215438669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6611917097734626143625779 9917875646601939215438669)
                  ·
                    refine ⟨3719203367475727205789501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9917875646601939215438669 3719203367475727205789501)
                    ·
                      refine ⟨1394701262803397702171063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719203367475727205789501 1394701262803397702171063)
                      ·
                        rfl

theorem cell23_2716171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 3].length) (baseStart_2716171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716171 prefixEnd_2716171 := by exact prefixLift 2716171
  have htrace : WordTrace (prefixWord ++ tailWord_2716171) baseStart_2716171 baseEnd_2716171 := by
    simpa [prefixWord, tailWord_2716171, baseEnd_2716171] using wordTrace_append hprefix tailTrace_2716171
  have hstable : (prefixWord ++ tailWord_2716171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716171).length < 2 ^ (prefixWord ++ tailWord_2716171).sum := by decide
  have hdescent : baseEnd_2716171 < baseStart_2716171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716181 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 3, 3, 2]
def baseStart_2716181 : Nat := 118140960795 + 2716181 * 2 ^ 59
def prefixEnd_2716181 : Nat := 4983230072969 + 3 ^ 40 * 2716181 * 2
def baseEnd_2716181 : Nat := 1394706397609942663046017

theorem tailTrace_2716181 : CollatzResearch.WordTrace tailWord_2716181 prefixEnd_2716181 1394706397609942663046017 := by
  unfold tailWord_2716181
  simp only [CollatzResearch.WordTrace]
  refine ⟨99067259772747598627996397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66044839848498399085330931 99067259772747598627996397)
  ·
    refine ⟨37150222414780349485498649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99067259772747598627996397 37150222414780349485498649)
    ·
      refine ⟨27862666811085262114123987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37150222414780349485498649 27862666811085262114123987)
      ·
        refine ⟨41794000216627893171185981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27862666811085262114123987 41794000216627893171185981)
        ·
          refine ⟨15672750081235459939194743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41794000216627893171185981 15672750081235459939194743)
          ·
            refine ⟨23509125121853189908792115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15672750081235459939194743 23509125121853189908792115)
            ·
              refine ⟨35263687682779784863188173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23509125121853189908792115 35263687682779784863188173)
              ·
                refine ⟨13223882881042419323695565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35263687682779784863188173 13223882881042419323695565)
                ·
                  refine ⟨4958956080390907246385837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13223882881042419323695565 4958956080390907246385837)
                  ·
                    refine ⟨1859608530146590217394689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4958956080390907246385837 1859608530146590217394689)
                    ·
                      refine ⟨1394706397609942663046017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859608530146590217394689 1394706397609942663046017)
                      ·
                        rfl

theorem cell23_2716181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_2716181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716181 prefixEnd_2716181 := by exact prefixLift 2716181
  have htrace : WordTrace (prefixWord ++ tailWord_2716181) baseStart_2716181 baseEnd_2716181 := by
    simpa [prefixWord, tailWord_2716181, baseEnd_2716181] using wordTrace_append hprefix tailTrace_2716181
  have hstable : (prefixWord ++ tailWord_2716181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716181).length < 2 ^ (prefixWord ++ tailWord_2716181).sum := by decide
  have hdescent : baseEnd_2716181 < baseStart_2716181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716192 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2716192 : Nat := 118140960795 + 2716192 * 2 ^ 59
def prefixEnd_2716192 : Nat := 4983230072969 + 3 ^ 40 * 2716192 * 2
def baseEnd_2716192 : Nat := 1394712045897142120008467

theorem tailTrace_2716192 : CollatzResearch.WordTrace tailWord_2716192 prefixEnd_2716192 1394712045897142120008467 := by
  unfold tailWord_2716192
  simp only [CollatzResearch.WordTrace]
  refine ⟨49533830487853873753323415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66045107317138498337764553 49533830487853873753323415)
  ·
    refine ⟨74300745731780810629985123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49533830487853873753323415 74300745731780810629985123)
    ·
      refine ⟨111451118597671215944977685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74300745731780810629985123 111451118597671215944977685)
      ·
        refine ⟨5224271184265838247420829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111451118597671215944977685 5224271184265838247420829)
        ·
          refine ⟨1959101694099689342782811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5224271184265838247420829 1959101694099689342782811)
          ·
            refine ⟨2938652541149534014174217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959101694099689342782811 2938652541149534014174217)
            ·
              refine ⟨2203989405862150510630663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2938652541149534014174217 2203989405862150510630663)
              ·
                refine ⟨3305984108793225765945995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203989405862150510630663 3305984108793225765945995)
                ·
                  refine ⟨4958976163189838648918993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305984108793225765945995 4958976163189838648918993)
                  ·
                    refine ⟨3719232122392378986689245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4958976163189838648918993 3719232122392378986689245)
                    ·
                      refine ⟨1394712045897142120008467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719232122392378986689245 1394712045897142120008467)
                      ·
                        rfl

theorem cell23_2716192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2716192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716192 prefixEnd_2716192 := by exact prefixLift 2716192
  have htrace : WordTrace (prefixWord ++ tailWord_2716192) baseStart_2716192 baseEnd_2716192 := by
    simpa [prefixWord, tailWord_2716192, baseEnd_2716192] using wordTrace_append hprefix tailTrace_2716192
  have hstable : (prefixWord ++ tailWord_2716192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716192).length < 2 ^ (prefixWord ++ tailWord_2716192).sum := by decide
  have hdescent : baseEnd_2716192 < baseStart_2716192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716222 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_2716222 : Nat := 118140960795 + 2716222 * 2 ^ 59
def prefixEnd_2716222 : Nat := 4983230072969 + 3 ^ 40 * 2716222 * 2
def baseEnd_2716222 : Nat := 1394727450316777002633329

theorem tailTrace_2716222 : CollatzResearch.WordTrace tailWord_2716222 prefixEnd_2716222 1394727450316777002633329 := by
  unfold tailWord_2716222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12383594395699882828779865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66045836777066041753492613 12383594395699882828779865)
  ·
    refine ⟨9287695796774912121584899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12383594395699882828779865 9287695796774912121584899)
    ·
      refine ⟨13931543695162368182377349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9287695796774912121584899 13931543695162368182377349)
      ·
        refine ⟨2612164442842944034195753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13931543695162368182377349 2612164442842944034195753)
        ·
          refine ⟨1959123332132208025646815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2612164442842944034195753 1959123332132208025646815)
          ·
            refine ⟨2938684998198312038470223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959123332132208025646815 2938684998198312038470223)
            ·
              refine ⟨4408027497297468057705335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2938684998198312038470223 4408027497297468057705335)
              ·
                refine ⟨6612041245946202086558003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408027497297468057705335 6612041245946202086558003)
                ·
                  refine ⟨9918061868919303129837005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6612041245946202086558003 9918061868919303129837005)
                  ·
                    refine ⟨3719273200844738673688877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9918061868919303129837005 3719273200844738673688877)
                    ·
                      refine ⟨1394727450316777002633329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719273200844738673688877 1394727450316777002633329)
                      ·
                        rfl

theorem cell23_2716222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_2716222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716222 prefixEnd_2716222 := by exact prefixLift 2716222
  have htrace : WordTrace (prefixWord ++ tailWord_2716222) baseStart_2716222 baseEnd_2716222 := by
    simpa [prefixWord, tailWord_2716222, baseEnd_2716222] using wordTrace_append hprefix tailTrace_2716222
  have hstable : (prefixWord ++ tailWord_2716222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716222).length < 2 ^ (prefixWord ++ tailWord_2716222).sum := by decide
  have hdescent : baseEnd_2716222 < baseStart_2716222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716224 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_2716224 : Nat := 118140960795 + 2716224 * 2 ^ 59
def prefixEnd_2716224 : Nat := 4983230072969 + 3 ^ 40 * 2716224 * 2
def baseEnd_2716224 : Nat := 1394728477278085994808319

theorem tailTrace_2716224 : CollatzResearch.WordTrace tailWord_2716224 prefixEnd_2716224 1394728477278085994808319 := by
  unfold tailWord_2716224
  simp only [CollatzResearch.WordTrace]
  refine ⟨49534414055795908485905863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66045885407727877981207817 49534414055795908485905863)
  ·
    refine ⟨74301621083693862728858795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49534414055795908485905863 74301621083693862728858795)
    ·
      refine ⟨111452431625540794093288193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74301621083693862728858795 111452431625540794093288193)
      ·
        refine ⟨83589323719155595569966145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111452431625540794093288193 83589323719155595569966145)
        ·
          refine ⟨62691992789366696677474609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83589323719155595569966145 62691992789366696677474609)
          ·
            refine ⟨47018994592025022508105957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62691992789366696677474609 47018994592025022508105957)
            ·
              refine ⟨8816061486004691720269867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47018994592025022508105957 8816061486004691720269867)
              ·
                refine ⟨13224092229007037580404801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8816061486004691720269867 13224092229007037580404801)
                ·
                  refine ⟨9918069171755278185303601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13224092229007037580404801 9918069171755278185303601)
                  ·
                    refine ⟨7438551878816458638977701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9918069171755278185303601 7438551878816458638977701)
                    ·
                      refine ⟨1394728477278085994808319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7438551878816458638977701 1394728477278085994808319)
                      ·
                        rfl

theorem cell23_2716224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_2716224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716224 prefixEnd_2716224 := by exact prefixLift 2716224
  have htrace : WordTrace (prefixWord ++ tailWord_2716224) baseStart_2716224 baseEnd_2716224 := by
    simpa [prefixWord, tailWord_2716224, baseEnd_2716224] using wordTrace_append hprefix tailTrace_2716224
  have hstable : (prefixWord ++ tailWord_2716224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716224).length < 2 ^ (prefixWord ++ tailWord_2716224).sum := by decide
  have hdescent : baseEnd_2716224 < baseStart_2716224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716227 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 9]
def baseStart_2716227 : Nat := 118140960795 + 2716227 * 2 ^ 59
def prefixEnd_2716227 : Nat := 4983230072969 + 3 ^ 40 * 2716227 * 2
def baseEnd_2716227 : Nat := 1394730017720049483070805

theorem tailTrace_2716227 : CollatzResearch.WordTrace tailWord_2716227 prefixEnd_2716227 1394730017720049483070805 := by
  unfold tailWord_2716227
  simp only [CollatzResearch.WordTrace]
  refine ⟨99068937530580948484170935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66045958353720632322780623 99068937530580948484170935)
  ·
    refine ⟨148603406295871422726256403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99068937530580948484170935 148603406295871422726256403)
    ·
      refine ⟨222905109443807134089384605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148603406295871422726256403 222905109443807134089384605)
      ·
        refine ⟨83589416041427675283519227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222905109443807134089384605 83589416041427675283519227)
        ·
          refine ⟨125384124062141512925278841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83589416041427675283519227 125384124062141512925278841)
          ·
            refine ⟨94038093046606134693959131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125384124062141512925278841 94038093046606134693959131)
            ·
              refine ⟨141057139569909202040938697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94038093046606134693959131 141057139569909202040938697)
              ·
                refine ⟨105792854677431901530704023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141057139569909202040938697 105792854677431901530704023)
                ·
                  refine ⟨158689282016147852296056035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105792854677431901530704023 158689282016147852296056035)
                  ·
                    refine ⟨238033923024221778444084053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158689282016147852296056035 238033923024221778444084053)
                    ·
                      refine ⟨1394730017720049483070805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 238033923024221778444084053 1394730017720049483070805)
                      ·
                        rfl

theorem cell23_2716227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_2716227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716227 prefixEnd_2716227 := by exact prefixLift 2716227
  have htrace : WordTrace (prefixWord ++ tailWord_2716227) baseStart_2716227 baseEnd_2716227 := by
    simpa [prefixWord, tailWord_2716227, baseEnd_2716227] using wordTrace_append hprefix tailTrace_2716227
  have hstable : (prefixWord ++ tailWord_2716227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716227).length < 2 ^ (prefixWord ++ tailWord_2716227).sum := by decide
  have hdescent : baseEnd_2716227 < baseStart_2716227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716234 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 7]
def baseStart_2716234 : Nat := 118140960795 + 2716234 * 2 ^ 59
def prefixEnd_2716234 : Nat := 4983230072969 + 3 ^ 40 * 2716234 * 2
def baseEnd_2716234 : Nat := 154970401342736772853697

theorem tailTrace_2716234 : CollatzResearch.WordTrace tailWord_2716234 prefixEnd_2716234 154970401342736772853697 := by
  unfold tailWord_2716234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24767298210388897169918939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66046128561037059119783837 24767298210388897169918939)
  ·
    refine ⟨37150947315583345754878409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24767298210388897169918939 37150947315583345754878409)
    ·
      refine ⟨27863210486687509316158807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37150947315583345754878409 27863210486687509316158807)
      ·
        refine ⟨41794815730031263974238211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27863210486687509316158807 41794815730031263974238211)
        ·
          refine ⟨62692223595046895961357317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41794815730031263974238211 62692223595046895961357317)
          ·
            refine ⟨11754791924071292992754497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62692223595046895961357317 11754791924071292992754497)
            ·
              refine ⟨8816093943053469744565873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11754791924071292992754497 8816093943053469744565873)
              ·
                refine ⟨6612070457290102308424405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8816093943053469744565873 6612070457290102308424405)
                ·
                  refine ⟨154970401342736772853697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6612070457290102308424405 154970401342736772853697)
                  ·
                    rfl

theorem cell23_2716234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_2716234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716234 prefixEnd_2716234 := by exact prefixLift 2716234
  have htrace : WordTrace (prefixWord ++ tailWord_2716234) baseStart_2716234 baseEnd_2716234 := by
    simpa [prefixWord, tailWord_2716234, baseEnd_2716234] using wordTrace_append hprefix tailTrace_2716234
  have hstable : (prefixWord ++ tailWord_2716234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716234).length < 2 ^ (prefixWord ++ tailWord_2716234).sum := by decide
  have hdescent : baseEnd_2716234 < baseStart_2716234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716284 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_2716284 : Nat := 118140960795 + 2716284 * 2 ^ 59
def prefixEnd_2716284 : Nat := 4983230072969 + 3 ^ 40 * 2716284 * 2
def baseEnd_2716284 : Nat := 1394759286117355760058043

theorem tailTrace_2716284 : CollatzResearch.WordTrace tailWord_2716284 prefixEnd_2716284 1394759286117355760058043 := by
  unfold tailWord_2716284
  simp only [CollatzResearch.WordTrace]
  refine ⟨49535508245687223609497953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66047344327582964812663937 49535508245687223609497953)
  ·
    refine ⟨37151631184265417707123465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49535508245687223609497953 37151631184265417707123465)
    ·
      refine ⟨27863723388199063280342599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37151631184265417707123465 27863723388199063280342599)
      ·
        refine ⟨41795585082298594920513899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27863723388199063280342599 41795585082298594920513899)
        ·
          refine ⟨62693377623447892380770849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41795585082298594920513899 62693377623447892380770849)
          ·
            refine ⟨47020033217585919285578137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62693377623447892380770849 47020033217585919285578137)
            ·
              refine ⟨35265024913189439464183603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47020033217585919285578137 35265024913189439464183603)
              ·
                refine ⟨52897537369784159196275405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35265024913189439464183603 52897537369784159196275405)
                ·
                  refine ⟨19836576513669059698603277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52897537369784159196275405 19836576513669059698603277)
                  ·
                    refine ⟨7438716192625897386976229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19836576513669059698603277 7438716192625897386976229)
                    ·
                      refine ⟨1394759286117355760058043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7438716192625897386976229 1394759286117355760058043)
                      ·
                        rfl

theorem cell23_2716284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_2716284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716284 prefixEnd_2716284 := by exact prefixLift 2716284
  have htrace : WordTrace (prefixWord ++ tailWord_2716284) baseStart_2716284 baseEnd_2716284 := by
    simpa [prefixWord, tailWord_2716284, baseEnd_2716284] using wordTrace_append hprefix tailTrace_2716284
  have hstable : (prefixWord ++ tailWord_2716284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716284).length < 2 ^ (prefixWord ++ tailWord_2716284).sum := by decide
  have hdescent : baseEnd_2716284 < baseStart_2716284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716298 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_2716298 : Nat := 118140960795 + 2716298 * 2 ^ 59
def prefixEnd_2716298 : Nat := 4983230072969 + 3 ^ 40 * 2716298 * 2
def baseEnd_2716298 : Nat := 464922158282172901760993

theorem tailTrace_2716298 : CollatzResearch.WordTrace tailWord_2716298 prefixEnd_2716298 464922158282172901760993 := by
  unfold tailWord_2716298
  simp only [CollatzResearch.WordTrace]
  refine ⟨24767881778330931902501387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66047684742215818406670365 24767881778330931902501387)
  ·
    refine ⟨37151822667496397853752081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24767881778330931902501387 37151822667496397853752081)
    ·
      refine ⟨27863867000622298390314061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37151822667496397853752081 27863867000622298390314061)
      ·
        refine ⟨10448950125233361896367773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27863867000622298390314061 10448950125233361896367773)
        ·
          refine ⟨3918356296962510711137915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10448950125233361896367773 3918356296962510711137915)
          ·
            refine ⟨5877534445443766066706873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918356296962510711137915 5877534445443766066706873)
            ·
              refine ⟨4408150834082824550030155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5877534445443766066706873 4408150834082824550030155)
              ·
                refine ⟨6612226251124236825045233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408150834082824550030155 6612226251124236825045233)
                ·
                  refine ⟨4959169688343177618783925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6612226251124236825045233 4959169688343177618783925)
                  ·
                    refine ⟨464922158282172901760993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4959169688343177618783925 464922158282172901760993)
                    ·
                      rfl

theorem cell23_2716298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_2716298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716298 prefixEnd_2716298 := by exact prefixLift 2716298
  have htrace : WordTrace (prefixWord ++ tailWord_2716298) baseStart_2716298 baseEnd_2716298 := by
    simpa [prefixWord, tailWord_2716298, baseEnd_2716298] using wordTrace_append hprefix tailTrace_2716298
  have hstable : (prefixWord ++ tailWord_2716298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716298).length < 2 ^ (prefixWord ++ tailWord_2716298).sum := by decide
  have hdescent : baseEnd_2716298 < baseStart_2716298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716318 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2716318 : Nat := 118140960795 + 2716318 * 2 ^ 59
def prefixEnd_2716318 : Nat := 4983230072969 + 3 ^ 40 * 2716318 * 2
def baseEnd_2716318 : Nat := 1394776744459608627032887

theorem tailTrace_2716318 : CollatzResearch.WordTrace tailWord_2716318 prefixEnd_2716318 1394776744459608627032887 := by
  unfold tailWord_2716318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12384032071656408878216701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66048171048834180683822405 12384032071656408878216701)
  ·
    refine ⟨4644012026871153329331263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12384032071656408878216701 4644012026871153329331263)
    ·
      refine ⟨6966018040306729993996895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4644012026871153329331263 6966018040306729993996895)
      ·
        refine ⟨10449027060460094990995343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6966018040306729993996895 10449027060460094990995343)
        ·
          refine ⟨15673540590690142486493015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10449027060460094990995343 15673540590690142486493015)
          ·
            refine ⟨23510310886035213729739523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15673540590690142486493015 23510310886035213729739523)
            ·
              refine ⟨35265466329052820594609285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23510310886035213729739523 35265466329052820594609285)
              ·
                refine ⟨6612274936697403861489241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35265466329052820594609285 6612274936697403861489241)
                ·
                  refine ⟨4959206202523052896116931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6612274936697403861489241 4959206202523052896116931)
                  ·
                    refine ⟨7438809303784579344175397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4959206202523052896116931 7438809303784579344175397)
                    ·
                      refine ⟨1394776744459608627032887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7438809303784579344175397 1394776744459608627032887)
                      ·
                        rfl

theorem cell23_2716318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2716318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716318 prefixEnd_2716318 := by exact prefixLift 2716318
  have htrace : WordTrace (prefixWord ++ tailWord_2716318) baseStart_2716318 baseEnd_2716318 := by
    simpa [prefixWord, tailWord_2716318, baseEnd_2716318] using wordTrace_append hprefix tailTrace_2716318
  have hstable : (prefixWord ++ tailWord_2716318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716318).length < 2 ^ (prefixWord ++ tailWord_2716318).sum := by decide
  have hdescent : baseEnd_2716318 < baseStart_2716318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716378 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2]
def baseStart_2716378 : Nat := 118140960795 + 2716378 * 2 ^ 59
def prefixEnd_2716378 : Nat := 4983230072969 + 3 ^ 40 * 2716378 * 2
def baseEnd_2716378 : Nat := 1394807553298878392282611

theorem tailTrace_2716378 : CollatzResearch.WordTrace tailWord_2716378 prefixEnd_2716378 1394807553298878392282611 := by
  unfold tailWord_2716378
  simp only [CollatzResearch.WordTrace]
  refine ⟨24768611238258475318229447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66049629968689267515278525 24768611238258475318229447)
  ·
    refine ⟨37152916857387712977344171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24768611238258475318229447 37152916857387712977344171)
    ·
      refine ⟨55729375286081569466016257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37152916857387712977344171 55729375286081569466016257)
      ·
        refine ⟨41797031464561177099512193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55729375286081569466016257 41797031464561177099512193)
        ·
          refine ⟨31347773598420882824634145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41797031464561177099512193 31347773598420882824634145)
          ·
            refine ⟨23510830198815662118475609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31347773598420882824634145 23510830198815662118475609)
            ·
              refine ⟨17633122649111746588856707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23510830198815662118475609 17633122649111746588856707)
              ·
                refine ⟨26449683973667619883285061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17633122649111746588856707 26449683973667619883285061)
                ·
                  refine ⟨4959315745062678728115949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26449683973667619883285061 4959315745062678728115949)
                  ·
                    refine ⟨1859743404398504523043481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4959315745062678728115949 1859743404398504523043481)
                    ·
                      refine ⟨1394807553298878392282611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859743404398504523043481 1394807553298878392282611)
                      ·
                        rfl

theorem cell23_2716378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_2716378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716378 prefixEnd_2716378 := by exact prefixLift 2716378
  have htrace : WordTrace (prefixWord ++ tailWord_2716378) baseStart_2716378 baseEnd_2716378 := by
    simpa [prefixWord, tailWord_2716378, baseEnd_2716378] using wordTrace_append hprefix tailTrace_2716378
  have hstable : (prefixWord ++ tailWord_2716378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716378).length < 2 ^ (prefixWord ++ tailWord_2716378).sum := by decide
  have hdescent : baseEnd_2716378 < baseStart_2716378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716385 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_2716385 : Nat := 118140960795 + 2716385 * 2 ^ 59
def prefixEnd_2716385 : Nat := 4983230072969 + 3 ^ 40 * 2716385 * 2
def baseEnd_2716385 : Nat := 1394811147663459864895079

theorem tailTrace_2716385 : CollatzResearch.WordTrace tailWord_2716385 prefixEnd_2716385 1394811147663459864895079 := by
  unfold tailWord_2716385
  simp only [CollatzResearch.WordTrace]
  refine ⟨99074700264008541468422609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66049800176005694312281739 99074700264008541468422609)
  ·
    refine ⟨74306025198006406101316957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99074700264008541468422609 74306025198006406101316957)
    ·
      refine ⟨27864759449252402287993859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74306025198006406101316957 27864759449252402287993859)
      ·
        refine ⟨41797139173878603431990789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27864759449252402287993859 41797139173878603431990789)
        ·
          refine ⟨7836963595102238143498273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41797139173878603431990789 7836963595102238143498273)
          ·
            refine ⟨5877722696326678607623705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7836963595102238143498273 5877722696326678607623705)
            ·
              refine ⟨4408292022245008955717779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5877722696326678607623705 4408292022245008955717779)
              ·
                refine ⟨6612438033367513433576669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408292022245008955717779 6612438033367513433576669)
                ·
                  refine ⟨2479664262512817537591251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6612438033367513433576669 2479664262512817537591251)
                  ·
                    refine ⟨3719496393769226306386877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2479664262512817537591251 3719496393769226306386877)
                    ·
                      refine ⟨1394811147663459864895079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719496393769226306386877 1394811147663459864895079)
                      ·
                        rfl

theorem cell23_2716385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_2716385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716385 prefixEnd_2716385 := by exact prefixLift 2716385
  have htrace : WordTrace (prefixWord ++ tailWord_2716385) baseStart_2716385 baseEnd_2716385 := by
    simpa [prefixWord, tailWord_2716385, baseEnd_2716385] using wordTrace_append hprefix tailTrace_2716385
  have hstable : (prefixWord ++ tailWord_2716385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716385).length < 2 ^ (prefixWord ++ tailWord_2716385).sum := by decide
  have hdescent : baseEnd_2716385 < baseStart_2716385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716408 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 1, 1, 4]
def baseStart_2716408 : Nat := 118140960795 + 2716408 * 2 ^ 59
def prefixEnd_2716408 : Nat := 4983230072969 + 3 ^ 40 * 2716408 * 2
def baseEnd_2716408 : Nat := 1394822957718513274907473

theorem tailTrace_2716408 : CollatzResearch.WordTrace tailWord_2716408 prefixEnd_2716408 1394822957718513274907473 := by
  unfold tailWord_2716408
  simp only [CollatzResearch.WordTrace]
  refine ⟨49537769571462608198254939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66050359428616810931006585 49537769571462608198254939)
  ·
    refine ⟨74306654357193912297382409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49537769571462608198254939 74306654357193912297382409)
    ·
      refine ⟨55729990767895434223036807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74306654357193912297382409 55729990767895434223036807)
      ·
        refine ⟨83594986151843151334555211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55729990767895434223036807 83594986151843151334555211)
        ·
          refine ⟨125392479227764727001832817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83594986151843151334555211 125392479227764727001832817)
          ·
            refine ⟨94044359420823545251374613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125392479227764727001832817 94044359420823545251374613)
            ·
              refine ⟨4408329347851103683658185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94044359420823545251374613 4408329347851103683658185)
              ·
                refine ⟨3306247010888327762743639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408329347851103683658185 3306247010888327762743639)
                ·
                  refine ⟨4959370516332491644115459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306247010888327762743639 4959370516332491644115459)
                  ·
                    refine ⟨7439055774498737466173189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4959370516332491644115459 7439055774498737466173189)
                    ·
                      refine ⟨1394822957718513274907473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7439055774498737466173189 1394822957718513274907473)
                      ·
                        rfl

theorem cell23_2716408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_2716408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716408 prefixEnd_2716408 := by exact prefixLift 2716408
  have htrace : WordTrace (prefixWord ++ tailWord_2716408) baseStart_2716408 baseEnd_2716408 := by
    simpa [prefixWord, tailWord_2716408, baseEnd_2716408] using wordTrace_append hprefix tailTrace_2716408
  have hstable : (prefixWord ++ tailWord_2716408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716408).length < 2 ^ (prefixWord ++ tailWord_2716408).sum := by decide
  have hdescent : baseEnd_2716408 < baseStart_2716408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716411 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 3]
def baseStart_2716411 : Nat := 118140960795 + 2716411 * 2 ^ 59
def prefixEnd_2716411 : Nat := 4983230072969 + 3 ^ 40 * 2716411 * 2
def baseEnd_2716411 : Nat := 1394824498160476763169959

theorem tailTrace_2716411 : CollatzResearch.WordTrace tailWord_2716411 prefixEnd_2716411 1394824498160476763169959 := by
  unfold tailWord_2716411
  simp only [CollatzResearch.WordTrace]
  refine ⟨99075648561914347908869087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66050432374609565272579391 99075648561914347908869087)
  ·
    refine ⟨148613472842871521863303631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99075648561914347908869087 148613472842871521863303631)
    ·
      refine ⟨222920209264307282794955447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148613472842871521863303631 222920209264307282794955447)
      ·
        refine ⟨334380313896460924192433171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222920209264307282794955447 334380313896460924192433171)
        ·
          refine ⟨501570470844691386288649757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334380313896460924192433171 501570470844691386288649757)
          ·
            refine ⟨188088926566759269858243659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 501570470844691386288649757 188088926566759269858243659)
            ·
              refine ⟨282133389850138904787365489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188088926566759269858243659 282133389850138904787365489)
              ·
                refine ⟨211600042387604178590524117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282133389850138904787365489 211600042387604178590524117)
                ·
                  refine ⟨4959375993459472935715409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 211600042387604178590524117 4959375993459472935715409)
                  ·
                    refine ⟨3719531995094604701786557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4959375993459472935715409 3719531995094604701786557)
                    ·
                      refine ⟨1394824498160476763169959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719531995094604701786557 1394824498160476763169959)
                      ·
                        rfl

theorem cell23_2716411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 3].length) (baseStart_2716411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716411 prefixEnd_2716411 := by exact prefixLift 2716411
  have htrace : WordTrace (prefixWord ++ tailWord_2716411) baseStart_2716411 baseEnd_2716411 := by
    simpa [prefixWord, tailWord_2716411, baseEnd_2716411] using wordTrace_append hprefix tailTrace_2716411
  have hstable : (prefixWord ++ tailWord_2716411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716411).length < 2 ^ (prefixWord ++ tailWord_2716411).sum := by decide
  have hdescent : baseEnd_2716411 < baseStart_2716411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716421 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_2716421 : Nat := 118140960795 + 2716421 * 2 ^ 59
def prefixEnd_2716421 : Nat := 4983230072969 + 3 ^ 40 * 2716421 * 2
def baseEnd_2716421 : Nat := 1394829632967021724044913

theorem tailTrace_2716421 : CollatzResearch.WordTrace tailWord_2716421 prefixEnd_2716421 1394829632967021724044913 := by
  unfold tailWord_2716421
  simp only [CollatzResearch.WordTrace]
  refine ⟨99076013291878119616733117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66050675527918746411155411 99076013291878119616733117)
  ·
    refine ⟨37153504984454294856274919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99076013291878119616733117 37153504984454294856274919)
    ·
      refine ⟨55730257476681442284412379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37153504984454294856274919 55730257476681442284412379)
      ·
        refine ⟨83595386215022163426618569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55730257476681442284412379 83595386215022163426618569)
        ·
          refine ⟨62696539661266622569963927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83595386215022163426618569 62696539661266622569963927)
          ·
            refine ⟨94044809491899933854945891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62696539661266622569963927 94044809491899933854945891)
            ·
              refine ⟨141067214237849900782418837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94044809491899933854945891 141067214237849900782418837)
              ·
                refine ⟨6612525667399214099175883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141067214237849900782418837 6612525667399214099175883)
                ·
                  refine ⟨9918788501098821148763825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6612525667399214099175883 9918788501098821148763825)
                  ·
                    refine ⟨7439091375824115861572869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9918788501098821148763825 7439091375824115861572869)
                    ·
                      refine ⟨1394829632967021724044913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7439091375824115861572869 1394829632967021724044913)
                      ·
                        rfl

theorem cell23_2716421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_2716421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716421 prefixEnd_2716421 := by exact prefixLift 2716421
  have htrace : WordTrace (prefixWord ++ tailWord_2716421) baseStart_2716421 baseEnd_2716421 := by
    simpa [prefixWord, tailWord_2716421, baseEnd_2716421] using wordTrace_append hprefix tailTrace_2716421
  have hstable : (prefixWord ++ tailWord_2716421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716421).length < 2 ^ (prefixWord ++ tailWord_2716421).sum := by decide
  have hdescent : baseEnd_2716421 < baseStart_2716421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716441 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 5, 3, 3]
def baseStart_2716441 : Nat := 118140960795 + 2716441 * 2 ^ 59
def prefixEnd_2716441 : Nat := 4983230072969 + 3 ^ 40 * 2716441 * 2
def baseEnd_2716441 : Nat := 1394839902580111645794821

theorem tailTrace_2716441 : CollatzResearch.WordTrace tailWord_2716441 prefixEnd_2716441 1394839902580111645794821 := by
  unfold tailWord_2716441
  simp only [CollatzResearch.WordTrace]
  refine ⟨99076742751805663032461177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66051161834537108688307451 99076742751805663032461177)
  ·
    refine ⟨74307557063854247274345883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99076742751805663032461177 74307557063854247274345883)
    ·
      refine ⟨111461335595781370911518825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74307557063854247274345883 111461335595781370911518825)
      ·
        refine ⟨83596001696836028183639119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111461335595781370911518825 83596001696836028183639119)
        ·
          refine ⟨125394002545254042275458679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83596001696836028183639119 125394002545254042275458679)
          ·
            refine ⟨188091003817881063413188019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125394002545254042275458679 188091003817881063413188019)
            ·
              refine ⟨282136505726821595119782029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188091003817881063413188019 282136505726821595119782029)
              ·
                refine ⟨105801189647558098169918261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282136505726821595119782029 105801189647558098169918261)
                ·
                  refine ⟨9918861529458571703429837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105801189647558098169918261 9918861529458571703429837)
                  ·
                    refine ⟨3719573073546964388786189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9918861529458571703429837 3719573073546964388786189)
                    ·
                      refine ⟨1394839902580111645794821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719573073546964388786189 1394839902580111645794821)
                      ·
                        rfl

theorem cell23_2716441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_2716441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716441 prefixEnd_2716441 := by exact prefixLift 2716441
  have htrace : WordTrace (prefixWord ++ tailWord_2716441) baseStart_2716441 baseEnd_2716441 := by
    simpa [prefixWord, tailWord_2716441, baseEnd_2716441] using wordTrace_append hprefix tailTrace_2716441
  have hstable : (prefixWord ++ tailWord_2716441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716441).length < 2 ^ (prefixWord ++ tailWord_2716441).sum := by decide
  have hdescent : baseEnd_2716441 < baseStart_2716441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716462 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2716462 : Nat := 118140960795 + 2716462 * 2 ^ 59
def prefixEnd_2716462 : Nat := 4983230072969 + 3 ^ 40 * 2716462 * 2
def baseEnd_2716462 : Nat := 1394850685673856063632225

theorem tailTrace_2716462 : CollatzResearch.WordTrace tailWord_2716462 prefixEnd_2716462 1394850685673856063632225 := by
  unfold tailWord_2716462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12384688585591197952371955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66051672456486389079317093 12384688585591197952371955)
  ·
    refine ⟨18577032878386796928557933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12384688585591197952371955 18577032878386796928557933)
    ·
      refine ⟨6966387329395048848209225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18577032878386796928557933 6966387329395048848209225)
      ·
        refine ⟨5224790497046286636156919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6966387329395048848209225 5224790497046286636156919)
        ·
          refine ⟨7837185745569429954235379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5224790497046286636156919 7837185745569429954235379)
          ·
            refine ⟨11755778618354144931353069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837185745569429954235379 11755778618354144931353069)
            ·
              refine ⟨4408416981882804349257401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11755778618354144931353069 4408416981882804349257401)
              ·
                refine ⟨3306312736412103261943051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408416981882804349257401 3306312736412103261943051)
                ·
                  refine ⟨4959469104618154892914577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306312736412103261943051 4959469104618154892914577)
                  ·
                    refine ⟨3719601828463616169685933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4959469104618154892914577 3719601828463616169685933)
                    ·
                      refine ⟨1394850685673856063632225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719601828463616169685933 1394850685673856063632225)
                      ·
                        rfl

theorem cell23_2716462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2716462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716462 prefixEnd_2716462 := by exact prefixLift 2716462
  have htrace : WordTrace (prefixWord ++ tailWord_2716462) baseStart_2716462 baseEnd_2716462 := by
    simpa [prefixWord, tailWord_2716462, baseEnd_2716462] using wordTrace_append hprefix tailTrace_2716462
  have hstable : (prefixWord ++ tailWord_2716462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716462).length < 2 ^ (prefixWord ++ tailWord_2716462).sum := by decide
  have hdescent : baseEnd_2716462 < baseStart_2716462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716492 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2716492 : Nat := 118140960795 + 2716492 * 2 ^ 59
def prefixEnd_2716492 : Nat := 4983230072969 + 3 ^ 40 * 2716492 * 2
def baseEnd_2716492 : Nat := 1394866090093490946257087

theorem tailTrace_2716492 : CollatzResearch.WordTrace tailWord_2716492 prefixEnd_2716492 1394866090093490946257087 := by
  unfold tailWord_2716492
  simp only [CollatzResearch.WordTrace]
  refine ⟨49539301437310449371283865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66052401916413932495045153 49539301437310449371283865)
  ·
    refine ⟨37154476077982837028462899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49539301437310449371283865 37154476077982837028462899)
    ·
      refine ⟨55731714116974255542694349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37154476077982837028462899 55731714116974255542694349)
      ·
        refine ⟨20899392793865345828510381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55731714116974255542694349 20899392793865345828510381)
        ·
          refine ⟨7837272297699504685691393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20899392793865345828510381 7837272297699504685691393)
          ·
            refine ⟨5877954223274628514268545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7837272297699504685691393 5877954223274628514268545)
            ·
              refine ⟨4408465667455971385701409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5877954223274628514268545 4408465667455971385701409)
              ·
                refine ⟨3306349250591978539276057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408465667455971385701409 3306349250591978539276057)
                ·
                  refine ⟨2479761937943983904457043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3306349250591978539276057 2479761937943983904457043)
                  ·
                    refine ⟨3719642906915975856685565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2479761937943983904457043 3719642906915975856685565)
                    ·
                      refine ⟨1394866090093490946257087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719642906915975856685565 1394866090093490946257087)
                      ·
                        rfl

theorem cell23_2716492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2716492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716492 prefixEnd_2716492 := by exact prefixLift 2716492
  have htrace : WordTrace (prefixWord ++ tailWord_2716492) baseStart_2716492 baseEnd_2716492 := by
    simpa [prefixWord, tailWord_2716492, baseEnd_2716492] using wordTrace_append hprefix tailTrace_2716492
  have hstable : (prefixWord ++ tailWord_2716492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716492).length < 2 ^ (prefixWord ++ tailWord_2716492).sum := by decide
  have hdescent : baseEnd_2716492 < baseStart_2716492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716508 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2716508 : Nat := 118140960795 + 2716508 * 2 ^ 59
def prefixEnd_2716508 : Nat := 4983230072969 + 3 ^ 40 * 2716508 * 2
def baseEnd_2716508 : Nat := 464958101927987627885671

theorem tailTrace_2716508 : CollatzResearch.WordTrace tailWord_2716508 prefixEnd_2716508 464958101927987627885671 := by
  unfold tailWord_2716508
  simp only [CollatzResearch.WordTrace]
  refine ⟨49539593221281466737575089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66052790961708622316766785 49539593221281466737575089)
  ·
    refine ⟨37154694915961100053181317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49539593221281466737575089 37154694915961100053181317)
    ·
      refine ⟨6966505296742706259971497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37154694915961100053181317 6966505296742706259971497)
      ·
        refine ⟨5224878972557029694978623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6966505296742706259971497 5224878972557029694978623)
        ·
          refine ⟨7837318458835544542467935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5224878972557029694978623 7837318458835544542467935)
          ·
            refine ⟨11755977688253316813701903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837318458835544542467935 11755977688253316813701903)
            ·
              refine ⟨17633966532379975220552855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11755977688253316813701903 17633966532379975220552855)
              ·
                refine ⟨26450949798569962830829283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17633966532379975220552855 26450949798569962830829283)
                ·
                  refine ⟨39676424697854944246243925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26450949798569962830829283 39676424697854944246243925)
                  ·
                    refine ⟨464958101927987627885671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39676424697854944246243925 464958101927987627885671)
                    ·
                      rfl

theorem cell23_2716508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2716508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716508 prefixEnd_2716508 := by exact prefixLift 2716508
  have htrace : WordTrace (prefixWord ++ tailWord_2716508) baseStart_2716508 baseEnd_2716508 := by
    simpa [prefixWord, tailWord_2716508, baseEnd_2716508] using wordTrace_append hprefix tailTrace_2716508
  have hstable : (prefixWord ++ tailWord_2716508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716508).length < 2 ^ (prefixWord ++ tailWord_2716508).sum := by decide
  have hdescent : baseEnd_2716508 < baseStart_2716508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716515 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 1, 4, 2]
def baseStart_2716515 : Nat := 118140960795 + 2716515 * 2 ^ 59
def prefixEnd_2716515 : Nat := 4983230072969 + 3 ^ 40 * 2716515 * 2
def baseEnd_2716515 : Nat := 1394877900148544356269481

theorem tailTrace_2716515 : CollatzResearch.WordTrace tailWord_2716515 prefixEnd_2716515 1394877900148544356269481 := by
  unfold tailWord_2716515
  simp only [CollatzResearch.WordTrace]
  refine ⟨99079441753537573670654999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66052961169025049113769999 99079441753537573670654999)
  ·
    refine ⟨148619162630306360505982499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99079441753537573670654999 148619162630306360505982499)
    ·
      refine ⟨222928743945459540758973749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148619162630306360505982499 222928743945459540758973749)
      ·
        refine ⟨20899569744886831946153789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222928743945459540758973749 20899569744886831946153789)
        ·
          refine ⟨7837338654332561979807671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20899569744886831946153789 7837338654332561979807671)
          ·
            refine ⟨11756007981498842969711507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837338654332561979807671 11756007981498842969711507)
            ·
              refine ⟨17634011972248264454567261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11756007981498842969711507 17634011972248264454567261)
              ·
                refine ⟨6612754489593099170462723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17634011972248264454567261 6612754489593099170462723)
                ·
                  refine ⟨9919131734389648755694085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6612754489593099170462723 9919131734389648755694085)
                  ·
                    refine ⟨1859837200198059141692641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9919131734389648755694085 1859837200198059141692641)
                    ·
                      refine ⟨1394877900148544356269481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859837200198059141692641 1394877900148544356269481)
                      ·
                        rfl

theorem cell23_2716515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_2716515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716515 prefixEnd_2716515 := by exact prefixLift 2716515
  have htrace : WordTrace (prefixWord ++ tailWord_2716515) baseStart_2716515 baseEnd_2716515 := by
    simpa [prefixWord, tailWord_2716515, baseEnd_2716515] using wordTrace_append hprefix tailTrace_2716515
  have hstable : (prefixWord ++ tailWord_2716515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716515).length < 2 ^ (prefixWord ++ tailWord_2716515).sum := by decide
  have hdescent : baseEnd_2716515 < baseStart_2716515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716549 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 2, 2, 2]
def baseStart_2716549 : Nat := 118140960795 + 2716549 * 2 ^ 59
def prefixEnd_2716549 : Nat := 4983230072969 + 3 ^ 40 * 2716549 * 2
def baseEnd_2716549 : Nat := 1394895358490797223244325

theorem tailTrace_2716549 : CollatzResearch.WordTrace tailWord_2716549 prefixEnd_2716549 1394895358490797223244325 := by
  unfold tailWord_2716549
  simp only [CollatzResearch.WordTrace]
  refine ⟨99080681835414397477392701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66053787890276264984928467 99080681835414397477392701)
  ·
    refine ⟨37155255688280399054022263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99080681835414397477392701 37155255688280399054022263)
    ·
      refine ⟨55732883532420598581033395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37155255688280399054022263 55732883532420598581033395)
      ·
        refine ⟨83599325298630897871550093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55732883532420598581033395 83599325298630897871550093)
        ·
          refine ⟨31349746986986586701831285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83599325298630897871550093 31349746986986586701831285)
          ·
            refine ⟨2939038780029992503296683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31349746986986586701831285 2939038780029992503296683)
            ·
              refine ⟨4408558170044988754945025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2939038780029992503296683 4408558170044988754945025)
              ·
                refine ⟨3306418627533741566208769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408558170044988754945025 3306418627533741566208769)
                ·
                  refine ⟨2479813970650306174656577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3306418627533741566208769 2479813970650306174656577)
                  ·
                    refine ⟨1859860477987729630992433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2479813970650306174656577 1859860477987729630992433)
                    ·
                      refine ⟨1394895358490797223244325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859860477987729630992433 1394895358490797223244325)
                      ·
                        rfl

theorem cell23_2716549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_2716549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716549 prefixEnd_2716549 := by exact prefixLift 2716549
  have htrace : WordTrace (prefixWord ++ tailWord_2716549) baseStart_2716549 baseEnd_2716549 := by
    simpa [prefixWord, tailWord_2716549, baseEnd_2716549] using wordTrace_append hprefix tailTrace_2716549
  have hstable : (prefixWord ++ tailWord_2716549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716549).length < 2 ^ (prefixWord ++ tailWord_2716549).sum := by decide
  have hdescent : baseEnd_2716549 < baseStart_2716549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716561 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_2716561 : Nat := 118140960795 + 2716561 * 2 ^ 59
def prefixEnd_2716561 : Nat := 4983230072969 + 3 ^ 40 * 2716561 * 2
def baseEnd_2716561 : Nat := 1394901520258651176294269

theorem tailTrace_2716561 : CollatzResearch.WordTrace tailWord_2716561 prefixEnd_2716561 1394901520258651176294269 := by
  unfold tailWord_2716561
  simp only [CollatzResearch.WordTrace]
  refine ⟨99081119511370923526829537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66054079674247282351219691 99081119511370923526829537)
  ·
    refine ⟨74310839633528192645122153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99081119511370923526829537 74310839633528192645122153)
    ·
      refine ⟨55733129725146144483841615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74310839633528192645122153 55733129725146144483841615)
      ·
        refine ⟨83599694587719216725762423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55733129725146144483841615 83599694587719216725762423)
        ·
          refine ⟨125399541881578825088643635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83599694587719216725762423 125399541881578825088643635)
          ·
            refine ⟨188099312822368237632965453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125399541881578825088643635 188099312822368237632965453)
            ·
              refine ⟨70537242308388089112362045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188099312822368237632965453 70537242308388089112362045)
              ·
                refine ⟨26451465865645533417135767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70537242308388089112362045 26451465865645533417135767)
                ·
                  refine ⟨39677198798468300125703651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26451465865645533417135767 39677198798468300125703651)
                  ·
                    refine ⟨59515798197702450188555477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39677198798468300125703651 59515798197702450188555477)
                    ·
                      refine ⟨1394901520258651176294269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59515798197702450188555477 1394901520258651176294269)
                      ·
                        rfl

theorem cell23_2716561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_2716561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716561 prefixEnd_2716561 := by exact prefixLift 2716561
  have htrace : WordTrace (prefixWord ++ tailWord_2716561) baseStart_2716561 baseEnd_2716561 := by
    simpa [prefixWord, tailWord_2716561, baseEnd_2716561] using wordTrace_append hprefix tailTrace_2716561
  have hstable : (prefixWord ++ tailWord_2716561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716561).length < 2 ^ (prefixWord ++ tailWord_2716561).sum := by decide
  have hdescent : baseEnd_2716561 < baseStart_2716561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716566 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2716566 : Nat := 118140960795 + 2716566 * 2 ^ 59
def prefixEnd_2716566 : Nat := 4983230072969 + 3 ^ 40 * 2716566 * 2
def baseEnd_2716566 : Nat := 1394904087661923656731747

theorem tailTrace_2716566 : CollatzResearch.WordTrace tailWord_2716566 prefixEnd_2716566 1394904087661923656731747 := by
  unfold tailWord_2716566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6192581367272050586297597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66054201250901872920507701 6192581367272050586297597)
  ·
    refine ⟨2322218012727018969861599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6192581367272050586297597 2322218012727018969861599)
    ·
      refine ⟨3483327019090528454792399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2322218012727018969861599 3483327019090528454792399)
      ·
        refine ⟨5224990528635792682188599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3483327019090528454792399 5224990528635792682188599)
        ·
          refine ⟨7837485792953689023282899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5224990528635792682188599 7837485792953689023282899)
          ·
            refine ⟨11756228689430533534924349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837485792953689023282899 11756228689430533534924349)
            ·
              refine ⟨4408585758536450075596631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11756228689430533534924349 4408585758536450075596631)
              ·
                refine ⟨6612878637804675113394947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408585758536450075596631 6612878637804675113394947)
                ·
                  refine ⟨9919317956707012670092421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6612878637804675113394947 9919317956707012670092421)
                  ·
                    refine ⟨1859872116882564875642329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9919317956707012670092421 1859872116882564875642329)
                    ·
                      refine ⟨1394904087661923656731747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859872116882564875642329 1394904087661923656731747)
                      ·
                        rfl

theorem cell23_2716566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2716566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716566 prefixEnd_2716566 := by exact prefixLift 2716566
  have htrace : WordTrace (prefixWord ++ tailWord_2716566) baseStart_2716566 baseEnd_2716566 := by
    simpa [prefixWord, tailWord_2716566, baseEnd_2716566] using wordTrace_append hprefix tailTrace_2716566
  have hstable : (prefixWord ++ tailWord_2716566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716566).length < 2 ^ (prefixWord ++ tailWord_2716566).sum := by decide
  have hdescent : baseEnd_2716566 < baseStart_2716566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716612 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2716612 : Nat := 118140960795 + 2716612 * 2 ^ 59
def prefixEnd_2716612 : Nat := 4983230072969 + 3 ^ 40 * 2716612 * 2
def baseEnd_2716612 : Nat := 1394927707772030476756535

theorem tailTrace_2716612 : CollatzResearch.WordTrace tailWord_2716612 prefixEnd_2716612 1394927707772030476756535 := by
  unfold tailWord_2716612
  simp only [CollatzResearch.WordTrace]
  refine ⟨49541489817093079618468045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66055319756124106157957393 49541489817093079618468045)
  ·
    refine ⟨18578058681409904856925517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49541489817093079618468045 18578058681409904856925517)
    ·
      refine ⟨6966772005528714321347069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18578058681409904856925517 6966772005528714321347069)
      ·
        refine ⟨2612539502073267870505151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6966772005528714321347069 2612539502073267870505151)
        ·
          refine ⟨3918809253109901805757727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2612539502073267870505151 3918809253109901805757727)
          ·
            refine ⟨5878213879664852708636591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918809253109901805757727 5878213879664852708636591)
            ·
              refine ⟨8817320819497279062954887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5878213879664852708636591 8817320819497279062954887)
              ·
                refine ⟨13225981229245918594432331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8817320819497279062954887 13225981229245918594432331)
                ·
                  refine ⟨19838971843868877891648497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13225981229245918594432331 19838971843868877891648497)
                  ·
                    refine ⟨14879228882901658418736373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19838971843868877891648497 14879228882901658418736373)
                    ·
                      refine ⟨1394927707772030476756535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14879228882901658418736373 1394927707772030476756535)
                      ·
                        rfl

theorem cell23_2716612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2716612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716612 prefixEnd_2716612 := by exact prefixLift 2716612
  have htrace : WordTrace (prefixWord ++ tailWord_2716612) baseStart_2716612 baseEnd_2716612 := by
    simpa [prefixWord, tailWord_2716612, baseEnd_2716612] using wordTrace_append hprefix tailTrace_2716612
  have hstable : (prefixWord ++ tailWord_2716612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716612).length < 2 ^ (prefixWord ++ tailWord_2716612).sum := by decide
  have hdescent : baseEnd_2716612 < baseStart_2716612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716615 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 3, 4]
def baseStart_2716615 : Nat := 118140960795 + 2716615 * 2 ^ 59
def prefixEnd_2716615 : Nat := 4983230072969 + 3 ^ 40 * 2716615 * 2
def baseEnd_2716615 : Nat := 464976416071331321673007

theorem tailTrace_2716615 : CollatzResearch.WordTrace tailWord_2716615 prefixEnd_2716615 464976416071331321673007 := by
  unfold tailWord_2716615
  simp only [CollatzResearch.WordTrace]
  refine ⟨99083089053175290749295299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66055392702116860499530199 99083089053175290749295299)
  ·
    refine ⟨148624633579762936123942949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99083089053175290749295299 148624633579762936123942949)
    ·
      refine ⟨27867118796205550523239303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148624633579762936123942949 27867118796205550523239303)
      ·
        refine ⟨41800678194308325784858955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27867118796205550523239303 41800678194308325784858955)
        ·
          refine ⟨62701017291462488677288433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41800678194308325784858955 62701017291462488677288433)
          ·
            refine ⟨47025762968596866507966325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62701017291462488677288433 47025762968596866507966325)
            ·
              refine ⟨4408665278305956235121843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47025762968596866507966325 4408665278305956235121843)
              ·
                refine ⟨6612997917458934352682765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408665278305956235121843 6612997917458934352682765)
                ·
                  refine ⟨2479874219047100382256037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6612997917458934352682765 2479874219047100382256037)
                  ·
                    refine ⟨464976416071331321673007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2479874219047100382256037 464976416071331321673007)
                    ·
                      rfl

theorem cell23_2716615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_2716615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716615 prefixEnd_2716615 := by exact prefixLift 2716615
  have htrace : WordTrace (prefixWord ++ tailWord_2716615) baseStart_2716615 baseEnd_2716615 := by
    simpa [prefixWord, tailWord_2716615, baseEnd_2716615] using wordTrace_append hprefix tailTrace_2716615
  have hstable : (prefixWord ++ tailWord_2716615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716615).length < 2 ^ (prefixWord ++ tailWord_2716615).sum := by decide
  have hdescent : baseEnd_2716615 < baseStart_2716615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716662 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_2716662 : Nat := 118140960795 + 2716662 * 2 ^ 59
def prefixEnd_2716662 : Nat := 4983230072969 + 3 ^ 40 * 2716662 * 2
def baseEnd_2716662 : Nat := 154994820200528364570145

theorem tailTrace_2716662 : CollatzResearch.WordTrace tailWord_2716662 prefixEnd_2716662 154994820200528364570145 := by
  unfold tailWord_2716662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6192800205250313611016015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66056535522670011850837493 6192800205250313611016015)
  ·
    refine ⟨9289200307875470416524023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6192800205250313611016015 9289200307875470416524023)
    ·
      refine ⟨13933800461813205624786035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9289200307875470416524023 13933800461813205624786035)
      ·
        refine ⟨20900700692719808437179053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13933800461813205624786035 20900700692719808437179053)
        ·
          refine ⟨7837762759769928163942145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20900700692719808437179053 7837762759769928163942145)
          ·
            refine ⟨5878322069827446122956609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7837762759769928163942145 5878322069827446122956609)
            ·
              refine ⟨4408741552370584592217457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5878322069827446122956609 4408741552370584592217457)
              ·
                refine ⟨3306556164277938444163093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408741552370584592217457 3306556164277938444163093)
                ·
                  refine ⟨154994820200528364570145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3306556164277938444163093 154994820200528364570145)
                  ·
                    rfl

theorem cell23_2716662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_2716662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716662 prefixEnd_2716662 := by exact prefixLift 2716662
  have htrace : WordTrace (prefixWord ++ tailWord_2716662) baseStart_2716662 baseEnd_2716662 := by
    simpa [prefixWord, tailWord_2716662, baseEnd_2716662] using wordTrace_append hprefix tailTrace_2716662
  have hstable : (prefixWord ++ tailWord_2716662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716662).length < 2 ^ (prefixWord ++ tailWord_2716662).sum := by decide
  have hdescent : baseEnd_2716662 < baseStart_2716662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716705 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 1, 6]
def baseStart_2716705 : Nat := 118140960795 + 2716705 * 2 ^ 59
def prefixEnd_2716705 : Nat := 4983230072969 + 3 ^ 40 * 2716705 * 2
def baseEnd_2716705 : Nat := 464991820490966204297869

theorem tailTrace_2716705 : CollatzResearch.WordTrace tailWord_2716705 prefixEnd_2716705 464991820490966204297869 := by
  unfold tailWord_2716705
  simp only [CollatzResearch.WordTrace]
  refine ⟨99086371622849236120071569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66057581081899490746714379 99086371622849236120071569)
  ·
    refine ⟨74314778717136927090053677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99086371622849236120071569 74314778717136927090053677)
    ·
      refine ⟨27868042018926347658770129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74314778717136927090053677 27868042018926347658770129)
      ·
        refine ⟨20901031514194760744077597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27868042018926347658770129 20901031514194760744077597)
        ·
          refine ⟨7837886817823035279029099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20901031514194760744077597 7837886817823035279029099)
          ·
            refine ⟨11756830226734552918543649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837886817823035279029099 11756830226734552918543649)
            ·
              refine ⟨8817622670050914688907737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11756830226734552918543649 8817622670050914688907737)
              ·
                refine ⟨6613217002538186016680803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8817622670050914688907737 6613217002538186016680803)
                ·
                  refine ⟨9919825503807279025021205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6613217002538186016680803 9919825503807279025021205)
                  ·
                    refine ⟨464991820490966204297869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9919825503807279025021205 464991820490966204297869)
                    ·
                      rfl

theorem cell23_2716705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_2716705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716705 prefixEnd_2716705 := by exact prefixLift 2716705
  have htrace : WordTrace (prefixWord ++ tailWord_2716705) baseStart_2716705 baseEnd_2716705 := by
    simpa [prefixWord, tailWord_2716705, baseEnd_2716705] using wordTrace_append hprefix tailTrace_2716705
  have hstable : (prefixWord ++ tailWord_2716705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716705).length < 2 ^ (prefixWord ++ tailWord_2716705).sum := by decide
  have hdescent : baseEnd_2716705 < baseStart_2716705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716706 : List Nat := [3, 3, 1, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_2716706 : Nat := 118140960795 + 2716706 * 2 ^ 59
def prefixEnd_2716706 : Nat := 4983230072969 + 3 ^ 40 * 2716706 * 2
def baseEnd_2716706 : Nat := 1394975974953553108981103

theorem tailTrace_2716706 : CollatzResearch.WordTrace tailWord_2716706 prefixEnd_2716706 1394975974953553108981103 := by
  unfold tailWord_2716706
  simp only [CollatzResearch.WordTrace]
  refine ⟨24771602023961403322714493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66057605397230408860571981 24771602023961403322714493)
  ·
    refine ⟨9289350758985526246017935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24771602023961403322714493 9289350758985526246017935)
    ·
      refine ⟨13934026138478289369026903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9289350758985526246017935 13934026138478289369026903)
      ·
        refine ⟨20901039207717434053540355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13934026138478289369026903 20901039207717434053540355)
        ·
          refine ⟨31351558811576151080310533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20901039207717434053540355 31351558811576151080310533)
          ·
            refine ⟨5878417277170528327558225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31351558811576151080310533 5878417277170528327558225)
            ·
              refine ⟨4408812957877896245668669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5878417277170528327558225 4408812957877896245668669)
              ·
                refine ⟨1653304859204211092125751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4408812957877896245668669 1653304859204211092125751)
                ·
                  refine ⟨2479957288806316638188627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653304859204211092125751 2479957288806316638188627)
                  ·
                    refine ⟨3719935933209474957282941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2479957288806316638188627 3719935933209474957282941)
                    ·
                      refine ⟨1394975974953553108981103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719935933209474957282941 1394975974953553108981103)
                      ·
                        rfl

theorem cell23_2716706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_2716706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716706 prefixEnd_2716706 := by exact prefixLift 2716706
  have htrace : WordTrace (prefixWord ++ tailWord_2716706) baseStart_2716706 baseEnd_2716706 := by
    simpa [prefixWord, tailWord_2716706, baseEnd_2716706] using wordTrace_append hprefix tailTrace_2716706
  have hstable : (prefixWord ++ tailWord_2716706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716706).length < 2 ^ (prefixWord ++ tailWord_2716706).sum := by decide
  have hdescent : baseEnd_2716706 < baseStart_2716706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716729 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 3, 2, 2]
def baseStart_2716729 : Nat := 118140960795 + 2716729 * 2 ^ 59
def prefixEnd_2716729 : Nat := 4983230072969 + 3 ^ 40 * 2716729 * 2
def baseEnd_2716729 : Nat := 1394987785008606518993497

theorem tailTrace_2716729 : CollatzResearch.WordTrace tailWord_2716729 prefixEnd_2716729 1394987785008606518993497 := by
  unfold tailWord_2716729
  simp only [CollatzResearch.WordTrace]
  refine ⟨99087246974762288218945241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66058164649841525479296827 99087246974762288218945241)
  ·
    refine ⟨74315435231071716164208931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99087246974762288218945241 74315435231071716164208931)
    ·
      refine ⟨111473152846607574246313397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74315435231071716164208931 111473152846607574246313397)
      ·
        refine ⟨10450608079369460085591881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111473152846607574246313397 10450608079369460085591881)
        ·
          refine ⟨7837956059527095064193911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10450608079369460085591881 7837956059527095064193911)
          ·
            refine ⟨11756934089290642596290867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837956059527095064193911 11756934089290642596290867)
            ·
              refine ⟨17635401133935963894436301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11756934089290642596290867 17635401133935963894436301)
              ·
                refine ⟨6613275425225986460413613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17635401133935963894436301 6613275425225986460413613)
                ·
                  refine ⟨2479978284459744922655105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6613275425225986460413613 2479978284459744922655105)
                  ·
                    refine ⟨1859983713344808691991329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2479978284459744922655105 1859983713344808691991329)
                    ·
                      refine ⟨1394987785008606518993497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1859983713344808691991329 1394987785008606518993497)
                      ·
                        rfl

theorem cell23_2716729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_2716729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716729 prefixEnd_2716729 := by exact prefixLift 2716729
  have htrace : WordTrace (prefixWord ++ tailWord_2716729) baseStart_2716729 baseEnd_2716729 := by
    simpa [prefixWord, tailWord_2716729, baseEnd_2716729] using wordTrace_append hprefix tailTrace_2716729
  have hstable : (prefixWord ++ tailWord_2716729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716729).length < 2 ^ (prefixWord ++ tailWord_2716729).sum := by decide
  have hdescent : baseEnd_2716729 < baseStart_2716729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716745 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 1, 3, 3]
def baseStart_2716745 : Nat := 118140960795 + 2716745 * 2 ^ 59
def prefixEnd_2716745 : Nat := 4983230072969 + 3 ^ 40 * 2716745 * 2
def baseEnd_2716745 : Nat := 1394996000699078456393423

theorem tailTrace_2716745 : CollatzResearch.WordTrace tailWord_2716745 prefixEnd_2716745 1394996000699078456393423 := by
  unfold tailWord_2716745
  simp only [CollatzResearch.WordTrace]
  refine ⟨99087830542704322951527689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66058553695136215301018459 99087830542704322951527689)
  ·
    refine ⟨74315872907028242213645767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99087830542704322951527689 74315872907028242213645767)
    ·
      refine ⟨111473809360542363320468651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74315872907028242213645767 111473809360542363320468651)
      ·
        refine ⟨167210714040813544980702977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111473809360542363320468651 167210714040813544980702977)
        ·
          refine ⟨125408035530610158735527233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167210714040813544980702977 125408035530610158735527233)
          ·
            refine ⟨94056026647957619051645425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125408035530610158735527233 94056026647957619051645425)
            ·
              refine ⟨70542019985968214288734069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94056026647957619051645425 70542019985968214288734069)
              ·
                refine ⟨6613314373684520089568819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70542019985968214288734069 6613314373684520089568819)
                ·
                  refine ⟨9919971560526780134353229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6613314373684520089568819 9919971560526780134353229)
                  ·
                    refine ⟨3719989335197542550382461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9919971560526780134353229 3719989335197542550382461)
                    ·
                      refine ⟨1394996000699078456393423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719989335197542550382461 1394996000699078456393423)
                      ·
                        rfl

theorem cell23_2716745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3, 3].length) (baseStart_2716745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716745 prefixEnd_2716745 := by exact prefixLift 2716745
  have htrace : WordTrace (prefixWord ++ tailWord_2716745) baseStart_2716745 baseEnd_2716745 := by
    simpa [prefixWord, tailWord_2716745, baseEnd_2716745] using wordTrace_append hprefix tailTrace_2716745
  have hstable : (prefixWord ++ tailWord_2716745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716745).length < 2 ^ (prefixWord ++ tailWord_2716745).sum := by decide
  have hdescent : baseEnd_2716745 < baseStart_2716745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716749 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_2716749 : Nat := 118140960795 + 2716749 * 2 ^ 59
def prefixEnd_2716749 : Nat := 4983230072969 + 3 ^ 40 * 2716749 * 2
def baseEnd_2716749 : Nat := 1394998054621696440743405

theorem tailTrace_2716749 : CollatzResearch.WordTrace tailWord_2716749 prefixEnd_2716749 1394998054621696440743405 := by
  unfold tailWord_2716749
  simp only [CollatzResearch.WordTrace]
  refine ⟨99087976434689831634673301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66058650956459887756448867 99087976434689831634673301)
  ·
    refine ⟨4644748895376085857875311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99087976434689831634673301 4644748895376085857875311)
    ·
      refine ⟨6967123343064128786812967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4644748895376085857875311 6967123343064128786812967)
      ·
        refine ⟨10450685014596193180219451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6967123343064128786812967 10450685014596193180219451)
        ·
          refine ⟨15676027521894289770329177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10450685014596193180219451 15676027521894289770329177)
          ·
            refine ⟨11757020641420717327746883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15676027521894289770329177 11757020641420717327746883)
            ·
              refine ⟨17635530962131075991620325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11757020641420717327746883 17635530962131075991620325)
              ·
                refine ⟨3306662055399576748428811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17635530962131075991620325 3306662055399576748428811)
                ·
                  refine ⟨4959993083099365122643217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306662055399576748428811 4959993083099365122643217)
                  ·
                    refine ⟨3719994812324523841982413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4959993083099365122643217 3719994812324523841982413)
                    ·
                      refine ⟨1394998054621696440743405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3719994812324523841982413 1394998054621696440743405)
                      ·
                        rfl

theorem cell23_2716749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_2716749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716749 prefixEnd_2716749 := by exact prefixLift 2716749
  have htrace : WordTrace (prefixWord ++ tailWord_2716749) baseStart_2716749 baseEnd_2716749 := by
    simpa [prefixWord, tailWord_2716749, baseEnd_2716749] using wordTrace_append hprefix tailTrace_2716749
  have hstable : (prefixWord ++ tailWord_2716749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716749).length < 2 ^ (prefixWord ++ tailWord_2716749).sum := by decide
  have hdescent : baseEnd_2716749 < baseStart_2716749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716766 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2716766 : Nat := 118140960795 + 2716766 * 2 ^ 59
def prefixEnd_2716766 : Nat := 4983230072969 + 3 ^ 40 * 2716766 * 2
def baseEnd_2716766 : Nat := 1395006783792822874230827

theorem tailTrace_2716766 : CollatzResearch.WordTrace tailWord_2716766 prefixEnd_2716766 1395006783792822874230827 := by
  unfold tailWord_2716766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12386074559453530442255269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66059064317085495692028101 12386074559453530442255269)
  ·
    refine ⟨2322388979897536957922863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12386074559453530442255269 2322388979897536957922863)
    ·
      refine ⟨3483583469846305436884295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2322388979897536957922863 3483583469846305436884295)
      ·
        refine ⟨5225375204769458155326443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3483583469846305436884295 5225375204769458155326443)
        ·
          refine ⟨7838062807154187232989665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5225375204769458155326443 7838062807154187232989665)
          ·
            refine ⟨5878547105365640424742249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7838062807154187232989665 5878547105365640424742249)
            ·
              refine ⟨4408910329024230318556687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5878547105365640424742249 4408910329024230318556687)
              ·
                refine ⟨6613365493536345477835031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408910329024230318556687 6613365493536345477835031)
                ·
                  refine ⟨9920048240304518216752547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6613365493536345477835031 9920048240304518216752547)
                  ·
                    refine ⟨14880072360456777325128821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9920048240304518216752547 14880072360456777325128821)
                    ·
                      refine ⟨1395006783792822874230827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14880072360456777325128821 1395006783792822874230827)
                      ·
                        rfl

theorem cell23_2716766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2716766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716766 prefixEnd_2716766 := by exact prefixLift 2716766
  have htrace : WordTrace (prefixWord ++ tailWord_2716766) baseStart_2716766 baseEnd_2716766 := by
    simpa [prefixWord, tailWord_2716766, baseEnd_2716766] using wordTrace_append hprefix tailTrace_2716766
  have hstable : (prefixWord ++ tailWord_2716766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716766).length < 2 ^ (prefixWord ++ tailWord_2716766).sum := by decide
  have hdescent : baseEnd_2716766 < baseStart_2716766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716772 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 5, 3, 2]
def baseStart_2716772 : Nat := 118140960795 + 2716772 * 2 ^ 59
def prefixEnd_2716772 : Nat := 4983230072969 + 3 ^ 40 * 2716772 * 2
def baseEnd_2716772 : Nat := 1395009864676749850755799

theorem tailTrace_2716772 : CollatzResearch.WordTrace tailWord_2716772 prefixEnd_2716772 1395009864676749850755799 := by
  unfold tailWord_2716772
  simp only [CollatzResearch.WordTrace]
  refine ⟨49544407656803253281380285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66059210209071004375173713 49544407656803253281380285)
  ·
    refine ⟨18579152871301219980517607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49544407656803253281380285 18579152871301219980517607)
    ·
      refine ⟨27868729306951829970776411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18579152871301219980517607 27868729306951829970776411)
      ·
        refine ⟨41803093960427744956164617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27868729306951829970776411 41803093960427744956164617)
        ·
          refine ⟨31352320470320808717123463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41803093960427744956164617 31352320470320808717123463)
          ·
            refine ⟨47028480705481213075685195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31352320470320808717123463 47028480705481213075685195)
            ·
              refine ⟨70542721058221819613527793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47028480705481213075685195 70542721058221819613527793)
              ·
                refine ⟨52907040793666364710145845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70542721058221819613527793 52907040793666364710145845)
                ·
                  refine ⟨4960035074406221691576173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52907040793666364710145845 4960035074406221691576173)
                  ·
                    refine ⟨1860013152902333134341065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4960035074406221691576173 1860013152902333134341065)
                    ·
                      refine ⟨1395009864676749850755799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860013152902333134341065 1395009864676749850755799)
                      ·
                        rfl

theorem cell23_2716772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_2716772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716772 prefixEnd_2716772 := by exact prefixLift 2716772
  have htrace : WordTrace (prefixWord ++ tailWord_2716772) baseStart_2716772 baseEnd_2716772 := by
    simpa [prefixWord, tailWord_2716772, baseEnd_2716772] using wordTrace_append hprefix tailTrace_2716772
  have hstable : (prefixWord ++ tailWord_2716772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716772).length < 2 ^ (prefixWord ++ tailWord_2716772).sum := by decide
  have hdescent : baseEnd_2716772 < baseStart_2716772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716835 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 3]
def baseStart_2716835 : Nat := 118140960795 + 2716835 * 2 ^ 59
def prefixEnd_2716835 : Nat := 4983230072969 + 3 ^ 40 * 2716835 * 2
def baseEnd_2716835 : Nat := 1395042213957983104268009

theorem tailTrace_2716835 : CollatzResearch.WordTrace tailWord_2716835 prefixEnd_2716835 1395042213957983104268009 := by
  unfold tailWord_2716835
  simp only [CollatzResearch.WordTrace]
  refine ⟨99091113112378268322303959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66060742074918845548202639 99091113112378268322303959)
  ·
    refine ⟨148636669668567402483455939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99091113112378268322303959 148636669668567402483455939)
    ·
      refine ⟨222955004502851103725183909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148636669668567402483455939 222955004502851103725183909)
      ·
        refine ⟨41804063344284581948471983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222955004502851103725183909 41804063344284581948471983)
        ·
          refine ⟨62706095016426872922707975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41804063344284581948471983 62706095016426872922707975)
          ·
            refine ⟨94059142524640309384061963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62706095016426872922707975 94059142524640309384061963)
            ·
              refine ⟨141088713786960464076092945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94059142524640309384061963 141088713786960464076092945)
              ·
                refine ⟨105816535340220348057069709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141088713786960464076092945 105816535340220348057069709)
                ·
                  refine ⟨39681200752582630521401141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105816535340220348057069709 39681200752582630521401141)
                  ·
                    refine ⟨3720112570554621611381357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39681200752582630521401141 3720112570554621611381357)
                    ·
                      refine ⟨1395042213957983104268009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3720112570554621611381357 1395042213957983104268009)
                      ·
                        rfl

theorem cell23_2716835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_2716835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716835 prefixEnd_2716835 := by exact prefixLift 2716835
  have htrace : WordTrace (prefixWord ++ tailWord_2716835) baseStart_2716835 baseEnd_2716835 := by
    simpa [prefixWord, tailWord_2716835, baseEnd_2716835] using wordTrace_append hprefix tailTrace_2716835
  have hstable : (prefixWord ++ tailWord_2716835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716835).length < 2 ^ (prefixWord ++ tailWord_2716835).sum := by decide
  have hdescent : baseEnd_2716835 < baseStart_2716835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716836 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 2, 2, 2]
def baseStart_2716836 : Nat := 118140960795 + 2716836 * 2 ^ 59
def prefixEnd_2716836 : Nat := 4983230072969 + 3 ^ 40 * 2716836 * 2
def baseEnd_2716836 : Nat := 1395042727438637600355505

theorem tailTrace_2716836 : CollatzResearch.WordTrace tailWord_2716836 prefixEnd_2716836 1395042727438637600355505 := by
  unfold tailWord_2716836
  simp only [CollatzResearch.WordTrace]
  refine ⟨49545574792687322746545181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66060766390249763662060241 49545574792687322746545181)
  ·
    refine ⟨18579590547257746029954443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49545574792687322746545181 18579590547257746029954443)
    ·
      refine ⟨27869385820886619044931665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18579590547257746029954443 27869385820886619044931665)
      ·
        refine ⟨20902039365664964283698749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27869385820886619044931665 20902039365664964283698749)
        ·
          refine ⟨7838264762124361606387031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20902039365664964283698749 7838264762124361606387031)
          ·
            refine ⟨11757397143186542409580547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7838264762124361606387031 11757397143186542409580547)
            ·
              refine ⟨17636095714779813614370821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11757397143186542409580547 17636095714779813614370821)
              ·
                refine ⟨3306767946521215052694529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17636095714779813614370821 3306767946521215052694529)
                ·
                  refine ⟨2480075959890911289520897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3306767946521215052694529 2480075959890911289520897)
                  ·
                    refine ⟨1860056969918183467140673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2480075959890911289520897 1860056969918183467140673)
                    ·
                      refine ⟨1395042727438637600355505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860056969918183467140673 1395042727438637600355505)
                      ·
                        rfl

theorem cell23_2716836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_2716836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716836 prefixEnd_2716836 := by exact prefixLift 2716836
  have htrace : WordTrace (prefixWord ++ tailWord_2716836) baseStart_2716836 baseEnd_2716836 := by
    simpa [prefixWord, tailWord_2716836, baseEnd_2716836] using wordTrace_append hprefix tailTrace_2716836
  have hstable : (prefixWord ++ tailWord_2716836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716836).length < 2 ^ (prefixWord ++ tailWord_2716836).sum := by decide
  have hdescent : baseEnd_2716836 < baseStart_2716836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716855 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 1, 7]
def baseStart_2716855 : Nat := 118140960795 + 2716855 * 2 ^ 59
def prefixEnd_2716855 : Nat := 4983230072969 + 3 ^ 40 * 2716855 * 2
def baseEnd_2716855 : Nat := 465017494523691008672639

theorem tailTrace_2716855 : CollatzResearch.WordTrace tailWord_2716855 prefixEnd_2716855 465017494523691008672639 := by
  unfold tailWord_2716855
  simp only [CollatzResearch.WordTrace]
  refine ⟨99091842572305811738032019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66061228381537207825354679 99091842572305811738032019)
  ·
    refine ⟨148637763858458717607048029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99091842572305811738032019 148637763858458717607048029)
    ·
      refine ⟨55739161446922019102643011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148637763858458717607048029 55739161446922019102643011)
      ·
        refine ⟨83608742170383028653964517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55739161446922019102643011 83608742170383028653964517)
        ·
          refine ⟨15676639156946817872618347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83608742170383028653964517 15676639156946817872618347)
          ·
            refine ⟨23514958735420226808927521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15676639156946817872618347 23514958735420226808927521)
            ·
              refine ⟨17636219051565170106695641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23514958735420226808927521 17636219051565170106695641)
              ·
                refine ⟨13227164288673877580021731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17636219051565170106695641 13227164288673877580021731)
                ·
                  refine ⟨19840746433010816370032597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13227164288673877580021731 19840746433010816370032597)
                  ·
                    refine ⟨465017494523691008672639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19840746433010816370032597 465017494523691008672639)
                    ·
                      rfl

theorem cell23_2716855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_2716855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716855 prefixEnd_2716855 := by exact prefixLift 2716855
  have htrace : WordTrace (prefixWord ++ tailWord_2716855) baseStart_2716855 baseEnd_2716855 := by
    simpa [prefixWord, tailWord_2716855, baseEnd_2716855] using wordTrace_append hprefix tailTrace_2716855
  have hstable : (prefixWord ++ tailWord_2716855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716855).length < 2 ^ (prefixWord ++ tailWord_2716855).sum := by decide
  have hdescent : baseEnd_2716855 < baseStart_2716855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716872 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 2, 5]
def baseStart_2716872 : Nat := 118140960795 + 2716872 * 2 ^ 59
def prefixEnd_2716872 : Nat := 4983230072969 + 3 ^ 40 * 2716872 * 2
def baseEnd_2716872 : Nat := 465020404247399819835113

theorem tailTrace_2716872 : CollatzResearch.WordTrace tailWord_2716872 prefixEnd_2716872 465020404247399819835113 := by
  unfold tailWord_2716872
  simp only [CollatzResearch.WordTrace]
  refine ⟨49546231306622111820700435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66061641742162815760933913 49546231306622111820700435)
  ·
    refine ⟨74319346959933167731050653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49546231306622111820700435 74319346959933167731050653)
    ·
      refine ⟨27869755109974937899143995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74319346959933167731050653 27869755109974937899143995)
      ·
        refine ⟨41804632664962406848715993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27869755109974937899143995 41804632664962406848715993)
        ·
          refine ⟨31353474498721805136536995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41804632664962406848715993 31353474498721805136536995)
          ·
            refine ⟨47030211748082707704805493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31353474498721805136536995 47030211748082707704805493)
            ·
              refine ⟨4409082351382753847325515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47030211748082707704805493 4409082351382753847325515)
              ·
                refine ⟨6613623527074130770988273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4409082351382753847325515 6613623527074130770988273)
                ·
                  refine ⟨4960217645305598078241205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6613623527074130770988273 4960217645305598078241205)
                  ·
                    refine ⟨465020404247399819835113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4960217645305598078241205 465020404247399819835113)
                    ·
                      rfl

theorem cell23_2716872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_2716872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716872 prefixEnd_2716872 := by exact prefixLift 2716872
  have htrace : WordTrace (prefixWord ++ tailWord_2716872) baseStart_2716872 baseEnd_2716872 := by
    simpa [prefixWord, tailWord_2716872, baseEnd_2716872] using wordTrace_append hprefix tailTrace_2716872
  have hstable : (prefixWord ++ tailWord_2716872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716872).length < 2 ^ (prefixWord ++ tailWord_2716872).sum := by decide
  have hdescent : baseEnd_2716872 < baseStart_2716872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716895 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_2716895 : Nat := 118140960795 + 2716895 * 2 ^ 59
def prefixEnd_2716895 : Nat := 4983230072969 + 3 ^ 40 * 2716895 * 2
def baseEnd_2716895 : Nat := 1395073022797252869517733

theorem tailTrace_2716895 : CollatzResearch.WordTrace tailWord_2716895 prefixEnd_2716895 1395073022797252869517733 := by
  unfold tailWord_2716895
  simp only [CollatzResearch.WordTrace]
  refine ⟨99093301492160898569488139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66062200994773932379658759 99093301492160898569488139)
  ·
    refine ⟨148639952238241347854232209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99093301492160898569488139 148639952238241347854232209)
    ·
      refine ⟨111479964178681010890674157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148639952238241347854232209 111479964178681010890674157)
      ·
        refine ⟨41804986567005379084002809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111479964178681010890674157 41804986567005379084002809)
        ·
          refine ⟨31353739925254034313002107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41804986567005379084002809 31353739925254034313002107)
          ·
            refine ⟨47030609887881051469503161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31353739925254034313002107 47030609887881051469503161)
            ·
              refine ⟨35272957415910788602127371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47030609887881051469503161 35272957415910788602127371)
              ·
                refine ⟨52909436123866182903191057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35272957415910788602127371 52909436123866182903191057)
                ·
                  refine ⟨39682077092899637177393293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52909436123866182903191057 39682077092899637177393293)
                  ·
                    refine ⟨14880778909837363941522485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39682077092899637177393293 14880778909837363941522485)
                    ·
                      refine ⟨1395073022797252869517733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14880778909837363941522485 1395073022797252869517733)
                      ·
                        rfl

theorem cell23_2716895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_2716895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716895 prefixEnd_2716895 := by exact prefixLift 2716895
  have htrace : WordTrace (prefixWord ++ tailWord_2716895) baseStart_2716895 baseEnd_2716895 := by
    simpa [prefixWord, tailWord_2716895, baseEnd_2716895] using wordTrace_append hprefix tailTrace_2716895
  have hstable : (prefixWord ++ tailWord_2716895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716895).length < 2 ^ (prefixWord ++ tailWord_2716895).sum := by decide
  have hdescent : baseEnd_2716895 < baseStart_2716895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716905 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_2716905 : Nat := 118140960795 + 2716905 * 2 ^ 59
def prefixEnd_2716905 : Nat := 4983230072969 + 3 ^ 40 * 2716905 * 2
def baseEnd_2716905 : Nat := 1395078157603797830392687

theorem tailTrace_2716905 : CollatzResearch.WordTrace tailWord_2716905 prefixEnd_2716905 1395078157603797830392687 := by
  unfold tailWord_2716905
  simp only [CollatzResearch.WordTrace]
  refine ⟨99093666222124670277352169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66062444148083113518234779 99093666222124670277352169)
  ·
    refine ⟨74320249666593502708014127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99093666222124670277352169 74320249666593502708014127)
    ·
      refine ⟨111480374499890254062021191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74320249666593502708014127 111480374499890254062021191)
      ·
        refine ⟨167220561749835381093031787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111480374499890254062021191 167220561749835381093031787)
        ·
          refine ⟨250830842624753071639547681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167220561749835381093031787 250830842624753071639547681)
          ·
            refine ⟨188123131968564803729660761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250830842624753071639547681 188123131968564803729660761)
            ·
              refine ⟨141092348976423602797245571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188123131968564803729660761 141092348976423602797245571)
              ·
                refine ⟨211638523464635404195868357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141092348976423602797245571 211638523464635404195868357)
                ·
                  refine ⟨39682223149619138286725317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211638523464635404195868357 39682223149619138286725317)
                  ·
                    refine ⟨7440416840553588428760997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39682223149619138286725317 7440416840553588428760997)
                    ·
                      refine ⟨1395078157603797830392687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7440416840553588428760997 1395078157603797830392687)
                      ·
                        rfl

theorem cell23_2716905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_2716905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716905 prefixEnd_2716905 := by exact prefixLift 2716905
  have htrace : WordTrace (prefixWord ++ tailWord_2716905) baseStart_2716905 baseEnd_2716905 := by
    simpa [prefixWord, tailWord_2716905, baseEnd_2716905] using wordTrace_append hprefix tailTrace_2716905
  have hstable : (prefixWord ++ tailWord_2716905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716905).length < 2 ^ (prefixWord ++ tailWord_2716905).sum := by decide
  have hdescent : baseEnd_2716905 < baseStart_2716905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716925 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_2716925 : Nat := 118140960795 + 2716925 * 2 ^ 59
def prefixEnd_2716925 : Nat := 4983230072969 + 3 ^ 40 * 2716925 * 2
def baseEnd_2716925 : Nat := 1395088427216887752142595

theorem tailTrace_2716925 : CollatzResearch.WordTrace tailWord_2716925 prefixEnd_2716925 1395088427216887752142595 := by
  unfold tailWord_2716925
  simp only [CollatzResearch.WordTrace]
  refine ⟨99094395682052213693080229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66062930454701475795386819 99094395682052213693080229)
  ·
    refine ⟨18580199190384790067452543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99094395682052213693080229 18580199190384790067452543)
    ·
      refine ⟨27870298785577185101178815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18580199190384790067452543 27870298785577185101178815)
      ·
        refine ⟨41805448178365777651768223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27870298785577185101178815 41805448178365777651768223)
        ·
          refine ⟨62708172267548666477652335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41805448178365777651768223 62708172267548666477652335)
          ·
            refine ⟨94062258401322999716478503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62708172267548666477652335 94062258401322999716478503)
            ·
              refine ⟨141093387601984499574717755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94062258401322999716478503 141093387601984499574717755)
              ·
                refine ⟨211640081402976749362076633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141093387601984499574717755 211640081402976749362076633)
                ·
                  refine ⟨158730061052232562021557475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211640081402976749362076633 158730061052232562021557475)
                  ·
                    refine ⟨238095091578348843032336213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158730061052232562021557475 238095091578348843032336213)
                    ·
                      refine ⟨1395088427216887752142595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 238095091578348843032336213 1395088427216887752142595)
                      ·
                        rfl

theorem cell23_2716925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_2716925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716925 prefixEnd_2716925 := by exact prefixLift 2716925
  have htrace : WordTrace (prefixWord ++ tailWord_2716925) baseStart_2716925 baseEnd_2716925 := by
    simpa [prefixWord, tailWord_2716925, baseEnd_2716925] using wordTrace_append hprefix tailTrace_2716925
  have hstable : (prefixWord ++ tailWord_2716925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716925).length < 2 ^ (prefixWord ++ tailWord_2716925).sum := by decide
  have hdescent : baseEnd_2716925 < baseStart_2716925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716932 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 8]
def baseStart_2716932 : Nat := 118140960795 + 2716932 * 2 ^ 59
def prefixEnd_2716932 : Nat := 4983230072969 + 3 ^ 40 * 2716932 * 2
def baseEnd_2716932 : Nat := 155010224620163247195007

theorem tailTrace_2716932 : CollatzResearch.WordTrace tailWord_2716932 prefixEnd_2716932 155010224620163247195007 := by
  unfold tailWord_2716932
  simp only [CollatzResearch.WordTrace]
  refine ⟨49547325496513426944292525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66063100662017902592390033 49547325496513426944292525)
  ·
    refine ⟨18580247061192535104109697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49547325496513426944292525 18580247061192535104109697)
    ·
      refine ⟨13935185295894401328082273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18580247061192535104109697 13935185295894401328082273)
      ·
        refine ⟨10451388971920800996061705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13935185295894401328082273 10451388971920800996061705)
        ·
          refine ⟨7838541728940600747046279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10451388971920800996061705 7838541728940600747046279)
          ·
            refine ⟨11757812593410901120569419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7838541728940600747046279 11757812593410901120569419)
            ·
              refine ⟨17636718890116351680854129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11757812593410901120569419 17636718890116351680854129)
              ·
                refine ⟨13227539167587263760640597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17636718890116351680854129 13227539167587263760640597)
                ·
                  refine ⟨155010224620163247195007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13227539167587263760640597 155010224620163247195007)
                  ·
                    rfl

theorem cell23_2716932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_2716932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716932 prefixEnd_2716932 := by exact prefixLift 2716932
  have htrace : WordTrace (prefixWord ++ tailWord_2716932) baseStart_2716932 baseEnd_2716932 := by
    simpa [prefixWord, tailWord_2716932, baseEnd_2716932] using wordTrace_append hprefix tailTrace_2716932
  have hstable : (prefixWord ++ tailWord_2716932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716932).length < 2 ^ (prefixWord ++ tailWord_2716932).sum := by decide
  have hdescent : baseEnd_2716932 < baseStart_2716932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716955 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 7]
def baseStart_2716955 : Nat := 118140960795 + 2716955 * 2 ^ 59
def prefixEnd_2716955 : Nat := 4983230072969 + 3 ^ 40 * 2716955 * 2
def baseEnd_2716955 : Nat := 1395103831636522634767457

theorem tailTrace_2716955 : CollatzResearch.WordTrace tailWord_2716955 prefixEnd_2716955 1395103831636522634767457 := by
  unfold tailWord_2716955
  simp only [CollatzResearch.WordTrace]
  refine ⟨99095489871943528816672319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66063659914629019211114879 99095489871943528816672319)
  ·
    refine ⟨148643234807915293225008479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99095489871943528816672319 148643234807915293225008479)
    ·
      refine ⟨222964852211872939837512719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148643234807915293225008479 222964852211872939837512719)
      ·
        refine ⟨334447278317809409756269079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222964852211872939837512719 334447278317809409756269079)
        ·
          refine ⟨501670917476714114634403619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334447278317809409756269079 501670917476714114634403619)
          ·
            refine ⟨752506376215071171951605429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501670917476714114634403619 752506376215071171951605429)
            ·
              refine ⟨70547472770162922370463009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 752506376215071171951605429 70547472770162922370463009)
              ·
                refine ⟨52910604577622191777847257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70547472770162922370463009 52910604577622191777847257)
                ·
                  refine ⟨39682953433216643833385443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52910604577622191777847257 39682953433216643833385443)
                  ·
                    refine ⟨59524430149824965750078165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39682953433216643833385443 59524430149824965750078165)
                    ·
                      refine ⟨1395103831636522634767457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59524430149824965750078165 1395103831636522634767457)
                      ·
                        rfl

theorem cell23_2716955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_2716955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716955 prefixEnd_2716955 := by exact prefixLift 2716955
  have htrace : WordTrace (prefixWord ++ tailWord_2716955) baseStart_2716955 baseEnd_2716955 := by
    simpa [prefixWord, tailWord_2716955, baseEnd_2716955] using wordTrace_append hprefix tailTrace_2716955
  have hstable : (prefixWord ++ tailWord_2716955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716955).length < 2 ^ (prefixWord ++ tailWord_2716955).sum := by decide
  have hdescent : baseEnd_2716955 < baseStart_2716955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716979 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 1, 5]
def baseStart_2716979 : Nat := 118140960795 + 2716979 * 2 ^ 59
def prefixEnd_2716979 : Nat := 4983230072969 + 3 ^ 40 * 2716979 * 2
def baseEnd_2716979 : Nat := 465038718390743513622449

theorem tailTrace_2716979 : CollatzResearch.WordTrace tailWord_2716979 prefixEnd_2716979 465038718390743513622449 := by
  unfold tailWord_2716979
  simp only [CollatzResearch.WordTrace]
  refine ⟨99096365223856580915545991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66064243482571053943697327 99096365223856580915545991)
  ·
    refine ⟨148644547835784871373318987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99096365223856580915545991 148644547835784871373318987)
    ·
      refine ⟨222966821753677307059978481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148644547835784871373318987 222966821753677307059978481)
      ·
        refine ⟨167225116315257980294983861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222966821753677307059978481 167225116315257980294983861)
        ·
          refine ⟨15677354654555435652654737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167225116315257980294983861 15677354654555435652654737)
          ·
            refine ⟨11758015990916576739491053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15677354654555435652654737 11758015990916576739491053)
            ·
              refine ⟨4409255996593716277309145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11758015990916576739491053 4409255996593716277309145)
              ·
                refine ⟨3306941997445287207981859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4409255996593716277309145 3306941997445287207981859)
                ·
                  refine ⟨4960412996167930811972789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306941997445287207981859 4960412996167930811972789)
                  ·
                    refine ⟨465038718390743513622449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4960412996167930811972789 465038718390743513622449)
                    ·
                      rfl

theorem cell23_2716979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 5].length) (baseStart_2716979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716979 prefixEnd_2716979 := by exact prefixLift 2716979
  have htrace : WordTrace (prefixWord ++ tailWord_2716979) baseStart_2716979 baseEnd_2716979 := by
    simpa [prefixWord, tailWord_2716979, baseEnd_2716979] using wordTrace_append hprefix tailTrace_2716979
  have hstable : (prefixWord ++ tailWord_2716979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716979).length < 2 ^ (prefixWord ++ tailWord_2716979).sum := by decide
  have hdescent : baseEnd_2716979 < baseStart_2716979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716986 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2]
def baseStart_2716986 : Nat := 118140960795 + 2716986 * 2 ^ 59
def prefixEnd_2716986 : Nat := 4983230072969 + 3 ^ 40 * 2716986 * 2
def baseEnd_2716986 : Nat := 1395119749536812013479815

theorem tailTrace_2716986 : CollatzResearch.WordTrace tailWord_2716986 prefixEnd_2716986 1395119749536812013479815 := by
  unfold tailWord_2716986
  simp only [CollatzResearch.WordTrace]
  refine ⟨24774155133707805277762703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66064413689887480740700541 24774155133707805277762703)
  ·
    refine ⟨37161232700561707916644055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24774155133707805277762703 37161232700561707916644055)
    ·
      refine ⟨55741849050842561874966083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37161232700561707916644055 55741849050842561874966083)
      ·
        refine ⟨83612773576263842812449125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55741849050842561874966083 83612773576263842812449125)
        ·
          refine ⟨15677395045549470527334211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83612773576263842812449125 15677395045549470527334211)
          ·
            refine ⟨23516092568324205791001317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15677395045549470527334211 23516092568324205791001317)
            ·
              refine ⟨4409267356560788585812747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23516092568324205791001317 4409267356560788585812747)
              ·
                refine ⟨6613901034841182878719121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4409267356560788585812747 6613901034841182878719121)
                ·
                  refine ⟨4960425776130887159039341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6613901034841182878719121 4960425776130887159039341)
                  ·
                    refine ⟨1860159666049082684639753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4960425776130887159039341 1860159666049082684639753)
                    ·
                      refine ⟨1395119749536812013479815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860159666049082684639753 1395119749536812013479815)
                      ·
                        rfl

theorem cell23_2716986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_2716986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716986 prefixEnd_2716986 := by exact prefixLift 2716986
  have htrace : WordTrace (prefixWord ++ tailWord_2716986) baseStart_2716986 baseEnd_2716986 := by
    simpa [prefixWord, tailWord_2716986, baseEnd_2716986] using wordTrace_append hprefix tailTrace_2716986
  have hstable : (prefixWord ++ tailWord_2716986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716986).length < 2 ^ (prefixWord ++ tailWord_2716986).sum := by decide
  have hdescent : baseEnd_2716986 < baseStart_2716986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716992 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 1, 6]
def baseStart_2716992 : Nat := 118140960795 + 2716992 * 2 ^ 59
def prefixEnd_2716992 : Nat := 4983230072969 + 3 ^ 40 * 2716992 * 2
def baseEnd_2716992 : Nat := 465040943473579663334929

theorem tailTrace_2716992 : CollatzResearch.WordTrace tailWord_2716992 prefixEnd_2716992 465040943473579663334929 := by
  unfold tailWord_2716992
  simp only [CollatzResearch.WordTrace]
  refine ⟨49548419686404742067884615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66064559581872989423846153 49548419686404742067884615)
  ·
    refine ⟨74322629529607113101826923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49548419686404742067884615 74322629529607113101826923)
    ·
      refine ⟨111483944294410669652740385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74322629529607113101826923 111483944294410669652740385)
      ·
        refine ⟨83612958220808002239555289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111483944294410669652740385 83612958220808002239555289)
        ·
          refine ⟨62709718665606001679666467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83612958220808002239555289 62709718665606001679666467)
          ·
            refine ⟨94064577998409002519499701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62709718665606001679666467 94064577998409002519499701)
            ·
              refine ⟨8818554187350843986203097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94064577998409002519499701 8818554187350843986203097)
              ·
                refine ⟨6613915640513132989652323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8818554187350843986203097 6613915640513132989652323)
                ·
                  refine ⟨9920873460769699484478485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6613915640513132989652323 9920873460769699484478485)
                  ·
                    refine ⟨465040943473579663334929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9920873460769699484478485 465040943473579663334929)
                    ·
                      rfl

theorem cell23_2716992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_2716992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2716992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2716992 prefixEnd_2716992 := by exact prefixLift 2716992
  have htrace : WordTrace (prefixWord ++ tailWord_2716992) baseStart_2716992 baseEnd_2716992 := by
    simpa [prefixWord, tailWord_2716992, baseEnd_2716992] using wordTrace_append hprefix tailTrace_2716992
  have hstable : (prefixWord ++ tailWord_2716992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716992).length < 2 ^ (prefixWord ++ tailWord_2716992).sum := by decide
  have hdescent : baseEnd_2716992 < baseStart_2716992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717016 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 3, 2, 2]
def baseStart_2717016 : Nat := 118140960795 + 2717016 * 2 ^ 59
def prefixEnd_2717016 : Nat := 4983230072969 + 3 ^ 40 * 2717016 * 2
def baseEnd_2717016 : Nat := 1395135153956446896104677

theorem tailTrace_2717016 : CollatzResearch.WordTrace tailWord_2717016 prefixEnd_2717016 1395135153956446896104677 := by
  unfold tailWord_2717016
  simp only [CollatzResearch.WordTrace]
  refine ⟨49548857362361268117321451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66065143149815024156428601 49548857362361268117321451)
  ·
    refine ⟨74323286043541902175982177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49548857362361268117321451 74323286043541902175982177)
    ·
      refine ⟨55742464532656426631986633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74323286043541902175982177 55742464532656426631986633)
      ·
        refine ⟨41806848399492319973989975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55742464532656426631986633 41806848399492319973989975)
        ·
          refine ⟨62710272599238479960984963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41806848399492319973989975 62710272599238479960984963)
          ·
            refine ⟨94065408898857719941477445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62710272599238479960984963 94065408898857719941477445)
            ·
              refine ⟨17637264168535822489027021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94065408898857719941477445 17637264168535822489027021)
              ·
                refine ⟨6613974063200933433385133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17637264168535822489027021 6613974063200933433385133)
                ·
                  refine ⟨2480240273700350037519425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6613974063200933433385133 2480240273700350037519425)
                  ·
                    refine ⟨1860180205275262528139569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2480240273700350037519425 1860180205275262528139569)
                    ·
                      refine ⟨1395135153956446896104677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860180205275262528139569 1395135153956446896104677)
                      ·
                        rfl

theorem cell23_2717016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_2717016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717016 prefixEnd_2717016 := by exact prefixLift 2717016
  have htrace : WordTrace (prefixWord ++ tailWord_2717016) baseStart_2717016 baseEnd_2717016 := by
    simpa [prefixWord, tailWord_2717016, baseEnd_2717016] using wordTrace_append hprefix tailTrace_2717016
  have hstable : (prefixWord ++ tailWord_2717016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717016).length < 2 ^ (prefixWord ++ tailWord_2717016).sum := by decide
  have hdescent : baseEnd_2717016 < baseStart_2717016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717026 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2717026 : Nat := 118140960795 + 2717026 * 2 ^ 59
def prefixEnd_2717026 : Nat := 4983230072969 + 3 ^ 40 * 2717026 * 2
def baseEnd_2717026 : Nat := 465046762920997285659877

theorem tailTrace_2717026 : CollatzResearch.WordTrace tailWord_2717026 prefixEnd_2717026 465046762920997285659877 := by
  unfold tailWord_2717026
  simp only [CollatzResearch.WordTrace]
  refine ⟨24774519863671576985626733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66065386303124205295004621 24774519863671576985626733)
  ·
    refine ⟨9290444948876841369610025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24774519863671576985626733 9290444948876841369610025)
    ·
      refine ⟨6967833711657631027207519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9290444948876841369610025 6967833711657631027207519)
      ·
        refine ⟨10451750567486446540811279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6967833711657631027207519 10451750567486446540811279)
        ·
          refine ⟨15677625851229669811216919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10451750567486446540811279 15677625851229669811216919)
          ·
            refine ⟨23516438776844504716825379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15677625851229669811216919 23516438776844504716825379)
            ·
              refine ⟨35274658165266757075238069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23516438776844504716825379 35274658165266757075238069)
              ·
                refine ⟨3306999202993758475803569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35274658165266757075238069 3306999202993758475803569)
                ·
                  refine ⟨2480249402245318856852677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3306999202993758475803569 2480249402245318856852677)
                  ·
                    refine ⟨465046762920997285659877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2480249402245318856852677 465046762920997285659877)
                    ·
                      rfl

theorem cell23_2717026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2717026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717026 prefixEnd_2717026 := by exact prefixLift 2717026
  have htrace : WordTrace (prefixWord ++ tailWord_2717026) baseStart_2717026 baseEnd_2717026 := by
    simpa [prefixWord, tailWord_2717026, baseEnd_2717026] using wordTrace_append hprefix tailTrace_2717026
  have hstable : (prefixWord ++ tailWord_2717026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717026).length < 2 ^ (prefixWord ++ tailWord_2717026).sum := by decide
  have hdescent : baseEnd_2717026 < baseStart_2717026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717029 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 4]
def baseStart_2717029 : Nat := 118140960795 + 2717029 * 2 ^ 59
def prefixEnd_2717029 : Nat := 4983230072969 + 3 ^ 40 * 2717029 * 2
def baseEnd_2717029 : Nat := 1395141829204955345242117

theorem tailTrace_2717029 : CollatzResearch.WordTrace tailWord_2717029 prefixEnd_2717029 1395141829204955345242117 := by
  unfold tailWord_2717029
  simp only [CollatzResearch.WordTrace]
  refine ⟨99098188873675439454866141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66065459249116959636577427 99098188873675439454866141)
  ·
    refine ⟨37161820827628289795574803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99098188873675439454866141 37161820827628289795574803)
    ·
      refine ⟨55742731241442434693362205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37161820827628289795574803 55742731241442434693362205)
      ·
        refine ⟨20903524215540913010010827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55742731241442434693362205 20903524215540913010010827)
        ·
          refine ⟨31355286323311369515016241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20903524215540913010010827 31355286323311369515016241)
          ·
            refine ⟨23516464742483527136262181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31355286323311369515016241 23516464742483527136262181)
            ·
              refine ⟨4409337139215661338049159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23516464742483527136262181 4409337139215661338049159)
              ·
                refine ⟨6614005708823492007073739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4409337139215661338049159 6614005708823492007073739)
                ·
                  refine ⟨9921008563235238010610609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6614005708823492007073739 9921008563235238010610609)
                  ·
                    refine ⟨7440756422426428507957957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9921008563235238010610609 7440756422426428507957957)
                    ·
                      refine ⟨1395141829204955345242117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7440756422426428507957957 1395141829204955345242117)
                      ·
                        rfl

theorem cell23_2717029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_2717029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717029 prefixEnd_2717029 := by exact prefixLift 2717029
  have htrace : WordTrace (prefixWord ++ tailWord_2717029) baseStart_2717029 baseEnd_2717029 := by
    simpa [prefixWord, tailWord_2717029, baseEnd_2717029] using wordTrace_append hprefix tailTrace_2717029
  have hstable : (prefixWord ++ tailWord_2717029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717029).length < 2 ^ (prefixWord ++ tailWord_2717029).sum := by decide
  have hdescent : baseEnd_2717029 < baseStart_2717029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717049 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 1, 3, 3]
def baseStart_2717049 : Nat := 118140960795 + 2717049 * 2 ^ 59
def prefixEnd_2717049 : Nat := 4983230072969 + 3 ^ 40 * 2717049 * 2
def baseEnd_2717049 : Nat := 1395152098818045266992025

theorem tailTrace_2717049 : CollatzResearch.WordTrace tailWord_2717049 prefixEnd_2717049 1395152098818045266992025 := by
  unfold tailWord_2717049
  simp only [CollatzResearch.WordTrace]
  refine ⟨99098918333602982870594201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66065945555735321913729467 99098918333602982870594201)
  ·
    refine ⟨74324188750202237152945651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99098918333602982870594201 74324188750202237152945651)
    ·
      refine ⟨111486283125303355729418477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74324188750202237152945651 111486283125303355729418477)
      ·
        refine ⟨41807356171988758398531929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111486283125303355729418477 41807356171988758398531929)
        ·
          refine ⟨31355517128991568798898947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41807356171988758398531929 31355517128991568798898947)
          ·
            refine ⟨47033275693487353198348421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31355517128991568798898947 47033275693487353198348421)
            ·
              refine ⟨8818739192528878724690329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47033275693487353198348421 8818739192528878724690329)
              ·
                refine ⟨6614054394396659043517747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8818739192528878724690329 6614054394396659043517747)
                ·
                  refine ⟨9921081591594988565276621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6614054394396659043517747 9921081591594988565276621)
                  ·
                    refine ⟨3720405596848120711978733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9921081591594988565276621 3720405596848120711978733)
                    ·
                      refine ⟨1395152098818045266992025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3720405596848120711978733 1395152098818045266992025)
                      ·
                        rfl

theorem cell23_2717049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_2717049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717049 prefixEnd_2717049 := by exact prefixLift 2717049
  have htrace : WordTrace (prefixWord ++ tailWord_2717049) baseStart_2717049 baseEnd_2717049 := by
    simpa [prefixWord, tailWord_2717049, baseEnd_2717049] using wordTrace_append hprefix tailTrace_2717049
  have hstable : (prefixWord ++ tailWord_2717049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717049).length < 2 ^ (prefixWord ++ tailWord_2717049).sum := by decide
  have hdescent : baseEnd_2717049 < baseStart_2717049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717109 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2717109 : Nat := 118140960795 + 2717109 * 2 ^ 59
def prefixEnd_2717109 : Nat := 4983230072969 + 3 ^ 40 * 2717109 * 2
def baseEnd_2717109 : Nat := 1395182907657315032241749

theorem tailTrace_2717109 : CollatzResearch.WordTrace tailWord_2717109 prefixEnd_2717109 1395182907657315032241749 := by
  unfold tailWord_2717109
  simp only [CollatzResearch.WordTrace]
  refine ⟨99101106713385613117778381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66067404475590408745185587 99101106713385613117778381)
  ·
    refine ⟨37162915017519604919166893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99101106713385613117778381 37162915017519604919166893)
    ·
      refine ⟨13936093131569851844687585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37162915017519604919166893 13936093131569851844687585)
      ·
        refine ⟨10452069848677388883515689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13936093131569851844687585 10452069848677388883515689)
        ·
          refine ⟨7839052386508041662636767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10452069848677388883515689 7839052386508041662636767)
          ·
            refine ⟨11758578579762062493955151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7839052386508041662636767 11758578579762062493955151)
            ·
              refine ⟨17637867869643093740932727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11758578579762062493955151 17637867869643093740932727)
              ·
                refine ⟨26456801804464640611399091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17637867869643093740932727 26456801804464640611399091)
                ·
                  refine ⟨39685202706696960917098637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26456801804464640611399091 39685202706696960917098637)
                  ·
                    refine ⟨14881951015011360343911989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39685202706696960917098637 14881951015011360343911989)
                    ·
                      refine ⟨1395182907657315032241749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14881951015011360343911989 1395182907657315032241749)
                      ·
                        rfl

theorem cell23_2717109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2717109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717109 prefixEnd_2717109 := by exact prefixLift 2717109
  have htrace : WordTrace (prefixWord ++ tailWord_2717109) baseStart_2717109 baseEnd_2717109 := by
    simpa [prefixWord, tailWord_2717109, baseEnd_2717109] using wordTrace_append hprefix tailTrace_2717109
  have hstable : (prefixWord ++ tailWord_2717109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717109).length < 2 ^ (prefixWord ++ tailWord_2717109).sum := by decide
  have hdescent : baseEnd_2717109 < baseStart_2717109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717112 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 9]
def baseStart_2717112 : Nat := 118140960795 + 2717112 * 2 ^ 59
def prefixEnd_2717112 : Nat := 4983230072969 + 3 ^ 40 * 2717112 * 2
def baseEnd_2717112 : Nat := 155020494233253168944915

theorem tailTrace_2717112 : CollatzResearch.WordTrace tailWord_2717112 prefixEnd_2717112 155020494233253168944915 := by
  unfold tailWord_2717112
  simp only [CollatzResearch.WordTrace]
  refine ⟨49550608066187372315068795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66067477421583163086758393 49550608066187372315068795)
  ·
    refine ⟨74325912099281058472603193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49550608066187372315068795 74325912099281058472603193)
    ·
      refine ⟨55744434074460793854452395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74325912099281058472603193 55744434074460793854452395)
      ·
        refine ⟨83616651111691190781678593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55744434074460793854452395 83616651111691190781678593)
        ·
          refine ⟨62712488333768393086258945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83616651111691190781678593 62712488333768393086258945)
          ·
            refine ⟨47034366250326294814694209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62712488333768393086258945 47034366250326294814694209)
            ·
              refine ⟨35275774687744721111020657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47034366250326294814694209 35275774687744721111020657)
              ·
                refine ⟨26456831015808540833265493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35275774687744721111020657 26456831015808540833265493)
                ·
                  refine ⟨155020494233253168944915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26456831015808540833265493 155020494233253168944915)
                  ·
                    rfl

theorem cell23_2717112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 9].length) (baseStart_2717112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717112 prefixEnd_2717112 := by exact prefixLift 2717112
  have htrace : WordTrace (prefixWord ++ tailWord_2717112) baseStart_2717112 baseEnd_2717112 := by
    simpa [prefixWord, tailWord_2717112, baseEnd_2717112] using wordTrace_append hprefix tailTrace_2717112
  have hstable : (prefixWord ++ tailWord_2717112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717112).length < 2 ^ (prefixWord ++ tailWord_2717112).sum := by decide
  have hdescent : baseEnd_2717112 < baseStart_2717112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717169 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_2717169 : Nat := 118140960795 + 2717169 * 2 ^ 59
def prefixEnd_2717169 : Nat := 4983230072969 + 3 ^ 40 * 2717169 * 2
def baseEnd_2717169 : Nat := 1395213716496584797491473

theorem tailTrace_2717169 : CollatzResearch.WordTrace tailWord_2717169 prefixEnd_2717169 1395213716496584797491473 := by
  unfold tailWord_2717169
  simp only [CollatzResearch.WordTrace]
  refine ⟨99103295093168243364962561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66068863395445495576641707 99103295093168243364962561)
  ·
    refine ⟨74327471319876182523721921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99103295093168243364962561 74327471319876182523721921)
    ·
      refine ⟨55745603489907136892791441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74327471319876182523721921 55745603489907136892791441)
      ·
        refine ⟨41809202617430352669593581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55745603489907136892791441 41809202617430352669593581)
        ·
          refine ⟨15678450981536382251097593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41809202617430352669593581 15678450981536382251097593)
          ·
            refine ⟨11758838236152286688323195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15678450981536382251097593 11758838236152286688323195)
            ·
              refine ⟨17638257354228430032484793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11758838236152286688323195 17638257354228430032484793)
              ·
                refine ⟨13228693015671322524363595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17638257354228430032484793 13228693015671322524363595)
                ·
                  refine ⟨19843039523506983786545393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13228693015671322524363595 19843039523506983786545393)
                  ·
                    refine ⟨14882279642630237839909045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19843039523506983786545393 14882279642630237839909045)
                    ·
                      refine ⟨1395213716496584797491473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14882279642630237839909045 1395213716496584797491473)
                      ·
                        rfl

theorem cell23_2717169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_2717169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717169 prefixEnd_2717169 := by exact prefixLift 2717169
  have htrace : WordTrace (prefixWord ++ tailWord_2717169) baseStart_2717169 baseEnd_2717169 := by
    simpa [prefixWord, tailWord_2717169, baseEnd_2717169] using wordTrace_append hprefix tailTrace_2717169
  have hstable : (prefixWord ++ tailWord_2717169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717169).length < 2 ^ (prefixWord ++ tailWord_2717169).sum := by decide
  have hdescent : baseEnd_2717169 < baseStart_2717169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717214 : List Nat := [4, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2717214 : Nat := 118140960795 + 2717214 * 2 ^ 59
def prefixEnd_2717214 : Nat := 4983230072969 + 3 ^ 40 * 2717214 * 2
def baseEnd_2717214 : Nat := 155026313680670791269863

theorem tailTrace_2717214 : CollatzResearch.WordTrace tailWord_2717214 prefixEnd_2717214 155026313680670791269863 := by
  unfold tailWord_2717214
  simp only [CollatzResearch.WordTrace]
  refine ⟨12388117047250652006293837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66069957585336810700233797 12388117047250652006293837)
  ·
    refine ⟨4645543892718994502360189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12388117047250652006293837 4645543892718994502360189)
    ·
      refine ⟨1742078959769622938385071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4645543892718994502360189 1742078959769622938385071)
      ·
        refine ⟨2613118439654434407577607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742078959769622938385071 2613118439654434407577607)
        ·
          refine ⟨3919677659481651611366411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613118439654434407577607 3919677659481651611366411)
          ·
            refine ⟨5879516489222477417049617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919677659481651611366411 5879516489222477417049617)
            ·
              refine ⟨4409637366916858062787213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5879516489222477417049617 4409637366916858062787213)
              ·
                refine ⟨1653614012593821773545205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4409637366916858062787213 1653614012593821773545205)
                ·
                  refine ⟨155026313680670791269863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1653614012593821773545205 155026313680670791269863)
                  ·
                    rfl

theorem cell23_2717214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2717214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717214 prefixEnd_2717214 := by exact prefixLift 2717214
  have htrace : WordTrace (prefixWord ++ tailWord_2717214) baseStart_2717214 baseEnd_2717214 := by
    simpa [prefixWord, tailWord_2717214, baseEnd_2717214] using wordTrace_append hprefix tailTrace_2717214
  have hstable : (prefixWord ++ tailWord_2717214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717214).length < 2 ^ (prefixWord ++ tailWord_2717214).sum := by decide
  have hdescent : baseEnd_2717214 < baseStart_2717214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717239 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_2717239 : Nat := 118140960795 + 2717239 * 2 ^ 59
def prefixEnd_2717239 : Nat := 4983230072969 + 3 ^ 40 * 2717239 * 2
def baseEnd_2717239 : Nat := 1395249660142399523616151

theorem tailTrace_2717239 : CollatzResearch.WordTrace tailWord_2717239 prefixEnd_2717239 1395249660142399523616151 := by
  unfold tailWord_2717239
  simp only [CollatzResearch.WordTrace]
  refine ⟨99105848202914645320010771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66070565468609763546673847 99105848202914645320010771)
  ·
    refine ⟨148658772304371967980016157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99105848202914645320010771 148658772304371967980016157)
    ·
      refine ⟨55747039614139487992506059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148658772304371967980016157 55747039614139487992506059)
      ·
        refine ⟨83620559421209231988759089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55747039614139487992506059 83620559421209231988759089)
        ·
          refine ⟨62715419565906923991569317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83620559421209231988759089 62715419565906923991569317)
          ·
            refine ⟨11759141168607548248419247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62715419565906923991569317 11759141168607548248419247)
            ·
              refine ⟨17638711752911322372628871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11759141168607548248419247 17638711752911322372628871)
              ·
                refine ⟨26458067629366983558943307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17638711752911322372628871 26458067629366983558943307)
                ·
                  refine ⟨39687101444050475338414961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26458067629366983558943307 39687101444050475338414961)
                  ·
                    refine ⟨29765326083037856503811221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39687101444050475338414961 29765326083037856503811221)
                    ·
                      refine ⟨1395249660142399523616151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29765326083037856503811221 1395249660142399523616151)
                      ·
                        rfl

theorem cell23_2717239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_2717239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717239 prefixEnd_2717239 := by exact prefixLift 2717239
  have htrace : WordTrace (prefixWord ++ tailWord_2717239) baseStart_2717239 baseEnd_2717239 := by
    simpa [prefixWord, tailWord_2717239, baseEnd_2717239] using wordTrace_append hprefix tailTrace_2717239
  have hstable : (prefixWord ++ tailWord_2717239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717239).length < 2 ^ (prefixWord ++ tailWord_2717239).sum := by decide
  have hdescent : baseEnd_2717239 < baseStart_2717239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717290 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_2717290 : Nat := 118140960795 + 2717290 * 2 ^ 59
def prefixEnd_2717290 : Nat := 4983230072969 + 3 ^ 40 * 2717290 * 2
def baseEnd_2717290 : Nat := 1395275847655778824078417

theorem tailTrace_2717290 : CollatzResearch.WordTrace tailWord_2717290 prefixEnd_2717290 1395275847655778824078417 := by
  unfold tailWord_2717290
  simp only [CollatzResearch.WordTrace]
  refine ⟨24776927081432470257529331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66071805550486587353411549 24776927081432470257529331)
  ·
    refine ⟨37165390622148705386293997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24776927081432470257529331 37165390622148705386293997)
    ·
      refine ⟨13937021483305764519860249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37165390622148705386293997 13937021483305764519860249)
      ·
        refine ⟨10452766112479323389895187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13937021483305764519860249 10452766112479323389895187)
        ·
          refine ⟨15679149168718985084842781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10452766112479323389895187 15679149168718985084842781)
          ·
            refine ⟨5879680938269619406816043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15679149168718985084842781 5879680938269619406816043)
            ·
              refine ⟨8819521407404429110224065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5879680938269619406816043 8819521407404429110224065)
              ·
                refine ⟨6614641055553321832668049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8819521407404429110224065 6614641055553321832668049)
                ·
                  refine ⟨4960980791664991374501037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6614641055553321832668049 4960980791664991374501037)
                  ·
                    refine ⟨1860367796874371765437889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4960980791664991374501037 1860367796874371765437889)
                    ·
                      refine ⟨1395275847655778824078417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860367796874371765437889 1395275847655778824078417)
                      ·
                        rfl

theorem cell23_2717290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_2717290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717290 prefixEnd_2717290 := by exact prefixLift 2717290
  have htrace : WordTrace (prefixWord ++ tailWord_2717290) baseStart_2717290 baseEnd_2717290 := by
    simpa [prefixWord, tailWord_2717290, baseEnd_2717290] using wordTrace_append hprefix tailTrace_2717290
  have hstable : (prefixWord ++ tailWord_2717290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717290).length < 2 ^ (prefixWord ++ tailWord_2717290).sum := by decide
  have hdescent : baseEnd_2717290 < baseStart_2717290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717320 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2717320 : Nat := 118140960795 + 2717320 * 2 ^ 59
def prefixEnd_2717320 : Nat := 4983230072969 + 3 ^ 40 * 2717320 * 2
def baseEnd_2717320 : Nat := 1395291252075413706703279

theorem tailTrace_2717320 : CollatzResearch.WordTrace tailWord_2717320 prefixEnd_2717320 1395291252075413706703279 := by
  unfold tailWord_2717320
  simp only [CollatzResearch.WordTrace]
  refine ⟨49554401257810598076854707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66072535010414130769139609 49554401257810598076854707)
  ·
    refine ⟨74331601886715897115282061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49554401257810598076854707 74331601886715897115282061)
    ·
      refine ⟨27874350707518461418230773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74331601886715897115282061 27874350707518461418230773)
      ·
        refine ⟨2613220378829855757959135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27874350707518461418230773 2613220378829855757959135)
        ·
          refine ⟨3919830568244783636938703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613220378829855757959135 3919830568244783636938703)
          ·
            refine ⟨5879745852367175455408055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919830568244783636938703 5879745852367175455408055)
            ·
              refine ⟨8819618778550763183112083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5879745852367175455408055 8819618778550763183112083)
              ·
                refine ⟨13229428167826144774668125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8819618778550763183112083 13229428167826144774668125)
                ·
                  refine ⟨4961035562934804290500547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13229428167826144774668125 4961035562934804290500547)
                  ·
                    refine ⟨7441553344402206435750821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4961035562934804290500547 7441553344402206435750821)
                    ·
                      refine ⟨1395291252075413706703279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7441553344402206435750821 1395291252075413706703279)
                      ·
                        rfl

theorem cell23_2717320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2717320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717320 prefixEnd_2717320 := by exact prefixLift 2717320
  have htrace : WordTrace (prefixWord ++ tailWord_2717320) baseStart_2717320 baseEnd_2717320 := by
    simpa [prefixWord, tailWord_2717320, baseEnd_2717320] using wordTrace_append hprefix tailTrace_2717320
  have hstable : (prefixWord ++ tailWord_2717320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717320).length < 2 ^ (prefixWord ++ tailWord_2717320).sum := by decide
  have hdescent : baseEnd_2717320 < baseStart_2717320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717326 : List Nat := [4, 1, 1, 3, 1, 2, 2, 9]
def baseStart_2717326 : Nat := 118140960795 + 2717326 * 2 ^ 59
def prefixEnd_2717326 : Nat := 4983230072969 + 3 ^ 40 * 2717326 * 2
def baseEnd_2717326 : Nat := 51677567887382988267713

theorem tailTrace_2717326 : CollatzResearch.WordTrace tailWord_2717326 prefixEnd_2717326 51677567887382988267713 := by
  unfold tailWord_2717326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12388627669199932397303479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66072680902399639452285221 12388627669199932397303479)
  ·
    refine ⟨18582941503799898595955219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12388627669199932397303479 18582941503799898595955219)
    ·
      refine ⟨27874412255699847893932829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18582941503799898595955219 27874412255699847893932829)
      ·
        refine ⟨10452904595887442960224811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27874412255699847893932829 10452904595887442960224811)
        ·
          refine ⟨15679356893831164440337217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10452904595887442960224811 15679356893831164440337217)
          ·
            refine ⟨11759517670373373330252913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15679356893831164440337217 11759517670373373330252913)
            ·
              refine ⟨8819638252780029997689685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11759517670373373330252913 8819638252780029997689685)
              ·
                refine ⟨51677567887382988267713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8819638252780029997689685 51677567887382988267713)
                ·
                  rfl

theorem cell23_2717326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_2717326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717326 prefixEnd_2717326 := by exact prefixLift 2717326
  have htrace : WordTrace (prefixWord ++ tailWord_2717326) baseStart_2717326 baseEnd_2717326 := by
    simpa [prefixWord, tailWord_2717326, baseEnd_2717326] using wordTrace_append hprefix tailTrace_2717326
  have hstable : (prefixWord ++ tailWord_2717326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717326).length < 2 ^ (prefixWord ++ tailWord_2717326).sum := by decide
  have hdescent : baseEnd_2717326 < baseStart_2717326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717340 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2717340 : Nat := 118140960795 + 2717340 * 2 ^ 59
def prefixEnd_2717340 : Nat := 4983230072969 + 3 ^ 40 * 2717340 * 2
def baseEnd_2717340 : Nat := 1395301521688503628453187

theorem tailTrace_2717340 : CollatzResearch.WordTrace tailWord_2717340 prefixEnd_2717340 1395301521688503628453187 := by
  unfold tailWord_2717340
  simp only [CollatzResearch.WordTrace]
  refine ⟨49554765987774369784718737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66073021317032493046291649 49554765987774369784718737)
  ·
    refine ⟨37166074490830777338539053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49554765987774369784718737 37166074490830777338539053)
    ·
      refine ⟨13937277934061541501952145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37166074490830777338539053 13937277934061541501952145)
      ·
        refine ⟨10452958450546156126464109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13937277934061541501952145 10452958450546156126464109)
        ·
          refine ⟨3919859418954808547424041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10452958450546156126464109 3919859418954808547424041)
          ·
            refine ⟨2939894564216106410568031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3919859418954808547424041 2939894564216106410568031)
            ·
              refine ⟨4409841846324159615852047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2939894564216106410568031 4409841846324159615852047)
              ·
                refine ⟨6614762769486239423778071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4409841846324159615852047 6614762769486239423778071)
                ·
                  refine ⟨9922144154229359135667107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6614762769486239423778071 9922144154229359135667107)
                  ·
                    refine ⟨14883216231344038703500661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9922144154229359135667107 14883216231344038703500661)
                    ·
                      refine ⟨1395301521688503628453187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14883216231344038703500661 1395301521688503628453187)
                      ·
                        rfl

theorem cell23_2717340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2717340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717340 prefixEnd_2717340 := by exact prefixLift 2717340
  have htrace : WordTrace (prefixWord ++ tailWord_2717340) baseStart_2717340 baseEnd_2717340 := by
    simpa [prefixWord, tailWord_2717340, baseEnd_2717340] using wordTrace_append hprefix tailTrace_2717340
  have hstable : (prefixWord ++ tailWord_2717340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717340).length < 2 ^ (prefixWord ++ tailWord_2717340).sum := by decide
  have hdescent : baseEnd_2717340 < baseStart_2717340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717343 : List Nat := [1, 1, 2, 7, 2, 10]
def baseStart_2717343 : Nat := 118140960795 + 2717343 * 2 ^ 59
def prefixEnd_2717343 : Nat := 4983230072969 + 3 ^ 40 * 2717343 * 2
def baseEnd_2717343 : Nat := 5741987910001922291011

theorem tailTrace_2717343 : CollatzResearch.WordTrace tailWord_2717343 prefixEnd_2717343 5741987910001922291011 := by
  unfold tailWord_2717343
  simp only [CollatzResearch.WordTrace]
  refine ⟨99109641394537871081796683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66073094263025247387864455 99109641394537871081796683)
  ·
    refine ⟨148664462091806806622695025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99109641394537871081796683 148664462091806806622695025)
    ·
      refine ⟨111498346568855104967021269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148664462091806806622695025 111498346568855104967021269)
      ·
        refine ⟨2613242497707541522664561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 111498346568855104967021269 2613242497707541522664561)
        ·
          refine ⟨1959931873280656141998421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2613242497707541522664561 1959931873280656141998421)
          ·
            refine ⟨5741987910001922291011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1959931873280656141998421 5741987910001922291011)
            ·
              rfl

theorem cell23_2717343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 10].length) (baseStart_2717343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717343 prefixEnd_2717343 := by exact prefixLift 2717343
  have htrace : WordTrace (prefixWord ++ tailWord_2717343) baseStart_2717343 baseEnd_2717343 := by
    simpa [prefixWord, tailWord_2717343, baseEnd_2717343] using wordTrace_append hprefix tailTrace_2717343
  have hstable : (prefixWord ++ tailWord_2717343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717343).length < 2 ^ (prefixWord ++ tailWord_2717343).sum := by decide
  have hdescent : baseEnd_2717343 < baseStart_2717343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717363 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 5, 3, 2]
def baseStart_2717363 : Nat := 118140960795 + 2717363 * 2 ^ 59
def prefixEnd_2717363 : Nat := 4983230072969 + 3 ^ 40 * 2717363 * 2
def baseEnd_2717363 : Nat := 1395313331743557038465581

theorem tailTrace_2717363 : CollatzResearch.WordTrace tailWord_2717363 prefixEnd_2717363 1395313331743557038465581 := by
  unfold tailWord_2717363
  simp only [CollatzResearch.WordTrace]
  refine ⟨99110370854465414497524743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66073580569643609665016495 99110370854465414497524743)
  ·
    refine ⟨148665556281698121746287115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99110370854465414497524743 148665556281698121746287115)
    ·
      refine ⟨222998334422547182619430673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148665556281698121746287115 222998334422547182619430673)
      ·
        refine ⟨167248750816910386964573005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222998334422547182619430673 167248750816910386964573005)
        ·
          refine ⟨62718281556341395111714877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167248750816910386964573005 62718281556341395111714877)
          ·
            refine ⟨23519355583628023166893079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62718281556341395111714877 23519355583628023166893079)
            ·
              refine ⟨35279033375442034750339619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23519355583628023166893079 35279033375442034750339619)
              ·
                refine ⟨52918550063163052125509429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35279033375442034750339619 52918550063163052125509429)
                ·
                  refine ⟨4961114068421536136766509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52918550063163052125509429 4961114068421536136766509)
                  ·
                    refine ⟨1860417775658076051287441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4961114068421536136766509 1860417775658076051287441)
                    ·
                      refine ⟨1395313331743557038465581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860417775658076051287441 1395313331743557038465581)
                      ·
                        rfl

theorem cell23_2717363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 3, 2].length) (baseStart_2717363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717363 prefixEnd_2717363 := by exact prefixLift 2717363
  have htrace : WordTrace (prefixWord ++ tailWord_2717363) baseStart_2717363 baseEnd_2717363 := by
    simpa [prefixWord, tailWord_2717363, baseEnd_2717363] using wordTrace_append hprefix tailTrace_2717363
  have hstable : (prefixWord ++ tailWord_2717363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717363).length < 2 ^ (prefixWord ++ tailWord_2717363).sum := by decide
  have hdescent : baseEnd_2717363 < baseStart_2717363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717370 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3]
def baseStart_2717370 : Nat := 118140960795 + 2717370 * 2 ^ 59
def prefixEnd_2717370 : Nat := 4983230072969 + 3 ^ 40 * 2717370 * 2
def baseEnd_2717370 : Nat := 1395316926108138511078049

theorem tailTrace_2717370 : CollatzResearch.WordTrace tailWord_2717370 prefixEnd_2717370 1395316926108138511078049 := by
  unfold tailWord_2717370
  simp only [CollatzResearch.WordTrace]
  refine ⟨24777656541360013673257391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66073750776960036462019709 24777656541360013673257391)
  ·
    refine ⟨37166484812040020509886087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24777656541360013673257391 37166484812040020509886087)
    ·
      refine ⟨55749727218060030764829131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37166484812040020509886087 55749727218060030764829131)
      ·
        refine ⟨83624590827090046147243697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55749727218060030764829131 83624590827090046147243697)
        ·
          refine ⟨62718443120317534610432773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83624590827090046147243697 62718443120317534610432773)
          ·
            refine ⟨11759708085059537739456145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62718443120317534610432773 11759708085059537739456145)
            ·
              refine ⟨8819781063794653304592109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11759708085059537739456145 8819781063794653304592109)
              ·
                refine ⟨3307417898922994989222041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8819781063794653304592109 3307417898922994989222041)
                ·
                  refine ⟨2480563424192246241916531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3307417898922994989222041 2480563424192246241916531)
                  ·
                    refine ⟨3720845136288369362874797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2480563424192246241916531 3720845136288369362874797)
                    ·
                      refine ⟨1395316926108138511078049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3720845136288369362874797 1395316926108138511078049)
                      ·
                        rfl

theorem cell23_2717370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_2717370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717370 prefixEnd_2717370 := by exact prefixLift 2717370
  have htrace : WordTrace (prefixWord ++ tailWord_2717370) baseStart_2717370 baseEnd_2717370 := by
    simpa [prefixWord, tailWord_2717370, baseEnd_2717370] using wordTrace_append hprefix tailTrace_2717370
  have hstable : (prefixWord ++ tailWord_2717370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717370).length < 2 ^ (prefixWord ++ tailWord_2717370).sum := by decide
  have hdescent : baseEnd_2717370 < baseStart_2717370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717376 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_2717376 : Nat := 118140960795 + 2717376 * 2 ^ 59
def prefixEnd_2717376 : Nat := 4983230072969 + 3 ^ 40 * 2717376 * 2
def baseEnd_2717376 : Nat := 1395320006992065487603021

theorem tailTrace_2717376 : CollatzResearch.WordTrace tailWord_2717376 prefixEnd_2717376 1395320006992065487603021 := by
  unfold tailWord_2717376
  simp only [CollatzResearch.WordTrace]
  refine ⟨49555422501709158858873991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66073896668945545145165321 49555422501709158858873991)
  ·
    refine ⟨74333133752563738288310987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49555422501709158858873991 74333133752563738288310987)
    ·
      refine ⟨111499700628845607432466481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74333133752563738288310987 111499700628845607432466481)
      ·
        refine ⟨83624775471634205574349861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111499700628845607432466481 83624775471634205574349861)
        ·
          refine ⟨15679645400931413545190599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83624775471634205574349861 15679645400931413545190599)
          ·
            refine ⟨23519468101397120317785899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15679645400931413545190599 23519468101397120317785899)
            ·
              refine ⟨35279202152095680476678849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23519468101397120317785899 35279202152095680476678849)
              ·
                refine ⟨26459401614071760357509137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35279202152095680476678849 26459401614071760357509137)
                ·
                  refine ⟨19844551210553820268131853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26459401614071760357509137 19844551210553820268131853)
                  ·
                    refine ⟨7441706703957682600549445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19844551210553820268131853 7441706703957682600549445)
                    ·
                      refine ⟨1395320006992065487603021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7441706703957682600549445 1395320006992065487603021)
                      ·
                        rfl

theorem cell23_2717376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_2717376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717376 prefixEnd_2717376 := by exact prefixLift 2717376
  have htrace : WordTrace (prefixWord ++ tailWord_2717376) baseStart_2717376 baseEnd_2717376 := by
    simpa [prefixWord, tailWord_2717376, baseEnd_2717376] using wordTrace_append hprefix tailTrace_2717376
  have hstable : (prefixWord ++ tailWord_2717376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717376).length < 2 ^ (prefixWord ++ tailWord_2717376).sum := by decide
  have hdescent : baseEnd_2717376 < baseStart_2717376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717380 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_2717380 : Nat := 118140960795 + 2717380 * 2 ^ 59
def prefixEnd_2717380 : Nat := 4983230072969 + 3 ^ 40 * 2717380 * 2
def baseEnd_2717380 : Nat := 1395322060914683471953003

theorem tailTrace_2717380 : CollatzResearch.WordTrace tailWord_2717380 prefixEnd_2717380 1395322060914683471953003 := by
  unfold tailWord_2717380
  simp only [CollatzResearch.WordTrace]
  refine ⟨49555495447701913200446797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66073993930269217600595729 49555495447701913200446797)
  ·
    refine ⟨18583310792888217450167549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49555495447701913200446797 18583310792888217450167549)
    ·
      refine ⟨6968741547333081543812831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18583310792888217450167549 6968741547333081543812831)
      ·
        refine ⟨10453112320999622315719247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6968741547333081543812831 10453112320999622315719247)
        ·
          refine ⟨15679668481499433473578871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10453112320999622315719247 15679668481499433473578871)
          ·
            refine ⟨23519502722249150210368307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15679668481499433473578871 23519502722249150210368307)
            ·
              refine ⟨35279254083373725315552461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23519502722249150210368307 35279254083373725315552461)
              ·
                refine ⟨13229720281265146993332173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35279254083373725315552461 13229720281265146993332173)
                ·
                  refine ⟨4961145105474430122499565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13229720281265146993332173 4961145105474430122499565)
                  ·
                    refine ⟨1860429414552911295937337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4961145105474430122499565 1860429414552911295937337)
                    ·
                      refine ⟨1395322060914683471953003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860429414552911295937337 1395322060914683471953003)
                      ·
                        rfl

theorem cell23_2717380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_2717380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717380 prefixEnd_2717380 := by exact prefixLift 2717380
  have htrace : WordTrace (prefixWord ++ tailWord_2717380) baseStart_2717380 baseEnd_2717380 := by
    simpa [prefixWord, tailWord_2717380, baseEnd_2717380] using wordTrace_append hprefix tailTrace_2717380
  have hstable : (prefixWord ++ tailWord_2717380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717380).length < 2 ^ (prefixWord ++ tailWord_2717380).sum := by decide
  have hdescent : baseEnd_2717380 < baseStart_2717380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717450 : List Nat := [3, 1, 2, 2, 1, 3, 3, 3, 5]
def baseStart_2717450 : Nat := 118140960795 + 2717450 * 2 ^ 59
def prefixEnd_2717450 : Nat := 4983230072969 + 3 ^ 40 * 2717450 * 2
def baseEnd_2717450 : Nat := 155039778284499799786409

theorem tailTrace_2717450 : CollatzResearch.WordTrace tailWord_2717450 prefixEnd_2717450 155039778284499799786409 := by
  unfold tailWord_2717450
  simp only [CollatzResearch.WordTrace]
  refine ⟨24778386001287557088985451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66075696003433485570627869 24778386001287557088985451)
  ·
    refine ⟨37167579001931335633478177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24778386001287557088985451 37167579001931335633478177)
    ·
      refine ⟨27875684251448501725108633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37167579001931335633478177 27875684251448501725108633)
      ·
        refine ⟨20906763188586376293831475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27875684251448501725108633 20906763188586376293831475)
        ·
          refine ⟨31360144782879564440747213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20906763188586376293831475 31360144782879564440747213)
          ·
            refine ⟨11760054293579836665280205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31360144782879564440747213 11760054293579836665280205)
            ·
              refine ⟨4410020360092438749480077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11760054293579836665280205 4410020360092438749480077)
              ·
                refine ⟨1653757635034664531055029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4410020360092438749480077 1653757635034664531055029)
                ·
                  refine ⟨155039778284499799786409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1653757635034664531055029 155039778284499799786409)
                  ·
                    rfl

theorem cell23_2717450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_2717450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717450 prefixEnd_2717450 := by exact prefixLift 2717450
  have htrace : WordTrace (prefixWord ++ tailWord_2717450) baseStart_2717450 baseEnd_2717450 := by
    simpa [prefixWord, tailWord_2717450, baseEnd_2717450] using wordTrace_append hprefix tailTrace_2717450
  have hstable : (prefixWord ++ tailWord_2717450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717450).length < 2 ^ (prefixWord ++ tailWord_2717450).sum := by decide
  have hdescent : baseEnd_2717450 < baseStart_2717450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717463 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 4, 5]
def baseStart_2717463 : Nat := 118140960795 + 2717463 * 2 ^ 59
def prefixEnd_2717463 : Nat := 4983230072969 + 3 ^ 40 * 2717463 * 2
def baseEnd_2717463 : Nat := 465121559936335549071707

theorem tailTrace_2717463 : CollatzResearch.WordTrace tailWord_2717463 prefixEnd_2717463 465121559936335549071707 := by
  unfold tailWord_2717463
  simp only [CollatzResearch.WordTrace]
  refine ⟨99114018154103131576165043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66076012102735421050776695 99114018154103131576165043)
  ·
    refine ⟨148671027231154697364247565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99114018154103131576165043 148671027231154697364247565)
    ·
      refine ⟨55751635211683011511592837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148671027231154697364247565 55751635211683011511592837)
      ·
        refine ⟨10453431602190564658423657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55751635211683011511592837 10453431602190564658423657)
        ·
          refine ⟨7840073701642923493817743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10453431602190564658423657 7840073701642923493817743)
          ·
            refine ⟨11760110552464385240726615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7840073701642923493817743 11760110552464385240726615)
            ·
              refine ⟨17640165828696577861089923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11760110552464385240726615 17640165828696577861089923)
              ·
                refine ⟨26460248743044866791634885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17640165828696577861089923 26460248743044866791634885)
                ·
                  refine ⟨4961296639320912523431541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26460248743044866791634885 4961296639320912523431541)
                  ·
                    refine ⟨465121559936335549071707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4961296639320912523431541 465121559936335549071707)
                    ·
                      rfl

theorem cell23_2717463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_2717463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717463 prefixEnd_2717463 := by exact prefixLift 2717463
  have htrace : WordTrace (prefixWord ++ tailWord_2717463) baseStart_2717463 baseEnd_2717463 := by
    simpa [prefixWord, tailWord_2717463, baseEnd_2717463] using wordTrace_append hprefix tailTrace_2717463
  have hstable : (prefixWord ++ tailWord_2717463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717463).length < 2 ^ (prefixWord ++ tailWord_2717463).sum := by decide
  have hdescent : baseEnd_2717463 < baseStart_2717463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717473 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2717473 : Nat := 118140960795 + 2717473 * 2 ^ 59
def prefixEnd_2717473 : Nat := 4983230072969 + 3 ^ 40 * 2717473 * 2
def baseEnd_2717473 : Nat := 1395369814615551608090075

theorem tailTrace_2717473 : CollatzResearch.WordTrace tailWord_2717473 prefixEnd_2717473 1395369814615551608090075 := by
  unfold tailWord_2717473
  simp only [CollatzResearch.WordTrace]
  refine ⟨99114382884066903284029073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66076255256044602189352715 99114382884066903284029073)
  ·
    refine ⟨74335787163050177463021805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99114382884066903284029073 74335787163050177463021805)
    ·
      refine ⟨27875920186143816548633177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74335787163050177463021805 27875920186143816548633177)
      ·
        refine ⟨20906940139607862411474883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27875920186143816548633177 20906940139607862411474883)
        ·
          refine ⟨31360410209411793617212325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20906940139607862411474883 31360410209411793617212325)
          ·
            refine ⟨5880076914264711303227311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31360410209411793617212325 5880076914264711303227311)
            ·
              refine ⟨8820115371397066954840967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880076914264711303227311 8820115371397066954840967)
              ·
                refine ⟨13230173057095600432261451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8820115371397066954840967 13230173057095600432261451)
                ·
                  refine ⟨19845259585643400648392177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13230173057095600432261451 19845259585643400648392177)
                  ·
                    refine ⟨14883944689232550486294133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19845259585643400648392177 14883944689232550486294133)
                    ·
                      refine ⟨1395369814615551608090075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14883944689232550486294133 1395369814615551608090075)
                      ·
                        rfl

theorem cell23_2717473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2717473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717473 prefixEnd_2717473 := by exact prefixLift 2717473
  have htrace : WordTrace (prefixWord ++ tailWord_2717473) baseStart_2717473 baseEnd_2717473 := by
    simpa [prefixWord, tailWord_2717473, baseEnd_2717473] using wordTrace_append hprefix tailTrace_2717473
  have hstable : (prefixWord ++ tailWord_2717473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717473).length < 2 ^ (prefixWord ++ tailWord_2717473).sum := by decide
  have hdescent : baseEnd_2717473 < baseStart_2717473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717497 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 2, 5]
def baseStart_2717497 : Nat := 118140960795 + 2717497 * 2 ^ 59
def prefixEnd_2717497 : Nat := 4983230072969 + 3 ^ 40 * 2717497 * 2
def baseEnd_2717497 : Nat := 465127379383753171396655

theorem tailTrace_2717497 : CollatzResearch.WordTrace tailWord_2717497 prefixEnd_2717497 465127379383753171396655 := by
  unfold tailWord_2717497
  simp only [CollatzResearch.WordTrace]
  refine ⟨99115258235979955382902745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66076838823986636921935163 99115258235979955382902745)
  ·
    refine ⟨74336443676984966537177059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99115258235979955382902745 74336443676984966537177059)
    ·
      refine ⟨111504665515477449805765589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74336443676984966537177059 111504665515477449805765589)
      ·
        refine ⟨2613390598019002729822631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 111504665515477449805765589 2613390598019002729822631)
        ·
          refine ⟨3920085897028504094733947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613390598019002729822631 3920085897028504094733947)
          ·
            refine ⟨5880128845542756142100921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920085897028504094733947 5880128845542756142100921)
            ·
              refine ⟨4410096634157067106575691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5880128845542756142100921 4410096634157067106575691)
              ·
                refine ⟨6615144951235600659863537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4410096634157067106575691 6615144951235600659863537)
                ·
                  refine ⟨4961358713426700494897653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6615144951235600659863537 4961358713426700494897653)
                  ·
                    refine ⟨465127379383753171396655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4961358713426700494897653 465127379383753171396655)
                    ·
                      rfl

theorem cell23_2717497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 5].length) (baseStart_2717497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717497 prefixEnd_2717497 := by exact prefixLift 2717497
  have htrace : WordTrace (prefixWord ++ tailWord_2717497) baseStart_2717497 baseEnd_2717497 := by
    simpa [prefixWord, tailWord_2717497, baseEnd_2717497] using wordTrace_append hprefix tailTrace_2717497
  have hstable : (prefixWord ++ tailWord_2717497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717497).length < 2 ^ (prefixWord ++ tailWord_2717497).sum := by decide
  have hdescent : baseEnd_2717497 < baseStart_2717497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717517 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2717517 : Nat := 118140960795 + 2717517 * 2 ^ 59
def prefixEnd_2717517 : Nat := 4983230072969 + 3 ^ 40 * 2717517 * 2
def baseEnd_2717517 : Nat := 1395392407764349435939873

theorem tailTrace_2717517 : CollatzResearch.WordTrace tailWord_2717517 prefixEnd_2717517 1395392407764349435939873 := by
  unfold tailWord_2717517
  simp only [CollatzResearch.WordTrace]
  refine ⟨99115987695907498798630805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66077325130604999199087203 99115987695907498798630805)
  ·
    refine ⟨4646061923245664006185819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99115987695907498798630805 4646061923245664006185819)
    ·
      refine ⟨6969092884868496009278729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4646061923245664006185819 6969092884868496009278729)
      ·
        refine ⟨5226819663651372006959047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6969092884868496009278729 5226819663651372006959047)
        ·
          refine ⟨7840229495477058010438571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5226819663651372006959047 7840229495477058010438571)
          ·
            refine ⟨11760344243215587015657857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7840229495477058010438571 11760344243215587015657857)
            ·
              refine ⟨8820258182411690261743393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11760344243215587015657857 8820258182411690261743393)
              ·
                refine ⟨6615193636808767696307545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8820258182411690261743393 6615193636808767696307545)
                ·
                  refine ⟨4961395227606575772230659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6615193636808767696307545 4961395227606575772230659)
                  ·
                    refine ⟨7442092841409863658345989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4961395227606575772230659 7442092841409863658345989)
                    ·
                      refine ⟨1395392407764349435939873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7442092841409863658345989 1395392407764349435939873)
                      ·
                        rfl

theorem cell23_2717517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2717517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717517 prefixEnd_2717517 := by exact prefixLift 2717517
  have htrace : WordTrace (prefixWord ++ tailWord_2717517) baseStart_2717517 baseEnd_2717517 := by
    simpa [prefixWord, tailWord_2717517, baseEnd_2717517] using wordTrace_append hprefix tailTrace_2717517
  have hstable : (prefixWord ++ tailWord_2717517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717517).length < 2 ^ (prefixWord ++ tailWord_2717517).sum := by decide
  have hdescent : baseEnd_2717517 < baseStart_2717517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717553 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 3, 5]
def baseStart_2717553 : Nat := 118140960795 + 2717553 * 2 ^ 59
def prefixEnd_2717553 : Nat := 4983230072969 + 3 ^ 40 * 2717553 * 2
def baseEnd_2717553 : Nat := 465136964355970431696569

theorem tailTrace_2717553 : CollatzResearch.WordTrace tailWord_2717553 prefixEnd_2717553 465136964355970431696569 := by
  unfold tailWord_2717553
  simp only [CollatzResearch.WordTrace]
  refine ⟨99117300723777076946941313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66078200482518051297960875 99117300723777076946941313)
  ·
    refine ⟨74337975542832807710205985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99117300723777076946941313 74337975542832807710205985)
    ·
      refine ⟨55753481657124605782654489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74337975542832807710205985 55753481657124605782654489)
      ·
        refine ⟨41815111242843454336990867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55753481657124605782654489 41815111242843454336990867)
        ·
          refine ⟨62722666864265181505486301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41815111242843454336990867 62722666864265181505486301)
          ·
            refine ⟨23521000074099443064557363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62722666864265181505486301 23521000074099443064557363)
            ·
              refine ⟨35281500111149164596836045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23521000074099443064557363 35281500111149164596836045)
              ·
                refine ⟨13230562541680936723813517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35281500111149164596836045 13230562541680936723813517)
                ·
                  refine ⟨4961460953130351271430069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13230562541680936723813517 4961460953130351271430069)
                  ·
                    refine ⟨465136964355970431696569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4961460953130351271430069 465136964355970431696569)
                    ·
                      rfl

theorem cell23_2717553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_2717553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717553 prefixEnd_2717553 := by exact prefixLift 2717553
  have htrace : WordTrace (prefixWord ++ tailWord_2717553) baseStart_2717553 baseEnd_2717553 := by
    simpa [prefixWord, tailWord_2717553, baseEnd_2717553] using wordTrace_append hprefix tailTrace_2717553
  have hstable : (prefixWord ++ tailWord_2717553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717553).length < 2 ^ (prefixWord ++ tailWord_2717553).sum := by decide
  have hdescent : baseEnd_2717553 < baseStart_2717553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717593 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_2717593 : Nat := 118140960795 + 2717593 * 2 ^ 59
def prefixEnd_2717593 : Nat := 4983230072969 + 3 ^ 40 * 2717593 * 2
def baseEnd_2717593 : Nat := 1395431432294091138589523

theorem tailTrace_2717593 : CollatzResearch.WordTrace tailWord_2717593 prefixEnd_2717593 1395431432294091138589523 := by
  unfold tailWord_2717593
  simp only [CollatzResearch.WordTrace]
  refine ⟨99118759643632163778397433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66079173095754775852264955 99118759643632163778397433)
  ·
    refine ⟨74339069732724122833798075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99118759643632163778397433 74339069732724122833798075)
    ·
      refine ⟨111508604599086184250697113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74339069732724122833798075 111508604599086184250697113)
      ·
        refine ⟨83631453449314638188022835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111508604599086184250697113 83631453449314638188022835)
        ·
          refine ⟨125447180173971957282034253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83631453449314638188022835 125447180173971957282034253)
          ·
            refine ⟨47042692565239483980762845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125447180173971957282034253 47042692565239483980762845)
            ·
              refine ⟨17641009711964806492786067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47042692565239483980762845 17641009711964806492786067)
              ·
                refine ⟨26461514567947209739179101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17641009711964806492786067 26461514567947209739179101)
                ·
                  refine ⟨9923067962980203652192163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26461514567947209739179101 9923067962980203652192163)
                  ·
                    refine ⟨14884601944470305478288245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9923067962980203652192163 14884601944470305478288245)
                    ·
                      refine ⟨1395431432294091138589523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14884601944470305478288245 1395431432294091138589523)
                      ·
                        rfl

theorem cell23_2717593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_2717593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717593 prefixEnd_2717593 := by exact prefixLift 2717593
  have htrace : WordTrace (prefixWord ++ tailWord_2717593) baseStart_2717593 baseEnd_2717593 := by
    simpa [prefixWord, tailWord_2717593, baseEnd_2717593] using wordTrace_append hprefix tailTrace_2717593
  have hstable : (prefixWord ++ tailWord_2717593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717593).length < 2 ^ (prefixWord ++ tailWord_2717593).sum := by decide
  have hdescent : baseEnd_2717593 < baseStart_2717593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717607 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_2717607 : Nat := 118140960795 + 2717607 * 2 ^ 59
def prefixEnd_2717607 : Nat := 4983230072969 + 3 ^ 40 * 2717607 * 2
def baseEnd_2717607 : Nat := 1395438621023254083814459

theorem tailTrace_2717607 : CollatzResearch.WordTrace tailWord_2717607 prefixEnd_2717607 1395438621023254083814459 := by
  unfold tailWord_2717607
  simp only [CollatzResearch.WordTrace]
  refine ⟨99119270265581444169407075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66079513510387629446271383 99119270265581444169407075)
  ·
    refine ⟨148678905398372166254110613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99119270265581444169407075 148678905398372166254110613)
    ·
      refine ⟨6969323690548695293161435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 148678905398372166254110613 6969323690548695293161435)
      ·
        refine ⟨10453985535823042939742153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6969323690548695293161435 10453985535823042939742153)
        ·
          refine ⟨7840489151867282204806615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10453985535823042939742153 7840489151867282204806615)
          ·
            refine ⟨11760733727800923307209923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7840489151867282204806615 11760733727800923307209923)
            ·
              refine ⟨17641100591701384960814885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11760733727800923307209923 17641100591701384960814885)
              ·
                refine ⟨3307706360944009680152791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17641100591701384960814885 3307706360944009680152791)
                ·
                  refine ⟨4961559541416014520229187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307706360944009680152791 4961559541416014520229187)
                  ·
                    refine ⟨7442339312124021780343781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4961559541416014520229187 7442339312124021780343781)
                    ·
                      refine ⟨1395438621023254083814459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7442339312124021780343781 1395438621023254083814459)
                      ·
                        rfl

theorem cell23_2717607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_2717607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717607 prefixEnd_2717607 := by exact prefixLift 2717607
  have htrace : WordTrace (prefixWord ++ tailWord_2717607) baseStart_2717607 baseEnd_2717607 := by
    simpa [prefixWord, tailWord_2717607, baseEnd_2717607] using wordTrace_append hprefix tailTrace_2717607
  have hstable : (prefixWord ++ tailWord_2717607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717607).length < 2 ^ (prefixWord ++ tailWord_2717607).sum := by decide
  have hdescent : baseEnd_2717607 < baseStart_2717607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717630 : List Nat := [4, 2, 1, 1, 1, 5, 9]
def baseStart_2717630 : Nat := 118140960795 + 2717630 * 2 ^ 59
def prefixEnd_2717630 : Nat := 4983230072969 + 3 ^ 40 * 2717630 * 2
def baseEnd_2717630 : Nat := 17227783099732191281813

theorem tailTrace_2717630 : CollatzResearch.WordTrace tailWord_2717630 prefixEnd_2717630 17227783099732191281813 := by
  unfold tailWord_2717630
  simp only [CollatzResearch.WordTrace]
  refine ⟨12390013643062264887186793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66080072762998746064996229 12390013643062264887186793)
  ·
    refine ⟨9292510232296698665390095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12390013643062264887186793 9292510232296698665390095)
    ·
      refine ⟨13938765348445047998085143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9292510232296698665390095 13938765348445047998085143)
      ·
        refine ⟨20908148022667571997127715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13938765348445047998085143 20908148022667571997127715)
        ·
          refine ⟨31362222034001357995691573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20908148022667571997127715 31362222034001357995691573)
          ·
            refine ⟨2940208315687627312096085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31362222034001357995691573 2940208315687627312096085)
            ·
              refine ⟨17227783099732191281813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2940208315687627312096085 17227783099732191281813)
              ·
                rfl

theorem cell23_2717630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 9].length) (baseStart_2717630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717630 prefixEnd_2717630 := by exact prefixLift 2717630
  have htrace : WordTrace (prefixWord ++ tailWord_2717630) baseStart_2717630 baseEnd_2717630 := by
    simpa [prefixWord, tailWord_2717630, baseEnd_2717630] using wordTrace_append hprefix tailTrace_2717630
  have hstable : (prefixWord ++ tailWord_2717630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717630).length < 2 ^ (prefixWord ++ tailWord_2717630).sum := by decide
  have hdescent : baseEnd_2717630 < baseStart_2717630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717643 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 2, 7]
def baseStart_2717643 : Nat := 118140960795 + 2717643 * 2 ^ 59
def prefixEnd_2717643 : Nat := 4983230072969 + 3 ^ 40 * 2717643 * 2
def baseEnd_2717643 : Nat := 465152368775605314321431

theorem tailTrace_2717643 : CollatzResearch.WordTrace tailWord_2717643 prefixEnd_2717643 465152368775605314321431 := by
  unfold tailWord_2717643
  simp only [CollatzResearch.WordTrace]
  refine ⟨99120583293451022317717583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66080388862300681545145055 99120583293451022317717583)
  ·
    refine ⟨148680874940176533476576375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99120583293451022317717583 148680874940176533476576375)
    ·
      refine ⟨223021312410264800214864563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148680874940176533476576375 223021312410264800214864563)
      ·
        refine ⟨334531968615397200322296845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223021312410264800214864563 334531968615397200322296845)
        ·
          refine ⟨125449488230773950120861317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334531968615397200322296845 125449488230773950120861317)
          ·
            refine ⟨23521779043270115647661497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125449488230773950120861317 23521779043270115647661497)
            ·
              refine ⟨17641334282452586735746123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23521779043270115647661497 17641334282452586735746123)
              ·
                refine ⟨26462001423678880103619185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17641334282452586735746123 26462001423678880103619185)
                ·
                  refine ⟨19846501067759160077714389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26462001423678880103619185 19846501067759160077714389)
                  ·
                    refine ⟨465152368775605314321431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19846501067759160077714389 465152368775605314321431)
                    ·
                      rfl

theorem cell23_2717643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 7].length) (baseStart_2717643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717643 prefixEnd_2717643 := by exact prefixLift 2717643
  have htrace : WordTrace (prefixWord ++ tailWord_2717643) baseStart_2717643 baseEnd_2717643 := by
    simpa [prefixWord, tailWord_2717643, baseEnd_2717643] using wordTrace_append hprefix tailTrace_2717643
  have hstable : (prefixWord ++ tailWord_2717643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717643).length < 2 ^ (prefixWord ++ tailWord_2717643).sum := by decide
  have hdescent : baseEnd_2717643 < baseStart_2717643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717661 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2717661 : Nat := 118140960795 + 2717661 * 2 ^ 59
def prefixEnd_2717661 : Nat := 4983230072969 + 3 ^ 40 * 2717661 * 2
def baseEnd_2717661 : Nat := 1395466348978596872539211

theorem tailTrace_2717661 : CollatzResearch.WordTrace tailWord_2717661 prefixEnd_2717661 1395466348978596872539211 := by
  unfold tailWord_2717661
  simp only [CollatzResearch.WordTrace]
  refine ⟨99121239807385811391872837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66080826538257207594581891 99121239807385811391872837)
  ·
    refine ⟨18585232463884839635976157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99121239807385811391872837 18585232463884839635976157)
    ·
      refine ⟨6969462173956814863491059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18585232463884839635976157 6969462173956814863491059)
      ·
        refine ⟨10454193260935222295236589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6969462173956814863491059 10454193260935222295236589)
        ·
          refine ⟨3920322472850708360713721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10454193260935222295236589 3920322472850708360713721)
          ·
            refine ⟨2940241854638031270535291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3920322472850708360713721 2940241854638031270535291)
            ·
              refine ⟨4410362781957046905802937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940241854638031270535291 4410362781957046905802937)
              ·
                refine ⟨3307772086467785179352203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4410362781957046905802937 3307772086467785179352203)
                ·
                  refine ⟨4961658129701677769028305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307772086467785179352203 4961658129701677769028305)
                  ·
                    refine ⟨3721243597276258326771229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4961658129701677769028305 3721243597276258326771229)
                    ·
                      refine ⟨1395466348978596872539211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3721243597276258326771229 1395466348978596872539211)
                      ·
                        rfl

theorem cell23_2717661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2717661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717661 prefixEnd_2717661 := by exact prefixLift 2717661
  have htrace : WordTrace (prefixWord ++ tailWord_2717661) baseStart_2717661 baseEnd_2717661 := by
    simpa [prefixWord, tailWord_2717661, baseEnd_2717661] using wordTrace_append hprefix tailTrace_2717661
  have hstable : (prefixWord ++ tailWord_2717661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717661).length < 2 ^ (prefixWord ++ tailWord_2717661).sum := by decide
  have hdescent : baseEnd_2717661 < baseStart_2717661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717697 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_2717697 : Nat := 118140960795 + 2717697 * 2 ^ 59
def prefixEnd_2717697 : Nat := 4983230072969 + 3 ^ 40 * 2717697 * 2
def baseEnd_2717697 : Nat := 1395484834282158731689045

theorem tailTrace_2717697 : CollatzResearch.WordTrace tailWord_2717697 prefixEnd_2717697 1395484834282158731689045 := by
  unfold tailWord_2717697
  simp only [CollatzResearch.WordTrace]
  refine ⟨99122552835255389540183345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66081701890170259693455563 99122552835255389540183345)
  ·
    refine ⟨74341914626441542155137509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99122552835255389540183345 74341914626441542155137509)
    ·
      refine ⟨13939108992457789154088283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74341914626441542155137509 13939108992457789154088283)
      ·
        refine ⟨20908663488686683731132425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13939108992457789154088283 20908663488686683731132425)
        ·
          refine ⟨15681497616515012798349319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20908663488686683731132425 15681497616515012798349319)
          ·
            refine ⟨23522246424772519197523979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15681497616515012798349319 23522246424772519197523979)
            ·
              refine ⟨35283369637158778796285969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23522246424772519197523979 35283369637158778796285969)
              ·
                refine ⟨26462527227869084097214477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35283369637158778796285969 26462527227869084097214477)
                ·
                  refine ⟨9923447710450906536455429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26462527227869084097214477 9923447710450906536455429)
                  ·
                    refine ⟨1860646445709544975585393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9923447710450906536455429 1860646445709544975585393)
                    ·
                      refine ⟨1395484834282158731689045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860646445709544975585393 1395484834282158731689045)
                      ·
                        rfl

theorem cell23_2717697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_2717697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717697 prefixEnd_2717697 := by exact prefixLift 2717697
  have htrace : WordTrace (prefixWord ++ tailWord_2717697) baseStart_2717697 baseEnd_2717697 := by
    simpa [prefixWord, tailWord_2717697, baseEnd_2717697] using wordTrace_append hprefix tailTrace_2717697
  have hstable : (prefixWord ++ tailWord_2717697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717697).length < 2 ^ (prefixWord ++ tailWord_2717697).sum := by decide
  have hdescent : baseEnd_2717697 < baseStart_2717697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717720 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 7]
def baseStart_2717720 : Nat := 118140960795 + 2717720 * 2 ^ 59
def prefixEnd_2717720 : Nat := 4983230072969 + 3 ^ 40 * 2717720 * 2
def baseEnd_2717720 : Nat := 155055182704134682411271

theorem tailTrace_2717720 : CollatzResearch.WordTrace tailWord_2717720 prefixEnd_2717720 155055182704134682411271 := by
  unfold tailWord_2717720
  simp only [CollatzResearch.WordTrace]
  refine ⟨49561695857086032234135307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66082261142781376312180409 49561695857086032234135307)
  ·
    refine ⟨74342543785629048351202961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49561695857086032234135307 74342543785629048351202961)
    ·
      refine ⟨55756907839221786263402221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74342543785629048351202961 55756907839221786263402221)
      ·
        refine ⟨20908840439708169848775833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55756907839221786263402221 20908840439708169848775833)
        ·
          refine ⟨15681630329781127386581875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20908840439708169848775833 15681630329781127386581875)
          ·
            refine ⟨23522445494671691079872813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15681630329781127386581875 23522445494671691079872813)
            ·
              refine ⟨8820917060501884154952305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23522445494671691079872813 8820917060501884154952305)
              ·
                refine ⟨6615687795376413116214229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8820917060501884154952305 6615687795376413116214229)
                ·
                  refine ⟨155055182704134682411271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6615687795376413116214229 155055182704134682411271)
                  ·
                    rfl

theorem cell23_2717720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 7].length) (baseStart_2717720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717720 prefixEnd_2717720 := by exact prefixLift 2717720
  have htrace : WordTrace (prefixWord ++ tailWord_2717720) baseStart_2717720 baseEnd_2717720 := by
    simpa [prefixWord, tailWord_2717720, baseEnd_2717720] using wordTrace_append hprefix tailTrace_2717720
  have hstable : (prefixWord ++ tailWord_2717720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717720).length < 2 ^ (prefixWord ++ tailWord_2717720).sum := by decide
  have hdescent : baseEnd_2717720 < baseStart_2717720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717735 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_2717735 : Nat := 118140960795 + 2717735 * 2 ^ 59
def prefixEnd_2717735 : Nat := 4983230072969 + 3 ^ 40 * 2717735 * 2
def baseEnd_2717735 : Nat := 1395504346547029583013871

theorem tailTrace_2717735 : CollatzResearch.WordTrace tailWord_2717735 prefixEnd_2717735 1395504346547029583013871 := by
  unfold tailWord_2717735
  simp only [CollatzResearch.WordTrace]
  refine ⟨99123938809117722030066659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66082625872745148020044439 99123938809117722030066659)
  ·
    refine ⟨148685908213676583045099989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99123938809117722030066659 148685908213676583045099989)
    ·
      refine ⟨3484825973758044915119531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 148685908213676583045099989 3484825973758044915119531)
      ·
        refine ⟨5227238960637067372679297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484825973758044915119531 5227238960637067372679297)
        ·
          refine ⟨3920429220477800529509473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5227238960637067372679297 3920429220477800529509473)
          ·
            refine ⟨2940321915358350397132105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3920429220477800529509473 2940321915358350397132105)
            ·
              refine ⟨2205241436518762797849079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2940321915358350397132105 2205241436518762797849079)
              ·
                refine ⟨3307862154778144196773619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205241436518762797849079 3307862154778144196773619)
                ·
                  refine ⟨4961793232167216295160429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307862154778144196773619 4961793232167216295160429)
                  ·
                    refine ⟨1860672462062706110685161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4961793232167216295160429 1860672462062706110685161)
                    ·
                      refine ⟨1395504346547029583013871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860672462062706110685161 1395504346547029583013871)
                      ·
                        rfl

theorem cell23_2717735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_2717735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717735 prefixEnd_2717735 := by exact prefixLift 2717735
  have htrace : WordTrace (prefixWord ++ tailWord_2717735) baseStart_2717735 baseEnd_2717735 := by
    simpa [prefixWord, tailWord_2717735, baseEnd_2717735] using wordTrace_append hprefix tailTrace_2717735
  have hstable : (prefixWord ++ tailWord_2717735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717735).length < 2 ^ (prefixWord ++ tailWord_2717735).sum := by decide
  have hdescent : baseEnd_2717735 < baseStart_2717735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717748 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_2717748 : Nat := 118140960795 + 2717748 * 2 ^ 59
def prefixEnd_2717748 : Nat := 4983230072969 + 3 ^ 40 * 2717748 * 2
def baseEnd_2717748 : Nat := 1395511021795538032151311

theorem tailTrace_2717748 : CollatzResearch.WordTrace tailWord_2717748 prefixEnd_2717748 1395511021795538032151311 := by
  unfold tailWord_2717748
  simp only [CollatzResearch.WordTrace]
  refine ⟨49562206479035312625144949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66082941972047083500193265 49562206479035312625144949)
  ·
    refine ⟨4646456857409560558607339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49562206479035312625144949 4646456857409560558607339)
    ·
      refine ⟨6969685286114340837911009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4646456857409560558607339 6969685286114340837911009)
      ·
        refine ⟨5227263964585755628433257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6969685286114340837911009 5227263964585755628433257)
        ·
          refine ⟨3920447973439316721324943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5227263964585755628433257 3920447973439316721324943)
          ·
            refine ⟨5880671960158975081987415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920447973439316721324943 5880671960158975081987415)
            ·
              refine ⟨8821007940238462622981123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880671960158975081987415 8821007940238462622981123)
              ·
                refine ⟨13231511910357693934471685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8821007940238462622981123 13231511910357693934471685)
                ·
                  refine ⟨2480908483192067612713441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13231511910357693934471685 2480908483192067612713441)
                  ·
                    refine ⟨1860681362394050709535081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2480908483192067612713441 1860681362394050709535081)
                    ·
                      refine ⟨1395511021795538032151311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860681362394050709535081 1395511021795538032151311)
                      ·
                        rfl

theorem cell23_2717748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_2717748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717748 prefixEnd_2717748 := by exact prefixLift 2717748
  have htrace : WordTrace (prefixWord ++ tailWord_2717748) baseStart_2717748 baseEnd_2717748 := by
    simpa [prefixWord, tailWord_2717748, baseEnd_2717748] using wordTrace_append hprefix tailTrace_2717748
  have hstable : (prefixWord ++ tailWord_2717748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717748).length < 2 ^ (prefixWord ++ tailWord_2717748).sum := by decide
  have hdescent : baseEnd_2717748 < baseStart_2717748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717780 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_2717780 : Nat := 118140960795 + 2717780 * 2 ^ 59
def prefixEnd_2717780 : Nat := 4983230072969 + 3 ^ 40 * 2717780 * 2
def baseEnd_2717780 : Nat := 465175817725493968983721

theorem tailTrace_2717780 : CollatzResearch.WordTrace tailWord_2717780 prefixEnd_2717780 465175817725493968983721 := by
  unfold tailWord_2717780
  simp only [CollatzResearch.WordTrace]
  refine ⟨49562790046977347357727397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66083720062636463143636529 49562790046977347357727397)
  ·
    refine ⟨9293023133808252629573887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49562790046977347357727397 9293023133808252629573887)
    ·
      refine ⟨13939534700712378944360831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9293023133808252629573887 13939534700712378944360831)
      ·
        refine ⟨20909302051068568416541247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13939534700712378944360831 20909302051068568416541247)
        ·
          refine ⟨31363953076602852624811871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20909302051068568416541247 31363953076602852624811871)
          ·
            refine ⟨47045929614904278937217807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31363953076602852624811871 47045929614904278937217807)
            ·
              refine ⟨70568894422356418405826711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47045929614904278937217807 70568894422356418405826711)
              ·
                refine ⟨105853341633534627608740067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70568894422356418405826711 105853341633534627608740067)
                ·
                  refine ⟨158780012450301941413110101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105853341633534627608740067 158780012450301941413110101)
                  ·
                    refine ⟨465175817725493968983721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 158780012450301941413110101 465175817725493968983721)
                    ·
                      rfl

theorem cell23_2717780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_2717780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717780 prefixEnd_2717780 := by exact prefixLift 2717780
  have htrace : WordTrace (prefixWord ++ tailWord_2717780) baseStart_2717780 baseEnd_2717780 := by
    simpa [prefixWord, tailWord_2717780, baseEnd_2717780] using wordTrace_append hprefix tailTrace_2717780
  have hstable : (prefixWord ++ tailWord_2717780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717780).length < 2 ^ (prefixWord ++ tailWord_2717780).sum := by decide
  have hdescent : baseEnd_2717780 < baseStart_2717780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717807 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 3]
def baseStart_2717807 : Nat := 118140960795 + 2717807 * 2 ^ 59
def prefixEnd_2717807 : Nat := 4983230072969 + 3 ^ 40 * 2717807 * 2
def baseEnd_2717807 : Nat := 1395541317154153301313539

theorem tailTrace_2717807 : CollatzResearch.WordTrace tailWord_2717807 prefixEnd_2717807 1395541317154153301313539 := by
  unfold tailWord_2717807
  simp only [CollatzResearch.WordTrace]
  refine ⟨99126564864856878326687675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66084376576571252217791783 99126564864856878326687675)
  ·
    refine ⟨148689847297285317490031513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99126564864856878326687675 148689847297285317490031513)
    ·
      refine ⟨111517385472963988117523635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148689847297285317490031513 111517385472963988117523635)
      ·
        refine ⟨167276078209445982176285453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111517385472963988117523635 167276078209445982176285453)
        ·
          refine ⟨62728529328542243316107045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167276078209445982176285453 62728529328542243316107045)
          ·
            refine ⟨11761599249101670621770071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62728529328542243316107045 11761599249101670621770071)
            ·
              refine ⟨17642398873652505932655107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11761599249101670621770071 17642398873652505932655107)
              ·
                refine ⟨26463598310478758898982661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17642398873652505932655107 26463598310478758898982661)
                ·
                  refine ⟨4961924683214767293559249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26463598310478758898982661 4961924683214767293559249)
                  ·
                    refine ⟨3721443512411075470169437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4961924683214767293559249 3721443512411075470169437)
                    ·
                      refine ⟨1395541317154153301313539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3721443512411075470169437 1395541317154153301313539)
                      ·
                        rfl

theorem cell23_2717807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 3].length) (baseStart_2717807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717807 prefixEnd_2717807 := by exact prefixLift 2717807
  have htrace : WordTrace (prefixWord ++ tailWord_2717807) baseStart_2717807 baseEnd_2717807 := by
    simpa [prefixWord, tailWord_2717807, baseEnd_2717807] using wordTrace_append hprefix tailTrace_2717807
  have hstable : (prefixWord ++ tailWord_2717807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717807).length < 2 ^ (prefixWord ++ tailWord_2717807).sum := by decide
  have hdescent : baseEnd_2717807 < baseStart_2717807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717827 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 6]
def baseStart_2717827 : Nat := 118140960795 + 2717827 * 2 ^ 59
def prefixEnd_2717827 : Nat := 4983230072969 + 3 ^ 40 * 2717827 * 2
def baseEnd_2717827 : Nat := 155061287418582580340383

theorem tailTrace_2717827 : CollatzResearch.WordTrace tailWord_2717827 prefixEnd_2717827 155061287418582580340383 := by
  unfold tailWord_2717827
  simp only [CollatzResearch.WordTrace]
  refine ⟨99127294324784421742415735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66084862883189614494943823 99127294324784421742415735)
  ·
    refine ⟨148690941487176632613623603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99127294324784421742415735 148690941487176632613623603)
    ·
      refine ⟨223036412230764948920435405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148690941487176632613623603 223036412230764948920435405)
      ·
        refine ⟨83638654586536855845163277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223036412230764948920435405 83638654586536855845163277)
        ·
          refine ⟨31364495469951320941936229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83638654586536855845163277 31364495469951320941936229)
          ·
            refine ⟨5880842900615872676613043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31364495469951320941936229 5880842900615872676613043)
            ·
              refine ⟨8821264350923809014919565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880842900615872676613043 8821264350923809014919565)
              ·
                refine ⟨3307974131596428380594837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8821264350923809014919565 3307974131596428380594837)
                ·
                  refine ⟨155061287418582580340383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3307974131596428380594837 155061287418582580340383)
                  ·
                    rfl

theorem cell23_2717827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 6].length) (baseStart_2717827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717827 prefixEnd_2717827 := by exact prefixLift 2717827
  have htrace : WordTrace (prefixWord ++ tailWord_2717827) baseStart_2717827 baseEnd_2717827 := by
    simpa [prefixWord, tailWord_2717827, baseEnd_2717827] using wordTrace_append hprefix tailTrace_2717827
  have hstable : (prefixWord ++ tailWord_2717827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717827).length < 2 ^ (prefixWord ++ tailWord_2717827).sum := by decide
  have hdescent : baseEnd_2717827 < baseStart_2717827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717887 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 6, 4]
def baseStart_2717887 : Nat := 118140960795 + 2717887 * 2 ^ 59
def prefixEnd_2717887 : Nat := 4983230072969 + 3 ^ 40 * 2717887 * 2
def baseEnd_2717887 : Nat := 465194131868837662771057

theorem tailTrace_2717887 : CollatzResearch.WordTrace tailWord_2717887 prefixEnd_2717887 465194131868837662771057 := by
  unfold tailWord_2717887
  simp only [CollatzResearch.WordTrace]
  refine ⟨99129482704567051989599915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66086321803044701326399943 99129482704567051989599915)
  ·
    refine ⟨148694224056850577984399873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99129482704567051989599915 148694224056850577984399873)
    ·
      refine ⟨111520668042637933488299905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148694224056850577984399873 111520668042637933488299905)
      ·
        refine ⟨83640501031978450116224929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111520668042637933488299905 83640501031978450116224929)
        ·
          refine ⟨62730375773983837587168697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83640501031978450116224929 62730375773983837587168697)
          ·
            refine ⟨47047781830487878190376523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62730375773983837587168697 47047781830487878190376523)
            ·
              refine ⟨70571672745731817285564785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47047781830487878190376523 70571672745731817285564785)
              ·
                refine ⟨52928754559298862964173589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70571672745731817285564785 52928754559298862964173589)
                ·
                  refine ⟨2481035369967134201445637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52928754559298862964173589 2481035369967134201445637)
                  ·
                    refine ⟨465194131868837662771057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2481035369967134201445637 465194131868837662771057)
                    ·
                      rfl

theorem cell23_2717887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 4].length) (baseStart_2717887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717887 prefixEnd_2717887 := by exact prefixLift 2717887
  have htrace : WordTrace (prefixWord ++ tailWord_2717887) baseStart_2717887 baseEnd_2717887 := by
    simpa [prefixWord, tailWord_2717887, baseEnd_2717887] using wordTrace_append hprefix tailTrace_2717887
  have hstable : (prefixWord ++ tailWord_2717887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717887).length < 2 ^ (prefixWord ++ tailWord_2717887).sum := by decide
  have hdescent : baseEnd_2717887 < baseStart_2717887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717922 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2717922 : Nat := 118140960795 + 2717922 * 2 ^ 59
def prefixEnd_2717922 : Nat := 4983230072969 + 3 ^ 40 * 2717922 * 2
def baseEnd_2717922 : Nat := 1395600367429420351375511

theorem tailTrace_2717922 : CollatzResearch.WordTrace tailWord_2717922 prefixEnd_2717922 1395600367429420351375511 := by
  unfold tailWord_2717922
  simp only [CollatzResearch.WordTrace]
  refine ⟨24782689814860063241781005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66087172839626835311416013 24782689814860063241781005)
  ·
    refine ⟨9293508680572523715667877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24782689814860063241781005 9293508680572523715667877)
    ·
      refine ⟨1742532877607348196687727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9293508680572523715667877 1742532877607348196687727)
      ·
        refine ⟨2613799316411022295031591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742532877607348196687727 2613799316411022295031591)
        ·
          refine ⟨3920698974616533442547387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613799316411022295031591 3920698974616533442547387)
          ·
            refine ⟨5881048461924800163821081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920698974616533442547387 5881048461924800163821081)
            ·
              refine ⟨4410786346443600122865811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5881048461924800163821081 4410786346443600122865811)
              ·
                refine ⟨6616179519665400184298717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4410786346443600122865811 6616179519665400184298717)
                ·
                  refine ⟨2481067319874525069112019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6616179519665400184298717 2481067319874525069112019)
                  ·
                    refine ⟨3721600979811787603668029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2481067319874525069112019 3721600979811787603668029)
                    ·
                      refine ⟨1395600367429420351375511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3721600979811787603668029 1395600367429420351375511)
                      ·
                        rfl

theorem cell23_2717922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2717922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717922 prefixEnd_2717922 := by exact prefixLift 2717922
  have htrace : WordTrace (prefixWord ++ tailWord_2717922) baseStart_2717922 baseEnd_2717922 := by
    simpa [prefixWord, tailWord_2717922, baseEnd_2717922] using wordTrace_append hprefix tailTrace_2717922
  have hstable : (prefixWord ++ tailWord_2717922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717922).length < 2 ^ (prefixWord ++ tailWord_2717922).sum := by decide
  have hdescent : baseEnd_2717922 < baseStart_2717922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717928 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_2717928 : Nat := 118140960795 + 2717928 * 2 ^ 59
def prefixEnd_2717928 : Nat := 4983230072969 + 3 ^ 40 * 2717928 * 2
def baseEnd_2717928 : Nat := 1395603448313347327900483

theorem tailTrace_2717928 : CollatzResearch.WordTrace tailWord_2717928 prefixEnd_2717928 1395603448313347327900483 := by
  unfold tailWord_2717928
  simp only [CollatzResearch.WordTrace]
  refine ⟨49565489048709257995921219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66087318731612343994561625 49565489048709257995921219)
  ·
    refine ⟨74348233573063886993881829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49565489048709257995921219 74348233573063886993881829)
    ·
      refine ⟨13940293794949478811352843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74348233573063886993881829 13940293794949478811352843)
      ·
        refine ⟨20910440692424218217029265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13940293794949478811352843 20910440692424218217029265)
        ·
          refine ⟨15682830519318163662771949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20910440692424218217029265 15682830519318163662771949)
          ·
            refine ⟨5881061444744311373539481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15682830519318163662771949 5881061444744311373539481)
            ·
              refine ⟨4410796083558233530154611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5881061444744311373539481 4410796083558233530154611)
              ·
                refine ⟨6616194125337350295231917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4410796083558233530154611 6616194125337350295231917)
                ·
                  refine ⟨2481072797001506360711969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6616194125337350295231917 2481072797001506360711969)
                  ·
                    refine ⟨1860804597751129770533977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2481072797001506360711969 1860804597751129770533977)
                    ·
                      refine ⟨1395603448313347327900483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860804597751129770533977 1395603448313347327900483)
                      ·
                        rfl

theorem cell23_2717928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_2717928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717928 prefixEnd_2717928 := by exact prefixLift 2717928
  have htrace : WordTrace (prefixWord ++ tailWord_2717928) baseStart_2717928 baseEnd_2717928 := by
    simpa [prefixWord, tailWord_2717928, baseEnd_2717928] using wordTrace_append hprefix tailTrace_2717928
  have hstable : (prefixWord ++ tailWord_2717928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717928).length < 2 ^ (prefixWord ++ tailWord_2717928).sum := by decide
  have hdescent : baseEnd_2717928 < baseStart_2717928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717938 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_2717938 : Nat := 118140960795 + 2717938 * 2 ^ 59
def prefixEnd_2717938 : Nat := 4983230072969 + 3 ^ 40 * 2717938 * 2
def baseEnd_2717938 : Nat := 465202861039964096258479

theorem tailTrace_2717938 : CollatzResearch.WordTrace tailWord_2717938 prefixEnd_2717938 465202861039964096258479 := by
  unfold tailWord_2717938
  simp only [CollatzResearch.WordTrace]
  refine ⟨24782835706845571924926617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66087561884921525133137645 24782835706845571924926617)
  ·
    refine ⟨18587126780134178943694963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24782835706845571924926617 18587126780134178943694963)
    ·
      refine ⟨27880690170201268415542445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18587126780134178943694963 27880690170201268415542445)
      ·
        refine ⟨10455258813825475655828417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27880690170201268415542445 10455258813825475655828417)
        ·
          refine ⟨7841444110369106741871313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10455258813825475655828417 7841444110369106741871313)
          ·
            refine ⟨5881083082776830056403485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7841444110369106741871313 5881083082776830056403485)
            ·
              refine ⟨2205406156041311271151307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5881083082776830056403485 2205406156041311271151307)
              ·
                refine ⟨3308109234061966906726961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205406156041311271151307 3308109234061966906726961)
                ·
                  refine ⟨2481081925546475180045221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3308109234061966906726961 2481081925546475180045221)
                  ·
                    refine ⟨465202861039964096258479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2481081925546475180045221 465202861039964096258479)
                    ·
                      rfl

theorem cell23_2717938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_2717938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717938 prefixEnd_2717938 := by exact prefixLift 2717938
  have htrace : WordTrace (prefixWord ++ tailWord_2717938) baseStart_2717938 baseEnd_2717938 := by
    simpa [prefixWord, tailWord_2717938, baseEnd_2717938] using wordTrace_append hprefix tailTrace_2717938
  have hstable : (prefixWord ++ tailWord_2717938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717938).length < 2 ^ (prefixWord ++ tailWord_2717938).sum := by decide
  have hdescent : baseEnd_2717938 < baseStart_2717938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717987 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 5]
def baseStart_2717987 : Nat := 118140960795 + 2717987 * 2 ^ 59
def prefixEnd_2717987 : Nat := 4983230072969 + 3 ^ 40 * 2717987 * 2
def baseEnd_2717987 : Nat := 1395633743671962597062711

theorem tailTrace_2717987 : CollatzResearch.WordTrace tailWord_2717987 prefixEnd_2717987 1395633743671962597062711 := by
  unfold tailWord_2717987
  simp only [CollatzResearch.WordTrace]
  refine ⟨99133130004204769068240215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66088753336136512712160143 99133130004204769068240215)
  ·
    refine ⟨148699695006307153602360323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99133130004204769068240215 148699695006307153602360323)
    ·
      refine ⟨223049542509460730403540485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148699695006307153602360323 223049542509460730403540485)
      ·
        refine ⟨41821789220523886950663841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223049542509460730403540485 41821789220523886950663841)
        ·
          refine ⟨31366341915392915212997881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41821789220523886950663841 31366341915392915212997881)
          ·
            refine ⟨23524756436544686409748411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31366341915392915212997881 23524756436544686409748411)
            ·
              refine ⟨35287134654817029614622617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23524756436544686409748411 35287134654817029614622617)
              ·
                refine ⟨26465350991112772210966963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35287134654817029614622617 26465350991112772210966963)
                ·
                  refine ⟨39698026486669158316450445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26465350991112772210966963 39698026486669158316450445)
                  ·
                    refine ⟨14886759932500934368668917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39698026486669158316450445 14886759932500934368668917)
                    ·
                      refine ⟨1395633743671962597062711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14886759932500934368668917 1395633743671962597062711)
                      ·
                        rfl

theorem cell23_2717987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_2717987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2717987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2717987 prefixEnd_2717987 := by exact prefixLift 2717987
  have htrace : WordTrace (prefixWord ++ tailWord_2717987) baseStart_2717987 baseEnd_2717987 := by
    simpa [prefixWord, tailWord_2717987, baseEnd_2717987] using wordTrace_append hprefix tailTrace_2717987
  have hstable : (prefixWord ++ tailWord_2717987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717987).length < 2 ^ (prefixWord ++ tailWord_2717987).sum := by decide
  have hdescent : baseEnd_2717987 < baseStart_2717987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718007 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 7]
def baseStart_2718007 : Nat := 118140960795 + 2718007 * 2 ^ 59
def prefixEnd_2718007 : Nat := 4983230072969 + 3 ^ 40 * 2718007 * 2
def baseEnd_2718007 : Nat := 155071557031672502090291

theorem tailTrace_2718007 : CollatzResearch.WordTrace tailWord_2718007 prefixEnd_2718007 155071557031672502090291 := by
  unfold tailWord_2718007
  simp only [CollatzResearch.WordTrace]
  refine ⟨99133859464132312483968275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66089239642754874989312183 99133859464132312483968275)
  ·
    refine ⟨148700789196198468725952413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99133859464132312483968275 148700789196198468725952413)
    ·
      refine ⟨55762795948574425772232155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148700789196198468725952413 55762795948574425772232155)
      ·
        refine ⟨83644193922861638658348233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55762795948574425772232155 83644193922861638658348233)
        ·
          refine ⟨62733145442146228993761175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83644193922861638658348233 62733145442146228993761175)
          ·
            refine ⟨94099718163219343490641763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62733145442146228993761175 94099718163219343490641763)
            ·
              refine ⟨141149577244829015235962645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94099718163219343490641763 141149577244829015235962645)
              ·
                refine ⟨6616386433351360089185749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141149577244829015235962645 6616386433351360089185749)
                ·
                  refine ⟨155071557031672502090291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6616386433351360089185749 155071557031672502090291)
                  ·
                    rfl

theorem cell23_2718007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 7].length) (baseStart_2718007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718007 prefixEnd_2718007 := by exact prefixLift 2718007
  have htrace : WordTrace (prefixWord ++ tailWord_2718007) baseStart_2718007 baseEnd_2718007 := by
    simpa [prefixWord, tailWord_2718007, baseEnd_2718007] using wordTrace_append hprefix tailTrace_2718007
  have hstable : (prefixWord ++ tailWord_2718007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718007).length < 2 ^ (prefixWord ++ tailWord_2718007).sum := by decide
  have hdescent : baseEnd_2718007 < baseStart_2718007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718061 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_2718061 : Nat := 118140960795 + 2718061 * 2 ^ 59
def prefixEnd_2718061 : Nat := 4983230072969 + 3 ^ 40 * 2718061 * 2
def baseEnd_2718061 : Nat := 1395671741240395307537371

theorem tailTrace_2718061 : CollatzResearch.WordTrace tailWord_2718061 prefixEnd_2718061 1395671741240395307537371 := by
  unfold tailWord_2718061
  simp only [CollatzResearch.WordTrace]
  refine ⟨99135829005936679706434037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66090552670624453137622691 99135829005936679706434037)
  ·
    refine ⟨9293983969306563722478191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99135829005936679706434037 9293983969306563722478191)
    ·
      refine ⟨13940975953959845583717287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9293983969306563722478191 13940975953959845583717287)
      ·
        refine ⟨20911463930939768375575931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13940975953959845583717287 20911463930939768375575931)
        ·
          refine ⟨31367195896409652563363897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20911463930939768375575931 31367195896409652563363897)
          ·
            refine ⟨23525396922307239422522923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31367195896409652563363897 23525396922307239422522923)
            ·
              refine ⟨35288095383460859133784385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23525396922307239422522923 35288095383460859133784385)
              ·
                refine ⟨26466071537595644350338289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35288095383460859133784385 26466071537595644350338289)
                ·
                  refine ⟨19849553653196733262753717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26466071537595644350338289 19849553653196733262753717)
                  ·
                    refine ⟨1860895654987193743383161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19849553653196733262753717 1860895654987193743383161)
                    ·
                      refine ⟨1395671741240395307537371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860895654987193743383161 1395671741240395307537371)
                      ·
                        rfl

theorem cell23_2718061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_2718061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718061 prefixEnd_2718061 := by exact prefixLift 2718061
  have htrace : WordTrace (prefixWord ++ tailWord_2718061) baseStart_2718061 baseEnd_2718061 := by
    simpa [prefixWord, tailWord_2718061, baseEnd_2718061] using wordTrace_append hprefix tailTrace_2718061
  have hstable : (prefixWord ++ tailWord_2718061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718061).length < 2 ^ (prefixWord ++ tailWord_2718061).sum := by decide
  have hdescent : baseEnd_2718061 < baseStart_2718061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718067 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 2, 8]
def baseStart_2718067 : Nat := 118140960795 + 2718067 * 2 ^ 59
def prefixEnd_2718067 : Nat := 4983230072969 + 3 ^ 40 * 2718067 * 2
def baseEnd_2718067 : Nat := 465224940708107428020781

theorem tailTrace_2718067 : CollatzResearch.WordTrace tailWord_2718067 prefixEnd_2718067 465224940708107428020781 := by
  unfold tailWord_2718067
  simp only [CollatzResearch.WordTrace]
  refine ⟨99136047843914942731152455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66090698562609961820768303 99136047843914942731152455)
  ·
    refine ⟨148704071765872414096728683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99136047843914942731152455 148704071765872414096728683)
    ·
      refine ⟨223056107648808621145093025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148704071765872414096728683 223056107648808621145093025)
      ·
        refine ⟨167292080736606465858819769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223056107648808621145093025 167292080736606465858819769)
        ·
          refine ⟨125469060552454849394114827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167292080736606465858819769 125469060552454849394114827)
          ·
            refine ⟨188203590828682274091172241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125469060552454849394114827 188203590828682274091172241)
            ·
              refine ⟨141152693121511705568379181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188203590828682274091172241 141152693121511705568379181)
              ·
                refine ⟨52932259920566889588142193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141152693121511705568379181 52932259920566889588142193)
                ·
                  refine ⟨39699194940425167191106645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52932259920566889588142193 39699194940425167191106645)
                  ·
                    refine ⟨465224940708107428020781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39699194940425167191106645 465224940708107428020781)
                    ·
                      rfl

theorem cell23_2718067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 8].length) (baseStart_2718067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718067 prefixEnd_2718067 := by exact prefixLift 2718067
  have htrace : WordTrace (prefixWord ++ tailWord_2718067) baseStart_2718067 baseEnd_2718067 := by
    simpa [prefixWord, tailWord_2718067, baseEnd_2718067] using wordTrace_append hprefix tailTrace_2718067
  have hstable : (prefixWord ++ tailWord_2718067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718067).length < 2 ^ (prefixWord ++ tailWord_2718067).sum := by decide
  have hdescent : baseEnd_2718067 < baseStart_2718067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718091 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 2, 4, 2]
def baseStart_2718091 : Nat := 118140960795 + 2718091 * 2 ^ 59
def prefixEnd_2718091 : Nat := 4983230072969 + 3 ^ 40 * 2718091 * 2
def baseEnd_2718091 : Nat := 1395687145660030190162233

theorem tailTrace_2718091 : CollatzResearch.WordTrace tailWord_2718091 prefixEnd_2718091 1395687145660030190162233 := by
  unfold tailWord_2718091
  simp only [CollatzResearch.WordTrace]
  refine ⟨99136923195827994830026127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66091282130551996553350751 99136923195827994830026127)
  ·
    refine ⟨148705384793741992245039191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99136923195827994830026127 148705384793741992245039191)
    ·
      refine ⟨223058077190612988367558787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148705384793741992245039191 223058077190612988367558787)
      ·
        refine ⟨334587115785919482551338181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223058077190612988367558787 334587115785919482551338181)
        ·
          refine ⟨62735084209859902978375909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 334587115785919482551338181 62735084209859902978375909)
          ·
            refine ⟨11762828289348731808445483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62735084209859902978375909 11762828289348731808445483)
            ·
              refine ⟨17644242434023097712668225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11762828289348731808445483 17644242434023097712668225)
              ·
                refine ⟨13233181825517323284501169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17644242434023097712668225 13233181825517323284501169)
                ·
                  refine ⟨9924886369137992463375877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13233181825517323284501169 9924886369137992463375877)
                  ·
                    refine ⟨1860916194213373586882977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9924886369137992463375877 1860916194213373586882977)
                    ·
                      refine ⟨1395687145660030190162233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1860916194213373586882977 1395687145660030190162233)
                      ·
                        rfl

theorem cell23_2718091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 4, 2].length) (baseStart_2718091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718091 prefixEnd_2718091 := by exact prefixLift 2718091
  have htrace : WordTrace (prefixWord ++ tailWord_2718091) baseStart_2718091 baseEnd_2718091 := by
    simpa [prefixWord, tailWord_2718091, baseEnd_2718091] using wordTrace_append hprefix tailTrace_2718091
  have hstable : (prefixWord ++ tailWord_2718091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718091).length < 2 ^ (prefixWord ++ tailWord_2718091).sum := by decide
  have hdescent : baseEnd_2718091 < baseStart_2718091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718124 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 3]
def baseStart_2718124 : Nat := 118140960795 + 2718124 * 2 ^ 59
def prefixEnd_2718124 : Nat := 4983230072969 + 3 ^ 40 * 2718124 * 2
def baseEnd_2718124 : Nat := 1395704090521628561049581

theorem tailTrace_2718124 : CollatzResearch.WordTrace tailWord_2718124 prefixEnd_2718124 1395704090521628561049581 := by
  unfold tailWord_2718124
  simp only [CollatzResearch.WordTrace]
  refine ⟨49569063402354220732988713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66092084536472294310651617 49569063402354220732988713)
  ·
    refine ⟨37176797551765665549741535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49569063402354220732988713 37176797551765665549741535)
    ·
      refine ⟨55765196327648498324612303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37176797551765665549741535 55765196327648498324612303)
      ·
        refine ⟨83647794491472747486918455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55765196327648498324612303 83647794491472747486918455)
        ·
          refine ⟨125471691737209121230377683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83647794491472747486918455 125471691737209121230377683)
          ·
            refine ⟨188207537605813681845566525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125471691737209121230377683 188207537605813681845566525)
            ·
              refine ⟨70577826602180130692087447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188207537605813681845566525 70577826602180130692087447)
              ·
                refine ⟨105866739903270196038131171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70577826602180130692087447 105866739903270196038131171)
                ·
                  refine ⟨158800109854905294057196757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105866739903270196038131171 158800109854905294057196757)
                  ·
                    refine ⟨3721877574724342829465549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 158800109854905294057196757 3721877574724342829465549)
                    ·
                      refine ⟨1395704090521628561049581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3721877574724342829465549 1395704090521628561049581)
                      ·
                        rfl

theorem cell23_2718124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_2718124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718124 prefixEnd_2718124 := by exact prefixLift 2718124
  have htrace : WordTrace (prefixWord ++ tailWord_2718124) baseStart_2718124 baseEnd_2718124 := by
    simpa [prefixWord, tailWord_2718124, baseEnd_2718124] using wordTrace_append hprefix tailTrace_2718124
  have hstable : (prefixWord ++ tailWord_2718124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718124).length < 2 ^ (prefixWord ++ tailWord_2718124).sum := by decide
  have hdescent : baseEnd_2718124 < baseStart_2718124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718135 : List Nat := [1, 1, 3, 1, 3, 5, 1, 3, 1, 4]
def baseStart_2718135 : Nat := 118140960795 + 2718135 * 2 ^ 59
def prefixEnd_2718135 : Nat := 4983230072969 + 3 ^ 40 * 2718135 * 2
def baseEnd_2718135 : Nat := 465236579602942672670677

theorem tailTrace_2718135 : CollatzResearch.WordTrace tailWord_2718135 prefixEnd_2718135 465236579602942672670677 := by
  unfold tailWord_2718135
  simp only [CollatzResearch.WordTrace]
  refine ⟨99138528007668590344627859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66092352005112393563085239 99138528007668590344627859)
  ·
    refine ⟨148707792011502885516941789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99138528007668590344627859 148707792011502885516941789)
    ·
      refine ⟨55765422004313582068853171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148707792011502885516941789 55765422004313582068853171)
      ·
        refine ⟨83648133006470373103279757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55765422004313582068853171 83648133006470373103279757)
        ·
          refine ⟨31368049877426389913729909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83648133006470373103279757 31368049877426389913729909)
          ·
            refine ⟨2940754676008724054412179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31368049877426389913729909 2940754676008724054412179)
            ·
              refine ⟨4411132014013086081618269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940754676008724054412179 4411132014013086081618269)
              ·
                refine ⟨1654174505254907280606851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4411132014013086081618269 1654174505254907280606851)
                ·
                  refine ⟨2481261757882360920910277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1654174505254907280606851 2481261757882360920910277)
                  ·
                    refine ⟨465236579602942672670677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2481261757882360920910277 465236579602942672670677)
                    ·
                      rfl

theorem cell23_2718135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_2718135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718135 prefixEnd_2718135 := by exact prefixLift 2718135
  have htrace : WordTrace (prefixWord ++ tailWord_2718135) baseStart_2718135 baseEnd_2718135 := by
    simpa [prefixWord, tailWord_2718135, baseEnd_2718135] using wordTrace_append hprefix tailTrace_2718135
  have hstable : (prefixWord ++ tailWord_2718135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718135).length < 2 ^ (prefixWord ++ tailWord_2718135).sum := by decide
  have hdescent : baseEnd_2718135 < baseStart_2718135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718144 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 5, 5]
def baseStart_2718144 : Nat := 118140960795 + 2718144 * 2 ^ 59
def prefixEnd_2718144 : Nat := 4983230072969 + 3 ^ 40 * 2718144 * 2
def baseEnd_2718144 : Nat := 465238120044906160933163

theorem tailTrace_2718144 : CollatzResearch.WordTrace tailWord_2718144 prefixEnd_2718144 465238120044906160933163 := by
  unfold tailWord_2718144
  simp only [CollatzResearch.WordTrace]
  refine ⟨49569428132317992440852743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66092570843090656587803657 49569428132317992440852743)
  ·
    refine ⟨74354142198476988661279115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49569428132317992440852743 74354142198476988661279115)
    ·
      refine ⟨111531213297715482991918673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74354142198476988661279115 111531213297715482991918673)
      ·
        refine ⟨83648409973286612243939005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111531213297715482991918673 83648409973286612243939005)
        ·
          refine ⟨31368153739982479591477127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83648409973286612243939005 31368153739982479591477127)
          ·
            refine ⟨47052230609973719387215691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31368153739982479591477127 47052230609973719387215691)
            ·
              refine ⟨70578345914960579080823537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47052230609973719387215691 70578345914960579080823537)
              ·
                refine ⟨52933759436220434310617653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70578345914960579080823537 52933759436220434310617653)
                ·
                  refine ⟨4962539947145665716620405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52933759436220434310617653 4962539947145665716620405)
                  ·
                    refine ⟨465238120044906160933163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4962539947145665716620405 465238120044906160933163)
                    ·
                      rfl

theorem cell23_2718144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_2718144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718144 prefixEnd_2718144 := by exact prefixLift 2718144
  have htrace : WordTrace (prefixWord ++ tailWord_2718144) baseStart_2718144 baseEnd_2718144 := by
    simpa [prefixWord, tailWord_2718144, baseEnd_2718144] using wordTrace_append hprefix tailTrace_2718144
  have hstable : (prefixWord ++ tailWord_2718144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718144).length < 2 ^ (prefixWord ++ tailWord_2718144).sum := by decide
  have hdescent : baseEnd_2718144 < baseStart_2718144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718201 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 5]
def baseStart_2718201 : Nat := 118140960795 + 2718201 * 2 ^ 59
def prefixEnd_2718201 : Nat := 4983230072969 + 3 ^ 40 * 2718201 * 2
def baseEnd_2718201 : Nat := 1395743628532024759786727

theorem tailTrace_2718201 : CollatzResearch.WordTrace tailWord_2718201 prefixEnd_2718201 1395743628532024759786727 := by
  unfold tailWord_2718201
  simp only [CollatzResearch.WordTrace]
  refine ⟨99140935225429483616530457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66093956816952989077686971 99140935225429483616530457)
  ·
    refine ⟨74355701419072112712397843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99140935225429483616530457 74355701419072112712397843)
    ·
      refine ⟨111533552128608169068596765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74355701419072112712397843 111533552128608169068596765)
      ·
        refine ⟨41825082048228063400723787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111533552128608169068596765 41825082048228063400723787)
        ·
          refine ⟨62737623072342095101085681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41825082048228063400723787 62737623072342095101085681)
          ·
            refine ⟨47053217304256571325814261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62737623072342095101085681 47053217304256571325814261)
            ·
              refine ⟨4411239122274053561795087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47053217304256571325814261 4411239122274053561795087)
              ·
                refine ⟨6616858683411080342692631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411239122274053561795087 6616858683411080342692631)
                ·
                  refine ⟨9925288025116620514038947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6616858683411080342692631 9925288025116620514038947)
                  ·
                    refine ⟨14887932037674930771058421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9925288025116620514038947 14887932037674930771058421)
                    ·
                      refine ⟨1395743628532024759786727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14887932037674930771058421 1395743628532024759786727)
                      ·
                        rfl

theorem cell23_2718201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_2718201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718201 prefixEnd_2718201 := by exact prefixLift 2718201
  have htrace : WordTrace (prefixWord ++ tailWord_2718201) baseStart_2718201 baseEnd_2718201 := by
    simpa [prefixWord, tailWord_2718201, baseEnd_2718201] using wordTrace_append hprefix tailTrace_2718201
  have hstable : (prefixWord ++ tailWord_2718201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718201).length < 2 ^ (prefixWord ++ tailWord_2718201).sum := by decide
  have hdescent : baseEnd_2718201 < baseStart_2718201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718209 : List Nat := [1, 2, 4, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_2718209 : Nat := 118140960795 + 2718209 * 2 ^ 59
def prefixEnd_2718209 : Nat := 4983230072969 + 3 ^ 40 * 2718209 * 2
def baseEnd_2718209 : Nat := 1395747736377260728486691

theorem tailTrace_2718209 : CollatzResearch.WordTrace tailWord_2718209 prefixEnd_2718209 1395747736377260728486691 := by
  unfold tailWord_2718209
  simp only [CollatzResearch.WordTrace]
  refine ⟨99141227009400500982821681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66094151339600333988547787 99141227009400500982821681)
  ·
    refine ⟨74355920257050375737116261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99141227009400500982821681 74355920257050375737116261)
    ·
      refine ⟨13941735048196945450709299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74355920257050375737116261 13941735048196945450709299)
      ·
        refine ⟨20912602572295418176063949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13941735048196945450709299 20912602572295418176063949)
        ·
          refine ⟨7842225964610781816023981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20912602572295418176063949 7842225964610781816023981)
          ·
            refine ⟨2940834736729043181008993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7842225964610781816023981 2940834736729043181008993)
            ·
              refine ⟨2205626052546782385756745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2940834736729043181008993 2205626052546782385756745)
              ·
                refine ⟨1654219539410086789317559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2205626052546782385756745 1654219539410086789317559)
                ·
                  refine ⟨2481329309115130183976339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1654219539410086789317559 2481329309115130183976339)
                  ·
                    refine ⟨3721993963672695275964509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2481329309115130183976339 3721993963672695275964509)
                    ·
                      refine ⟨1395747736377260728486691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3721993963672695275964509 1395747736377260728486691)
                      ·
                        rfl

theorem cell23_2718209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_2718209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718209 prefixEnd_2718209 := by exact prefixLift 2718209
  have htrace : WordTrace (prefixWord ++ tailWord_2718209) baseStart_2718209 baseEnd_2718209 := by
    simpa [prefixWord, tailWord_2718209, baseEnd_2718209] using wordTrace_append hprefix tailTrace_2718209
  have hstable : (prefixWord ++ tailWord_2718209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718209).length < 2 ^ (prefixWord ++ tailWord_2718209).sum := by decide
  have hdescent : baseEnd_2718209 < baseStart_2718209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718276 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2718276 : Nat := 118140960795 + 2718276 * 2 ^ 59
def prefixEnd_2718276 : Nat := 4983230072969 + 3 ^ 40 * 2718276 * 2
def baseEnd_2718276 : Nat := 465260713193703988782961

theorem tailTrace_2718276 : CollatzResearch.WordTrace tailWord_2718276 prefixEnd_2718276 465260713193703988782961 := by
  unfold tailWord_2718276
  simp only [CollatzResearch.WordTrace]
  refine ⟨49571835350078885712755341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66095780466771847617007121 49571835350078885712755341)
  ·
    refine ⟨18589438256279582142283253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49571835350078885712755341 18589438256279582142283253)
    ·
      refine ⟨1742759836526210825839055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18589438256279582142283253 1742759836526210825839055)
      ·
        refine ⟨2614139754789316238758583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742759836526210825839055 2614139754789316238758583)
        ·
          refine ⟨3921209632183974358137875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2614139754789316238758583 3921209632183974358137875)
          ·
            refine ⟨5881814448275961537206813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3921209632183974358137875 5881814448275961537206813)
            ·
              refine ⟨2205680418103485576452555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5881814448275961537206813 2205680418103485576452555)
              ·
                refine ⟨3308520627155228364678833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205680418103485576452555 3308520627155228364678833)
                ·
                  refine ⟨2481390470366421273509125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3308520627155228364678833 2481390470366421273509125)
                  ·
                    refine ⟨465260713193703988782961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2481390470366421273509125 465260713193703988782961)
                    ·
                      rfl

theorem cell23_2718276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2718276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718276 prefixEnd_2718276 := by exact prefixLift 2718276
  have htrace : WordTrace (prefixWord ++ tailWord_2718276) baseStart_2718276 baseEnd_2718276 := by
    simpa [prefixWord, tailWord_2718276, baseEnd_2718276] using wordTrace_append hprefix tailTrace_2718276
  have hstable : (prefixWord ++ tailWord_2718276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718276).length < 2 ^ (prefixWord ++ tailWord_2718276).sum := by decide
  have hdescent : baseEnd_2718276 < baseStart_2718276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718282 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3]
def baseStart_2718282 : Nat := 118140960795 + 2718282 * 2 ^ 59
def prefixEnd_2718282 : Nat := 4983230072969 + 3 ^ 40 * 2718282 * 2
def baseEnd_2718282 : Nat := 1395785220465038942873855

theorem tailTrace_2718282 : CollatzResearch.WordTrace tailWord_2718282 prefixEnd_2718282 1395785220465038942873855 := by
  unfold tailWord_2718282
  simp only [CollatzResearch.WordTrace]
  refine ⟨24785972384534008612557275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66095926358757356300152733 24785972384534008612557275)
  ·
    refine ⟨37178958576801012918835913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24785972384534008612557275 37178958576801012918835913)
    ·
      refine ⟨27884218932600759689126935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37178958576801012918835913 27884218932600759689126935)
      ·
        refine ⟨41826328398901139533690403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27884218932600759689126935 41826328398901139533690403)
        ·
          refine ⟨62739492598351709300535605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41826328398901139533690403 62739492598351709300535605)
          ·
            refine ⟨5881827431095472746925213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62739492598351709300535605 5881827431095472746925213)
            ·
              refine ⟨2205685286660802280096955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5881827431095472746925213 2205685286660802280096955)
              ·
                refine ⟨3308527929991203420145433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205685286660802280096955 3308527929991203420145433)
                ·
                  refine ⟨2481395947493402565109075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3308527929991203420145433 2481395947493402565109075)
                  ·
                    refine ⟨3722093921240103847663613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2481395947493402565109075 3722093921240103847663613)
                    ·
                      refine ⟨1395785220465038942873855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3722093921240103847663613 1395785220465038942873855)
                      ·
                        rfl

theorem cell23_2718282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_2718282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718282 prefixEnd_2718282 := by exact prefixLift 2718282
  have htrace : WordTrace (prefixWord ++ tailWord_2718282) baseStart_2718282 baseEnd_2718282 := by
    simpa [prefixWord, tailWord_2718282, baseEnd_2718282] using wordTrace_append hprefix tailTrace_2718282
  have hstable : (prefixWord ++ tailWord_2718282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718282).length < 2 ^ (prefixWord ++ tailWord_2718282).sum := by decide
  have hdescent : baseEnd_2718282 < baseStart_2718282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718288 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 1, 4, 2]
def baseStart_2718288 : Nat := 118140960795 + 2718288 * 2 ^ 59
def prefixEnd_2718288 : Nat := 4983230072969 + 3 ^ 40 * 2718288 * 2
def baseEnd_2718288 : Nat := 1395788301348965919398827

theorem tailTrace_2718288 : CollatzResearch.WordTrace tailWord_2718288 prefixEnd_2718288 1395788301348965919398827 := by
  unfold tailWord_2718288
  simp only [CollatzResearch.WordTrace]
  refine ⟨49572054188057148737473759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66096072250742864983298345 49572054188057148737473759)
  ·
    refine ⟨74358081282085723106210639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49572054188057148737473759 74358081282085723106210639)
    ·
      refine ⟨111537121923128584659315959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74358081282085723106210639 111537121923128584659315959)
      ·
        refine ⟨167305682884692876988973939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111537121923128584659315959 167305682884692876988973939)
        ·
          refine ⟨250958524327039315483460909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167305682884692876988973939 250958524327039315483460909)
          ·
            refine ⟨94109446622639743306297841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250958524327039315483460909 94109446622639743306297841)
            ·
              refine ⟨70582084966979807479723381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94109446622639743306297841 70582084966979807479723381)
              ·
                refine ⟨6617070465654356951224067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70582084966979807479723381 6617070465654356951224067)
                ·
                  refine ⟨9925605698481535426836101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6617070465654356951224067 9925605698481535426836101)
                  ·
                    refine ⟨1861051068465287892531769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9925605698481535426836101 1861051068465287892531769)
                    ·
                      refine ⟨1395788301348965919398827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861051068465287892531769 1395788301348965919398827)
                      ·
                        rfl

theorem cell23_2718288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 4, 2].length) (baseStart_2718288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718288 prefixEnd_2718288 := by exact prefixLift 2718288
  have htrace : WordTrace (prefixWord ++ tailWord_2718288) baseStart_2718288 baseEnd_2718288 := by
    simpa [prefixWord, tailWord_2718288, baseEnd_2718288] using wordTrace_append hprefix tailTrace_2718288
  have hstable : (prefixWord ++ tailWord_2718288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718288).length < 2 ^ (prefixWord ++ tailWord_2718288).sum := by decide
  have hdescent : baseEnd_2718288 < baseStart_2718288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718292 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_2718292 : Nat := 118140960795 + 2718292 * 2 ^ 59
def prefixEnd_2718292 : Nat := 4983230072969 + 3 ^ 40 * 2718292 * 2
def baseEnd_2718292 : Nat := 1395790355271583903748809

theorem tailTrace_2718292 : CollatzResearch.WordTrace tailWord_2718292 prefixEnd_2718292 1395790355271583903748809 := by
  unfold tailWord_2718292
  simp only [CollatzResearch.WordTrace]
  refine ⟨49572127134049903079046565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66096169512066537438728753 49572127134049903079046565)
  ·
    refine ⟨9294773837634356827321231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49572127134049903079046565 9294773837634356827321231)
    ·
      refine ⟨13942160756451535240981847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9294773837634356827321231 13942160756451535240981847)
      ·
        refine ⟨20913241134677302861472771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13942160756451535240981847 20913241134677302861472771)
        ·
          refine ⟨31369861702015954292209157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20913241134677302861472771 31369861702015954292209157)
          ·
            refine ⟨5881849069127991429789217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31369861702015954292209157 5881849069127991429789217)
            ·
              refine ⟨4411386801845993572341913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5881849069127991429789217 4411386801845993572341913)
              ·
                refine ⟨3308540101384495179256435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4411386801845993572341913 3308540101384495179256435)
                ·
                  refine ⟨4962810152076742768884653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3308540101384495179256435 4962810152076742768884653)
                  ·
                    refine ⟨1861053807028778538331745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4962810152076742768884653 1861053807028778538331745)
                    ·
                      refine ⟨1395790355271583903748809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861053807028778538331745 1395790355271583903748809)
                      ·
                        rfl

theorem cell23_2718292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_2718292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718292 prefixEnd_2718292 := by exact prefixLift 2718292
  have htrace : WordTrace (prefixWord ++ tailWord_2718292) baseStart_2718292 baseEnd_2718292 := by
    simpa [prefixWord, tailWord_2718292, baseEnd_2718292] using wordTrace_append hprefix tailTrace_2718292
  have hstable : (prefixWord ++ tailWord_2718292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718292).length < 2 ^ (prefixWord ++ tailWord_2718292).sum := by decide
  have hdescent : baseEnd_2718292 < baseStart_2718292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718305 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 4, 2, 2]
def baseStart_2718305 : Nat := 118140960795 + 2718305 * 2 ^ 59
def prefixEnd_2718305 : Nat := 4983230072969 + 3 ^ 40 * 2718305 * 2
def baseEnd_2718305 : Nat := 1395797030520092352886249

theorem tailTrace_2718305 : CollatzResearch.WordTrace tailWord_2718305 prefixEnd_2718305 1395797030520092352886249 := by
  unfold tailWord_2718305
  simp only [CollatzResearch.WordTrace]
  refine ⟨99144728417052709378316369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66096485611368472918877579 99144728417052709378316369)
  ·
    refine ⟨74358546312789532033737277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99144728417052709378316369 74358546312789532033737277)
    ·
      refine ⟨27884454867296074512651479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74358546312789532033737277 27884454867296074512651479)
      ·
        refine ⟨41826682300944111768977219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27884454867296074512651479 41826682300944111768977219)
        ·
          refine ⟨62740023451416167653465829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41826682300944111768977219 62740023451416167653465829)
          ·
            refine ⟨11763754397140531435024843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62740023451416167653465829 11763754397140531435024843)
            ·
              refine ⟨17645631595710797152537265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11763754397140531435024843 17645631595710797152537265)
              ·
                refine ⟨13234223696783097864402949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17645631595710797152537265 13234223696783097864402949)
                ·
                  refine ⟨2481416943146830849575553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13234223696783097864402949 2481416943146830849575553)
                  ·
                    refine ⟨1861062707360123137181665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2481416943146830849575553 1861062707360123137181665)
                    ·
                      refine ⟨1395797030520092352886249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861062707360123137181665 1395797030520092352886249)
                      ·
                        rfl

theorem cell23_2718305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_2718305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718305 prefixEnd_2718305 := by exact prefixLift 2718305
  have htrace : WordTrace (prefixWord ++ tailWord_2718305) baseStart_2718305 baseEnd_2718305 := by
    simpa [prefixWord, tailWord_2718305, baseEnd_2718305] using wordTrace_append hprefix tailTrace_2718305
  have hstable : (prefixWord ++ tailWord_2718305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718305).length < 2 ^ (prefixWord ++ tailWord_2718305).sum := by decide
  have hdescent : baseEnd_2718305 < baseStart_2718305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718348 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 4, 5, 2]
def baseStart_2718348 : Nat := 118140960795 + 2718348 * 2 ^ 59
def prefixEnd_2718348 : Nat := 4983230072969 + 3 ^ 40 * 2718348 * 2
def baseEnd_2718348 : Nat := 1395819110188235684648551

theorem tailTrace_2718348 : CollatzResearch.WordTrace tailWord_2718348 prefixEnd_2718348 1395819110188235684648551 := by
  unfold tailWord_2718348
  simp only [CollatzResearch.WordTrace]
  refine ⟨49573148377948463861065849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66097531170597951814754465 49573148377948463861065849)
  ·
    refine ⟨37179861283461347895799387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49573148377948463861065849 37179861283461347895799387)
    ·
      refine ⟨55769791925192021843699081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37179861283461347895799387 55769791925192021843699081)
      ·
        refine ⟨41827343943894016382774311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55769791925192021843699081 41827343943894016382774311)
        ·
          refine ⟨62741015915841024574161467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41827343943894016382774311 62741015915841024574161467)
          ·
            refine ⟨94111523873761536861242201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62741015915841024574161467 94111523873761536861242201)
            ·
              refine ⟨70583642905321152645931651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94111523873761536861242201 70583642905321152645931651)
              ·
                refine ⟨105875464357981728968897477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70583642905321152645931651 105875464357981728968897477)
                ·
                  refine ⟨19851649567121574181668277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105875464357981728968897477 19851649567121574181668277)
                  ·
                    refine ⟨1861092146917647579531401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19851649567121574181668277 1861092146917647579531401)
                    ·
                      refine ⟨1395819110188235684648551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861092146917647579531401 1395819110188235684648551)
                      ·
                        rfl

theorem cell23_2718348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_2718348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718348 prefixEnd_2718348 := by exact prefixLift 2718348
  have htrace : WordTrace (prefixWord ++ tailWord_2718348) baseStart_2718348 baseEnd_2718348 := by
    simpa [prefixWord, tailWord_2718348, baseEnd_2718348] using wordTrace_append hprefix tailTrace_2718348
  have hstable : (prefixWord ++ tailWord_2718348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718348).length < 2 ^ (prefixWord ++ tailWord_2718348).sum := by decide
  have hdescent : baseEnd_2718348 < baseStart_2718348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718382 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_2718382 : Nat := 118140960795 + 2718382 * 2 ^ 59
def prefixEnd_2718382 : Nat := 4983230072969 + 3 ^ 40 * 2718382 * 2
def baseEnd_2718382 : Nat := 1395836568530488551623395

theorem tailTrace_2718382 : CollatzResearch.WordTrace tailWord_2718382 prefixEnd_2718382 1395836568530488551623395 := by
  unfold tailWord_2718382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12393442104721718941108675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66098357891849167685912933 12393442104721718941108675)
  ·
    refine ⟨18590163157082578411663013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12393442104721718941108675 18590163157082578411663013)
    ·
      refine ⟨3485655591952983452186815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18590163157082578411663013 3485655591952983452186815)
      ·
        refine ⟨5228483387929475178280223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3485655591952983452186815 5228483387929475178280223)
        ·
          refine ⟨7842725081894212767420335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5228483387929475178280223 7842725081894212767420335)
          ·
            refine ⟨11764087622841319151130503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7842725081894212767420335 11764087622841319151130503)
            ·
              refine ⟨17646131434261978726695755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11764087622841319151130503 17646131434261978726695755)
              ·
                refine ⟨26469197151392968090043633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17646131434261978726695755 26469197151392968090043633)
                ·
                  refine ⟨19851897863544726067532725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26469197151392968090043633 19851897863544726067532725)
                  ·
                    refine ⟨1861115424707318068831193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19851897863544726067532725 1861115424707318068831193)
                    ·
                      refine ⟨1395836568530488551623395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861115424707318068831193 1395836568530488551623395)
                      ·
                        rfl

theorem cell23_2718382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_2718382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718382 prefixEnd_2718382 := by exact prefixLift 2718382
  have htrace : WordTrace (prefixWord ++ tailWord_2718382) baseStart_2718382 baseEnd_2718382 := by
    simpa [prefixWord, tailWord_2718382, baseEnd_2718382] using wordTrace_append hprefix tailTrace_2718382
  have hstable : (prefixWord ++ tailWord_2718382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718382).length < 2 ^ (prefixWord ++ tailWord_2718382).sum := by decide
  have hdescent : baseEnd_2718382 < baseStart_2718382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718412 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2718412 : Nat := 118140960795 + 2718412 * 2 ^ 59
def prefixEnd_2718412 : Nat := 4983230072969 + 3 ^ 40 * 2718412 * 2
def baseEnd_2718412 : Nat := 1395851972950123434248257

theorem tailTrace_2718412 : CollatzResearch.WordTrace tailWord_2718412 prefixEnd_2718412 1395851972950123434248257 := by
  unfold tailWord_2718412
  simp only [CollatzResearch.WordTrace]
  refine ⟨49574315513832533326230745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66099087351776711101640993 49574315513832533326230745)
  ·
    refine ⟨37180736635374399994673059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49574315513832533326230745 37180736635374399994673059)
    ·
      refine ⟨55771104953061599992009589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37180736635374399994673059 55771104953061599992009589)
      ·
        refine ⟨5228541089349524999250899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55771104953061599992009589 5228541089349524999250899)
        ·
          refine ⟨7842811634024287498876349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5228541089349524999250899 7842811634024287498876349)
          ·
            refine ⟨2941054362759107812078631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7842811634024287498876349 2941054362759107812078631)
            ·
              refine ⟨4411581544138661718117947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941054362759107812078631 4411581544138661718117947)
              ·
                refine ⟨6617372316207992577176921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411581544138661718117947 6617372316207992577176921)
                ·
                  refine ⟨4963029237155994432882691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6617372316207992577176921 4963029237155994432882691)
                  ·
                    refine ⟨7444543855733991649324037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4963029237155994432882691 7444543855733991649324037)
                    ·
                      refine ⟨1395851972950123434248257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7444543855733991649324037 1395851972950123434248257)
                      ·
                        rfl

theorem cell23_2718412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2718412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718412 prefixEnd_2718412 := by exact prefixLift 2718412
  have htrace : WordTrace (prefixWord ++ tailWord_2718412) baseStart_2718412 baseEnd_2718412 := by
    simpa [prefixWord, tailWord_2718412, baseEnd_2718412] using wordTrace_append hprefix tailTrace_2718412
  have hstable : (prefixWord ++ tailWord_2718412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718412).length < 2 ^ (prefixWord ++ tailWord_2718412).sum := by decide
  have hdescent : baseEnd_2718412 < baseStart_2718412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718435 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 6]
def baseStart_2718435 : Nat := 118140960795 + 2718435 * 2 ^ 59
def prefixEnd_2718435 : Nat := 4983230072969 + 3 ^ 40 * 2718435 * 2
def baseEnd_2718435 : Nat := 155095975889464093806739

theorem tailTrace_2718435 : CollatzResearch.WordTrace tailWord_2718435 prefixEnd_2718435 155095975889464093806739 := by
  unfold tailWord_2718435
  simp only [CollatzResearch.WordTrace]
  refine ⟨99149469906581741580548759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66099646604387827720365839 99149469906581741580548759)
  ·
    refine ⟨148724204859872612370823139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99149469906581741580548759 148724204859872612370823139)
    ·
      refine ⟨223086307289808918556234709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148724204859872612370823139 223086307289808918556234709)
      ·
        refine ⟨5228585327104896528661751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 223086307289808918556234709 5228585327104896528661751)
        ·
          refine ⟨7842877990657344792992627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5228585327104896528661751 7842877990657344792992627)
          ·
            refine ⟨11764316985986017189488941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7842877990657344792992627 11764316985986017189488941)
            ·
              refine ⟨4411618869744756446058353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11764316985986017189488941 4411618869744756446058353)
              ·
                refine ⟨3308714152308567334543765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4411618869744756446058353 3308714152308567334543765)
                ·
                  refine ⟨155095975889464093806739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3308714152308567334543765 155095975889464093806739)
                  ·
                    rfl

theorem cell23_2718435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 6].length) (baseStart_2718435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718435 prefixEnd_2718435 := by exact prefixLift 2718435
  have htrace : WordTrace (prefixWord ++ tailWord_2718435) baseStart_2718435 baseEnd_2718435 := by
    simpa [prefixWord, tailWord_2718435, baseEnd_2718435] using wordTrace_append hprefix tailTrace_2718435
  have hstable : (prefixWord ++ tailWord_2718435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718435).length < 2 ^ (prefixWord ++ tailWord_2718435).sum := by decide
  have hdescent : baseEnd_2718435 < baseStart_2718435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718478 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_2718478 : Nat := 118140960795 + 2718478 * 2 ^ 59
def prefixEnd_2718478 : Nat := 4983230072969 + 3 ^ 40 * 2718478 * 2
def baseEnd_2718478 : Nat := 465295287557773392007651

theorem tailTrace_2718478 : CollatzResearch.WordTrace tailWord_2718478 prefixEnd_2718478 465295287557773392007651 := by
  unfold tailWord_2718478
  simp only [CollatzResearch.WordTrace]
  refine ⟨12393879780678244990545511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66100692163617306616242725 12393879780678244990545511)
  ·
    refine ⟨18590819671017367485818267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12393879780678244990545511 18590819671017367485818267)
    ·
      refine ⟨27886229506526051228727401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18590819671017367485818267 27886229506526051228727401)
      ·
        refine ⟨20914672129894538421545551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27886229506526051228727401 20914672129894538421545551)
        ·
          refine ⟨31372008194841807632318327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20914672129894538421545551 31372008194841807632318327)
          ·
            refine ⟨47058012292262711448477491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31372008194841807632318327 47058012292262711448477491)
            ·
              refine ⟨70587018438394067172716237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47058012292262711448477491 70587018438394067172716237)
              ·
                refine ⟨26470131914397775189768589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70587018438394067172716237 26470131914397775189768589)
                ·
                  refine ⟨9926299467899165696163221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26470131914397775189768589 9926299467899165696163221)
                  ·
                    refine ⟨465295287557773392007651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9926299467899165696163221 465295287557773392007651)
                    ·
                      rfl

theorem cell23_2718478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_2718478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718478 prefixEnd_2718478 := by exact prefixLift 2718478
  have htrace : WordTrace (prefixWord ++ tailWord_2718478) baseStart_2718478 baseEnd_2718478 := by
    simpa [prefixWord, tailWord_2718478, baseEnd_2718478] using wordTrace_append hprefix tailTrace_2718478
  have hstable : (prefixWord ++ tailWord_2718478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718478).length < 2 ^ (prefixWord ++ tailWord_2718478).sum := by decide
  have hdescent : baseEnd_2718478 < baseStart_2718478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718485 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_2718485 : Nat := 118140960795 + 2718485 * 2 ^ 59
def prefixEnd_2718485 : Nat := 4983230072969 + 3 ^ 40 * 2718485 * 2
def baseEnd_2718485 : Nat := 1395889457037901648635421

theorem tailTrace_2718485 : CollatzResearch.WordTrace tailWord_2718485 prefixEnd_2718485 1395889457037901648635421 := by
  unfold tailWord_2718485
  simp only [CollatzResearch.WordTrace]
  refine ⟨99151293556400600119868909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66100862370933733413245939 99151293556400600119868909)
  ·
    refine ⟨37181735083650225044950841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99151293556400600119868909 37181735083650225044950841)
    ·
      refine ⟨27886301312737668783713131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37181735083650225044950841 27886301312737668783713131)
      ·
        refine ⟨41829451969106503175569697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27886301312737668783713131 41829451969106503175569697)
        ·
          refine ⟨31372088976829877381677273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41829451969106503175569697 31372088976829877381677273)
          ·
            refine ⟨23529066732622408036257955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31372088976829877381677273 23529066732622408036257955)
            ·
              refine ⟨35293600098933612054386933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23529066732622408036257955 35293600098933612054386933)
              ·
                refine ⟨3308775009275026130098775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35293600098933612054386933 3308775009275026130098775)
                ·
                  refine ⟨4963162513912539195148163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3308775009275026130098775 4963162513912539195148163)
                  ·
                    refine ⟨7444743770868808792722245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4963162513912539195148163 7444743770868808792722245)
                    ·
                      refine ⟨1395889457037901648635421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7444743770868808792722245 1395889457037901648635421)
                      ·
                        rfl

theorem cell23_2718485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_2718485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718485 prefixEnd_2718485 := by exact prefixLift 2718485
  have htrace : WordTrace (prefixWord ++ tailWord_2718485) baseStart_2718485 baseEnd_2718485 := by
    simpa [prefixWord, tailWord_2718485, baseEnd_2718485] using wordTrace_append hprefix tailTrace_2718485
  have hstable : (prefixWord ++ tailWord_2718485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718485).length < 2 ^ (prefixWord ++ tailWord_2718485).sum := by decide
  have hdescent : baseEnd_2718485 < baseStart_2718485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718495 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 4, 4]
def baseStart_2718495 : Nat := 118140960795 + 2718495 * 2 ^ 59
def prefixEnd_2718495 : Nat := 4983230072969 + 3 ^ 40 * 2718495 * 2
def baseEnd_2718495 : Nat := 465298197281482203170125

theorem tailTrace_2718495 : CollatzResearch.WordTrace tailWord_2718495 prefixEnd_2718495 465298197281482203170125 := by
  unfold tailWord_2718495
  simp only [CollatzResearch.WordTrace]
  refine ⟨99151658286364371827732939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66101105524242914551821959 99151658286364371827732939)
  ·
    refine ⟨148727487429546557741599409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99151658286364371827732939 148727487429546557741599409)
    ·
      refine ⟨111545615572159918306199557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148727487429546557741599409 111545615572159918306199557)
      ·
        refine ⟨20914802919779984682412417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111545615572159918306199557 20914802919779984682412417)
        ·
          refine ⟨15686102189834988511809313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20914802919779984682412417 15686102189834988511809313)
          ·
            refine ⟨11764576642376241383856985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15686102189834988511809313 11764576642376241383856985)
            ·
              refine ⟨8823432481782181037892739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11764576642376241383856985 8823432481782181037892739)
              ·
                refine ⟨13235148722673271556839109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8823432481782181037892739 13235148722673271556839109)
                ·
                  refine ⟨2481590385501238416907333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13235148722673271556839109 2481590385501238416907333)
                  ·
                    refine ⟨465298197281482203170125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2481590385501238416907333 465298197281482203170125)
                    ·
                      rfl

theorem cell23_2718495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 4].length) (baseStart_2718495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718495 prefixEnd_2718495 := by exact prefixLift 2718495
  have htrace : WordTrace (prefixWord ++ tailWord_2718495) baseStart_2718495 baseEnd_2718495 := by
    simpa [prefixWord, tailWord_2718495, baseEnd_2718495] using wordTrace_append hprefix tailTrace_2718495
  have hstable : (prefixWord ++ tailWord_2718495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718495).length < 2 ^ (prefixWord ++ tailWord_2718495).sum := by decide
  have hdescent : baseEnd_2718495 < baseStart_2718495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718496 : List Nat := [2, 1, 1, 5, 1, 3, 3, 2, 1, 1, 3]
def baseStart_2718496 : Nat := 118140960795 + 2718496 * 2 ^ 59
def prefixEnd_2718496 : Nat := 4983230072969 + 3 ^ 40 * 2718496 * 2
def baseEnd_2718496 : Nat := 1395895105325101105597871

theorem tailTrace_2718496 : CollatzResearch.WordTrace tailWord_2718496 prefixEnd_2718496 1395895105325101105597871 := by
  unfold tailWord_2718496
  simp only [CollatzResearch.WordTrace]
  refine ⟨49575847379680374499259671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66101129839573832665679561 49575847379680374499259671)
  ·
    refine ⟨74363771069520561748889507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49575847379680374499259671 74363771069520561748889507)
    ·
      refine ⟨111545656604280842623334261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74363771069520561748889507 111545656604280842623334261)
      ·
        refine ⟨10457405306651328995937587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111545656604280842623334261 10457405306651328995937587)
        ·
          refine ⟨15686107959976993493906381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10457405306651328995937587 15686107959976993493906381)
          ·
            refine ⟨5882290484991372560214893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15686107959976993493906381 5882290484991372560214893)
            ·
              refine ⟨2205858931871764710080585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5882290484991372560214893 2205858931871764710080585)
              ·
                refine ⟨1654394198903823532560439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2205858931871764710080585 1654394198903823532560439)
                ·
                  refine ⟨2481591298355735298840659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1654394198903823532560439 2481591298355735298840659)
                  ·
                    refine ⟨3722386947533602948260989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2481591298355735298840659 3722386947533602948260989)
                    ·
                      refine ⟨1395895105325101105597871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3722386947533602948260989 1395895105325101105597871)
                      ·
                        rfl

theorem cell23_2718496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_2718496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718496 prefixEnd_2718496 := by exact prefixLift 2718496
  have htrace : WordTrace (prefixWord ++ tailWord_2718496) baseStart_2718496 baseEnd_2718496 := by
    simpa [prefixWord, tailWord_2718496, baseEnd_2718496] using wordTrace_append hprefix tailTrace_2718496
  have hstable : (prefixWord ++ tailWord_2718496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718496).length < 2 ^ (prefixWord ++ tailWord_2718496).sum := by decide
  have hdescent : baseEnd_2718496 < baseStart_2718496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718508 : List Nat := [2, 2, 1, 1, 1, 4, 4, 8]
def baseStart_2718508 : Nat := 118140960795 + 2718508 * 2 ^ 59
def prefixEnd_2718508 : Nat := 4983230072969 + 3 ^ 40 * 2718508 * 2
def baseEnd_2718508 : Nat := 51700046929368705875845

theorem tailTrace_2718508 : CollatzResearch.WordTrace tailWord_2718508 prefixEnd_2718508 51700046929368705875845 := by
  unfold tailWord_2718508
  simp only [CollatzResearch.WordTrace]
  refine ⟨49576066217658637523978089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66101421623544850031970785 49576066217658637523978089)
  ·
    refine ⟨37182049663243978142983567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49576066217658637523978089 37182049663243978142983567)
    ·
      refine ⟨55773074494865967214475351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37182049663243978142983567 55773074494865967214475351)
      ·
        refine ⟨83659611742298950821713027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55773074494865967214475351 83659611742298950821713027)
        ·
          refine ⟨125489417613448426232569541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83659611742298950821713027 125489417613448426232569541)
          ·
            refine ⟨23529265802521579918606789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125489417613448426232569541 23529265802521579918606789)
            ·
              refine ⟨4411737337972796234738773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23529265802521579918606789 4411737337972796234738773)
              ·
                refine ⟨51700046929368705875845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4411737337972796234738773 51700046929368705875845)
                ·
                  rfl

theorem cell23_2718508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 8].length) (baseStart_2718508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718508 prefixEnd_2718508 := by exact prefixLift 2718508
  have htrace : WordTrace (prefixWord ++ tailWord_2718508) baseStart_2718508 baseEnd_2718508 := by
    simpa [prefixWord, tailWord_2718508, baseEnd_2718508] using wordTrace_append hprefix tailTrace_2718508
  have hstable : (prefixWord ++ tailWord_2718508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718508).length < 2 ^ (prefixWord ++ tailWord_2718508).sum := by decide
  have hdescent : baseEnd_2718508 < baseStart_2718508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718516 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_2718516 : Nat := 118140960795 + 2718516 * 2 ^ 59
def prefixEnd_2718516 : Nat := 4983230072969 + 3 ^ 40 * 2718516 * 2
def baseEnd_2718516 : Nat := 465301791646063675782593

theorem tailTrace_2718516 : CollatzResearch.WordTrace tailWord_2718516 prefixEnd_2718516 465301791646063675782593 := by
  unfold tailWord_2718516
  simp only [CollatzResearch.WordTrace]
  refine ⟨49576212109644146207123701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66101616146192194942831601 49576212109644146207123701)
  ·
    refine ⟨4647769885279138706917847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49576212109644146207123701 4647769885279138706917847)
    ·
      refine ⟨6971654827918708060376771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4647769885279138706917847 6971654827918708060376771)
      ·
        refine ⟨10457482241878062090565157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6971654827918708060376771 10457482241878062090565157)
        ·
          refine ⟨1960777920352136641980967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10457482241878062090565157 1960777920352136641980967)
          ·
            refine ⟨2941166880528204962971451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1960777920352136641980967 2941166880528204962971451)
            ·
              refine ⟨4411750320792307444457177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941166880528204962971451 4411750320792307444457177)
              ·
                refine ⟨3308812740594230583342883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4411750320792307444457177 3308812740594230583342883)
                ·
                  refine ⟨4963219110891345875014325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3308812740594230583342883 4963219110891345875014325)
                  ·
                    refine ⟨465301791646063675782593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4963219110891345875014325 465301791646063675782593)
                    ·
                      rfl

theorem cell23_2718516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_2718516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718516 prefixEnd_2718516 := by exact prefixLift 2718516
  have htrace : WordTrace (prefixWord ++ tailWord_2718516) baseStart_2718516 baseEnd_2718516 := by
    simpa [prefixWord, tailWord_2718516, baseEnd_2718516] using wordTrace_append hprefix tailTrace_2718516
  have hstable : (prefixWord ++ tailWord_2718516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718516).length < 2 ^ (prefixWord ++ tailWord_2718516).sum := by decide
  have hdescent : baseEnd_2718516 < baseStart_2718516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718522 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3]
def baseStart_2718522 : Nat := 118140960795 + 2718522 * 2 ^ 59
def prefixEnd_2718522 : Nat := 4983230072969 + 3 ^ 40 * 2718522 * 2
def baseEnd_2718522 : Nat := 1395908455822118003872751

theorem tailTrace_2718522 : CollatzResearch.WordTrace tailWord_2718522 prefixEnd_2718522 1395908455822118003872751 := by
  unfold tailWord_2718522
  simp only [CollatzResearch.WordTrace]
  refine ⟨24788160764316638859741455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66101762038177703625977213 24788160764316638859741455)
  ·
    refine ⟨37182241146474958289612183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24788160764316638859741455 37182241146474958289612183)
    ·
      refine ⟨55773361719712437434418275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37182241146474958289612183 55773361719712437434418275)
      ·
        refine ⟨83660042579568656151627413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55773361719712437434418275 83660042579568656151627413)
        ·
          refine ⟨3921564495917280757107535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83660042579568656151627413 3921564495917280757107535)
          ·
            refine ⟨5882346743875921135661303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3921564495917280757107535 5882346743875921135661303)
            ·
              refine ⟨8823520115813881703491955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5882346743875921135661303 8823520115813881703491955)
              ·
                refine ⟨13235280173720822555237933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8823520115813881703491955 13235280173720822555237933)
                ·
                  refine ⟨4963230065145308458214225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13235280173720822555237933 4963230065145308458214225)
                  ·
                    refine ⟨3722422548858981343660669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4963230065145308458214225 3722422548858981343660669)
                    ·
                      refine ⟨1395908455822118003872751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3722422548858981343660669 1395908455822118003872751)
                      ·
                        rfl

theorem cell23_2718522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_2718522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718522 prefixEnd_2718522 := by exact prefixLift 2718522
  have htrace : WordTrace (prefixWord ++ tailWord_2718522) baseStart_2718522 baseEnd_2718522 := by
    simpa [prefixWord, tailWord_2718522, baseEnd_2718522] using wordTrace_append hprefix tailTrace_2718522
  have hstable : (prefixWord ++ tailWord_2718522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718522).length < 2 ^ (prefixWord ++ tailWord_2718522).sum := by decide
  have hdescent : baseEnd_2718522 < baseStart_2718522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718553 : List Nat := [1, 2, 1, 2, 2, 6, 2, 2, 1, 2, 2]
def baseStart_2718553 : Nat := 118140960795 + 2718553 * 2 ^ 59
def prefixEnd_2718553 : Nat := 4983230072969 + 3 ^ 40 * 2718553 * 2
def baseEnd_2718553 : Nat := 1395924373722407382585109

theorem tailTrace_2718553 : CollatzResearch.WordTrace tailWord_2718553 prefixEnd_2718553 1395924373722407382585109 := by
  unfold tailWord_2718553
  simp only [CollatzResearch.WordTrace]
  refine ⟨99153773720154247733344313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66102515813436165155562875 99153773720154247733344313)
  ·
    refine ⟨74365330290115685800008235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99153773720154247733344313 74365330290115685800008235)
    ·
      refine ⟨111547995435173528700012353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74365330290115685800008235 111547995435173528700012353)
      ·
        refine ⟨83660996576380146525009265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111547995435173528700012353 83660996576380146525009265)
        ·
          refine ⟨62745747432285109893756949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83660996576380146525009265 62745747432285109893756949)
          ·
            refine ⟨2941206910888364526269857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62745747432285109893756949 2941206910888364526269857)
            ·
              refine ⟨2205905183166273394702393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2941206910888364526269857 2205905183166273394702393)
              ·
                refine ⟨1654428887374705046026795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2205905183166273394702393 1654428887374705046026795)
                ·
                  refine ⟨2481643331062057569040193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1654428887374705046026795 2481643331062057569040193)
                  ·
                    refine ⟨1861232498296543176780145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2481643331062057569040193 1861232498296543176780145)
                    ·
                      refine ⟨1395924373722407382585109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861232498296543176780145 1395924373722407382585109)
                      ·
                        rfl

theorem cell23_2718553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 1, 2, 2].length) (baseStart_2718553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718553 prefixEnd_2718553 := by exact prefixLift 2718553
  have htrace : WordTrace (prefixWord ++ tailWord_2718553) baseStart_2718553 baseEnd_2718553 := by
    simpa [prefixWord, tailWord_2718553, baseEnd_2718553] using wordTrace_append hprefix tailTrace_2718553
  have hstable : (prefixWord ++ tailWord_2718553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718553).length < 2 ^ (prefixWord ++ tailWord_2718553).sum := by decide
  have hdescent : baseEnd_2718553 < baseStart_2718553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718590 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2718590 : Nat := 118140960795 + 2718590 * 2 ^ 59
def prefixEnd_2718590 : Nat := 4983230072969 + 3 ^ 40 * 2718590 * 2
def baseEnd_2718590 : Nat := 1395943372506623737822439

theorem tailTrace_2718590 : CollatzResearch.WordTrace tailWord_2718590 prefixEnd_2718590 1395943372506623737822439 := by
  unfold tailWord_2718590
  simp only [CollatzResearch.WordTrace]
  refine ⟨12394390402627525381555153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66103415480680135368294149 12394390402627525381555153)
  ·
    refine ⟨9295792801970644036166365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12394390402627525381555153 9295792801970644036166365)
    ·
      refine ⟨3485922300738991513562387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9295792801970644036166365 3485922300738991513562387)
      ·
        refine ⟨5228883451108487270343581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3485922300738991513562387 5228883451108487270343581)
        ·
          refine ⟨1960831294165682726378843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5228883451108487270343581 1960831294165682726378843)
          ·
            refine ⟨2941246941248524089568265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1960831294165682726378843 2941246941248524089568265)
            ·
              refine ⟨2205935205936393067176199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2941246941248524089568265 2205935205936393067176199)
              ·
                refine ⟨3308902808904589600764299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205935205936393067176199 3308902808904589600764299)
                ·
                  refine ⟨4963354213356884401146449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3308902808904589600764299 4963354213356884401146449)
                  ·
                    refine ⟨3722515660017663300859837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4963354213356884401146449 3722515660017663300859837)
                    ·
                      refine ⟨1395943372506623737822439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3722515660017663300859837 1395943372506623737822439)
                      ·
                        rfl

theorem cell23_2718590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2718590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718590 prefixEnd_2718590 := by exact prefixLift 2718590
  have htrace : WordTrace (prefixWord ++ tailWord_2718590) baseStart_2718590 baseEnd_2718590 := by
    simpa [prefixWord, tailWord_2718590, baseEnd_2718590] using wordTrace_append hprefix tailTrace_2718590
  have hstable : (prefixWord ++ tailWord_2718590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718590).length < 2 ^ (prefixWord ++ tailWord_2718590).sum := by decide
  have hdescent : baseEnd_2718590 < baseStart_2718590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718615 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 7]
def baseStart_2718615 : Nat := 118140960795 + 2718615 * 2 ^ 59
def prefixEnd_2718615 : Nat := 4983230072969 + 3 ^ 40 * 2718615 * 2
def baseEnd_2718615 : Nat := 155106245502554015556647

theorem tailTrace_2718615 : CollatzResearch.WordTrace tailWord_2718615 prefixEnd_2718615 155106245502554015556647 := by
  unfold tailWord_2718615
  simp only [CollatzResearch.WordTrace]
  refine ⟨99156035045929632322101299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66104023363953088214734199 99156035045929632322101299)
  ·
    refine ⟨148734052568894448483151949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99156035045929632322101299 148734052568894448483151949)
    ·
      refine ⟨55775269713335418181181981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148734052568894448483151949 55775269713335418181181981)
      ·
        refine ⟨20915726142500781817943243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55775269713335418181181981 20915726142500781817943243)
        ·
          refine ⟨31373589213751172726914865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20915726142500781817943243 31373589213751172726914865)
          ·
            refine ⟨23530191910313379545186149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31373589213751172726914865 23530191910313379545186149)
            ·
              refine ⟨4411910983183758664722403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23530191910313379545186149 4411910983183758664722403)
              ·
                refine ⟨6617866474775637997083605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411910983183758664722403 6617866474775637997083605)
                ·
                  refine ⟨155106245502554015556647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6617866474775637997083605 155106245502554015556647)
                  ·
                    rfl

theorem cell23_2718615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 7].length) (baseStart_2718615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718615 prefixEnd_2718615 := by exact prefixLift 2718615
  have htrace : WordTrace (prefixWord ++ tailWord_2718615) baseStart_2718615 baseEnd_2718615 := by
    simpa [prefixWord, tailWord_2718615, baseEnd_2718615] using wordTrace_append hprefix tailTrace_2718615
  have hstable : (prefixWord ++ tailWord_2718615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718615).length < 2 ^ (prefixWord ++ tailWord_2718615).sum := by decide
  have hdescent : baseEnd_2718615 < baseStart_2718615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718626 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_2718626 : Nat := 118140960795 + 2718626 * 2 ^ 59
def prefixEnd_2718626 : Nat := 4983230072969 + 3 ^ 40 * 2718626 * 2
def baseEnd_2718626 : Nat := 1395961857810185596972273

theorem tailTrace_2718626 : CollatzResearch.WordTrace tailWord_2718626 prefixEnd_2718626 1395961857810185596972273 := by
  unfold tailWord_2718626
  simp only [CollatzResearch.WordTrace]
  refine ⟨24789109062222445300187933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66104290832593187467167821 24789109062222445300187933)
  ·
    refine ⟨9295915898333416987570475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24789109062222445300187933 9295915898333416987570475)
    ·
      refine ⟨13943873847500125481355713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9295915898333416987570475 13943873847500125481355713)
      ·
        refine ⟨10457905385625094111016785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13943873847500125481355713 10457905385625094111016785)
        ·
          refine ⟨7843429039218820583262589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10457905385625094111016785 7843429039218820583262589)
          ·
            refine ⟨2941285889707057718723471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7843429039218820583262589 2941285889707057718723471)
            ·
              refine ⟨4411928834560586578085207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941285889707057718723471 4411928834560586578085207)
              ·
                refine ⟨6617893251840879867127811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411928834560586578085207 6617893251840879867127811)
                ·
                  refine ⟨9926839877761319800691717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6617893251840879867127811 9926839877761319800691717)
                  ·
                    refine ⟨1861282477080247462629697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9926839877761319800691717 1861282477080247462629697)
                    ·
                      refine ⟨1395961857810185596972273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861282477080247462629697 1395961857810185596972273)
                      ·
                        rfl

theorem cell23_2718626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_2718626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718626 prefixEnd_2718626 := by exact prefixLift 2718626
  have htrace : WordTrace (prefixWord ++ tailWord_2718626) baseStart_2718626 baseEnd_2718626 := by
    simpa [prefixWord, tailWord_2718626, baseEnd_2718626] using wordTrace_append hprefix tailTrace_2718626
  have hstable : (prefixWord ++ tailWord_2718626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718626).length < 2 ^ (prefixWord ++ tailWord_2718626).sum := by decide
  have hdescent : baseEnd_2718626 < baseStart_2718626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718645 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2718645 : Nat := 118140960795 + 2718645 * 2 ^ 59
def prefixEnd_2718645 : Nat := 4983230072969 + 3 ^ 40 * 2718645 * 2
def baseEnd_2718645 : Nat := 465323871314207007544895

theorem tailTrace_2718645 : CollatzResearch.WordTrace tailWord_2718645 prefixEnd_2718645 465323871314207007544895 := by
  unfold tailWord_2718645
  simp only [CollatzResearch.WordTrace]
  refine ⟨99157129235820947445693389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66104752823880631630462259 99157129235820947445693389)
  ·
    refine ⟨37183923463432855292135021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99157129235820947445693389 37183923463432855292135021)
    ·
      refine ⟨13943971298787320734550633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37183923463432855292135021 13943971298787320734550633)
      ·
        refine ⟨10457978474090490550912975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13943971298787320734550633 10457978474090490550912975)
        ·
          refine ⟨15686967711135735826369463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10457978474090490550912975 15686967711135735826369463)
          ·
            refine ⟨23530451566703603739554195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15686967711135735826369463 23530451566703603739554195)
            ·
              refine ⟨35295677350055405609331293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23530451566703603739554195 35295677350055405609331293)
              ·
                refine ⟨13235879006270777103499235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35295677350055405609331293 13235879006270777103499235)
                ·
                  refine ⟨19853818509406165655248853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13235879006270777103499235 19853818509406165655248853)
                  ·
                    refine ⟨465323871314207007544895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19853818509406165655248853 465323871314207007544895)
                    ·
                      rfl

theorem cell23_2718645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2718645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718645 prefixEnd_2718645 := by exact prefixLift 2718645
  have htrace : WordTrace (prefixWord ++ tailWord_2718645) baseStart_2718645 baseEnd_2718645 := by
    simpa [prefixWord, tailWord_2718645, baseEnd_2718645] using wordTrace_append hprefix tailTrace_2718645
  have hstable : (prefixWord ++ tailWord_2718645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718645).length < 2 ^ (prefixWord ++ tailWord_2718645).sum := by decide
  have hdescent : baseEnd_2718645 < baseStart_2718645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718649 : List Nat := [1, 2, 1, 4, 2, 4, 1, 3, 5]
def baseStart_2718649 : Nat := 118140960795 + 2718649 * 2 ^ 59
def prefixEnd_2718649 : Nat := 4983230072969 + 3 ^ 40 * 2718649 * 2
def baseEnd_2718649 : Nat := 155108185318359889664963

theorem tailTrace_2718649 : CollatzResearch.WordTrace tailWord_2718649 prefixEnd_2718649 155108185318359889664963 := by
  unfold tailWord_2718649
  simp only [CollatzResearch.WordTrace]
  refine ⟨99157275127806456128839001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66104850085204304085892667 99157275127806456128839001)
  ·
    refine ⟨74367956345854842096629251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99157275127806456128839001 74367956345854842096629251)
    ·
      refine ⟨111551934518782263144943877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74367956345854842096629251 111551934518782263144943877)
      ·
        refine ⟨20915987722271674339676977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111551934518782263144943877 20915987722271674339676977)
        ·
          refine ⟨15686990791703755754757733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20915987722271674339676977 15686990791703755754757733)
          ·
            refine ⟨2941310773444454204017075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15686990791703755754757733 2941310773444454204017075)
            ·
              refine ⟨4411966160166681306025613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941310773444454204017075 4411966160166681306025613)
              ·
                refine ⟨1654487310062505489759605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4411966160166681306025613 1654487310062505489759605)
                ·
                  refine ⟨155108185318359889664963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1654487310062505489759605 155108185318359889664963)
                  ·
                    rfl

theorem cell23_2718649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 5].length) (baseStart_2718649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718649 prefixEnd_2718649 := by exact prefixLift 2718649
  have htrace : WordTrace (prefixWord ++ tailWord_2718649) baseStart_2718649 baseEnd_2718649 := by
    simpa [prefixWord, tailWord_2718649, baseEnd_2718649] using wordTrace_append hprefix tailTrace_2718649
  have hstable : (prefixWord ++ tailWord_2718649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718649).length < 2 ^ (prefixWord ++ tailWord_2718649).sum := by decide
  have hdescent : baseEnd_2718649 < baseStart_2718649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718725 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_2718725 : Nat := 118140960795 + 2718725 * 2 ^ 59
def prefixEnd_2718725 : Nat := 4983230072969 + 3 ^ 40 * 2718725 * 2
def baseEnd_2718725 : Nat := 1396012692394980709634317

theorem tailTrace_2718725 : CollatzResearch.WordTrace tailWord_2718725 prefixEnd_2718725 1396012692394980709634317 := by
  unfold tailWord_2718725
  simp only [CollatzResearch.WordTrace]
  refine ⟨99160047075531121108605629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66106698050354080739070419 99160047075531121108605629)
  ·
    refine ⟨37185017653324170415727111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99160047075531121108605629 37185017653324170415727111)
    ·
      refine ⟨55777526479986255623590667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37185017653324170415727111 55777526479986255623590667)
      ·
        refine ⟨83666289719979383435386001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55777526479986255623590667 83666289719979383435386001)
        ·
          refine ⟨62749717289984537576539501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83666289719979383435386001 62749717289984537576539501)
          ·
            refine ⟨23531143983744201591202313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62749717289984537576539501 23531143983744201591202313)
            ·
              refine ⟨17648357987808151193401735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23531143983744201591202313 17648357987808151193401735)
              ·
                refine ⟨26472536981712226790102603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17648357987808151193401735 26472536981712226790102603)
                ·
                  refine ⟨39708805472568340185153905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26472536981712226790102603 39708805472568340185153905)
                  ·
                    refine ⟨29781604104426255138865429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39708805472568340185153905 29781604104426255138865429)
                    ·
                      refine ⟨1396012692394980709634317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29781604104426255138865429 1396012692394980709634317)
                      ·
                        rfl

theorem cell23_2718725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_2718725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718725 prefixEnd_2718725 := by exact prefixLift 2718725
  have htrace : WordTrace (prefixWord ++ tailWord_2718725) baseStart_2718725 baseEnd_2718725 := by
    simpa [prefixWord, tailWord_2718725, baseEnd_2718725] using wordTrace_append hprefix tailTrace_2718725
  have hstable : (prefixWord ++ tailWord_2718725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718725).length < 2 ^ (prefixWord ++ tailWord_2718725).sum := by decide
  have hdescent : baseEnd_2718725 < baseStart_2718725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718792 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2718792 : Nat := 118140960795 + 2718792 * 2 ^ 59
def prefixEnd_2718792 : Nat := 4983230072969 + 3 ^ 40 * 2718792 * 2
def baseEnd_2718792 : Nat := 1396047095598831947496509

theorem tailTrace_2718792 : CollatzResearch.WordTrace tailWord_2718792 prefixEnd_2718792 1396047095598831947496509 := by
  unfold tailWord_2718792
  simp only [CollatzResearch.WordTrace]
  refine ⟨49581245383144195775647315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66108327177525594367529753 49581245383144195775647315)
  ·
    refine ⟨74371868074716293663470973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49581245383144195775647315 74371868074716293663470973)
    ·
      refine ⟨27889450528018610123801615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74371868074716293663470973 27889450528018610123801615)
      ·
        refine ⟨41834175792027915185702423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27889450528018610123801615 41834175792027915185702423)
        ·
          refine ⟨62751263688041872778553635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41834175792027915185702423 62751263688041872778553635)
          ·
            refine ⟨94126895532062809167830453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62751263688041872778553635 94126895532062809167830453)
            ·
              refine ⟨8824396456130888359484105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94126895532062809167830453 8824396456130888359484105)
              ·
                refine ⟨6618297342098166269613079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8824396456130888359484105 6618297342098166269613079)
                ·
                  refine ⟨9927446013147249404419619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6618297342098166269613079 9927446013147249404419619)
                  ·
                    refine ⟨14891169019720874106629429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9927446013147249404419619 14891169019720874106629429)
                    ·
                      refine ⟨1396047095598831947496509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14891169019720874106629429 1396047095598831947496509)
                      ·
                        rfl

theorem cell23_2718792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2718792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718792 prefixEnd_2718792 := by exact prefixLift 2718792
  have htrace : WordTrace (prefixWord ++ tailWord_2718792) baseStart_2718792 baseEnd_2718792 := by
    simpa [prefixWord, tailWord_2718792, baseEnd_2718792] using wordTrace_append hprefix tailTrace_2718792
  have hstable : (prefixWord ++ tailWord_2718792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718792).length < 2 ^ (prefixWord ++ tailWord_2718792).sum := by decide
  have hdescent : baseEnd_2718792 < baseStart_2718792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718812 : List Nat := [2, 2, 4, 1, 1, 1, 3, 9]
def baseStart_2718812 : Nat := 118140960795 + 2718812 * 2 ^ 59
def prefixEnd_2718812 : Nat := 4983230072969 + 3 ^ 40 * 2718812 * 2
def baseEnd_2718812 : Nat := 51705828341182291453571

theorem tailTrace_2718812 : CollatzResearch.WordTrace tailWord_2718812 prefixEnd_2718812 51705828341182291453571 := by
  unfold tailWord_2718812
  simp only [CollatzResearch.WordTrace]
  refine ⟨49581610113107967483511345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66108813484143956644681793 49581610113107967483511345)
  ·
    refine ⟨37186207584830975612633509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49581610113107967483511345 37186207584830975612633509)
    ·
      refine ⟨6972413922155807927368783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37186207584830975612633509 6972413922155807927368783)
      ·
        refine ⟨10458620883233711891053175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6972413922155807927368783 10458620883233711891053175)
        ·
          refine ⟨15687931324850567836579763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10458620883233711891053175 15687931324850567836579763)
          ·
            refine ⟨23531896987275851754869645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15687931324850567836579763 23531896987275851754869645)
            ·
              refine ⟨8824461370228444408076117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23531896987275851754869645 8824461370228444408076117)
              ·
                refine ⟨51705828341182291453571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8824461370228444408076117 51705828341182291453571)
                ·
                  rfl

theorem cell23_2718812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 9].length) (baseStart_2718812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718812 prefixEnd_2718812 := by exact prefixLift 2718812
  have htrace : WordTrace (prefixWord ++ tailWord_2718812) baseStart_2718812 baseEnd_2718812 := by
    simpa [prefixWord, tailWord_2718812, baseEnd_2718812] using wordTrace_append hprefix tailTrace_2718812
  have hstable : (prefixWord ++ tailWord_2718812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718812).length < 2 ^ (prefixWord ++ tailWord_2718812).sum := by decide
  have hdescent : baseEnd_2718812 < baseStart_2718812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718826 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2718826 : Nat := 118140960795 + 2718826 * 2 ^ 59
def prefixEnd_2718826 : Nat := 4983230072969 + 3 ^ 40 * 2718826 * 2
def baseEnd_2718826 : Nat := 1396064553941084814471353

theorem tailTrace_2718826 : CollatzResearch.WordTrace tailWord_2718826 prefixEnd_2718826 1396064553941084814471353 := by
  unfold tailWord_2718826
  simp only [CollatzResearch.WordTrace]
  refine ⟨24790932712041303839508083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66109153898776810238688221 24790932712041303839508083)
  ·
    refine ⟨37186399068061955759262125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24790932712041303839508083 37186399068061955759262125)
    ·
      refine ⟨13944899650523233409723297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37186399068061955759262125 13944899650523233409723297)
      ·
        refine ⟨10458674737892425057292473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13944899650523233409723297 10458674737892425057292473)
        ·
          refine ⟨7844006053419318792969355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10458674737892425057292473 7844006053419318792969355)
          ·
            refine ⟨11766009080128978189454033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7844006053419318792969355 11766009080128978189454033)
            ·
              refine ⟨8824506810096733642090525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11766009080128978189454033 8824506810096733642090525)
              ·
                refine ⟨3309190053786275115783947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8824506810096733642090525 3309190053786275115783947)
                ·
                  refine ⟨4963785080679412673675921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3309190053786275115783947 4963785080679412673675921)
                  ·
                    refine ⟨3722838810509559505256941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4963785080679412673675921 3722838810509559505256941)
                    ·
                      refine ⟨1396064553941084814471353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3722838810509559505256941 1396064553941084814471353)
                      ·
                        rfl

theorem cell23_2718826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2718826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718826 prefixEnd_2718826 := by exact prefixLift 2718826
  have htrace : WordTrace (prefixWord ++ tailWord_2718826) baseStart_2718826 baseEnd_2718826 := by
    simpa [prefixWord, tailWord_2718826, baseEnd_2718826] using wordTrace_append hprefix tailTrace_2718826
  have hstable : (prefixWord ++ tailWord_2718826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718826).length < 2 ^ (prefixWord ++ tailWord_2718826).sum := by decide
  have hdescent : baseEnd_2718826 < baseStart_2718826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718839 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 4, 1, 3]
def baseStart_2718839 : Nat := 118140960795 + 2718839 * 2 ^ 59
def prefixEnd_2718839 : Nat := 4983230072969 + 3 ^ 40 * 2718839 * 2
def baseEnd_2718839 : Nat := 1396071229189593263608793

theorem tailTrace_2718839 : CollatzResearch.WordTrace tailWord_2718839 prefixEnd_2718839 1396071229189593263608793 := by
  unfold tailWord_2718839
  simp only [CollatzResearch.WordTrace]
  refine ⟨99164204997118118578255571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66109469998078745718837047 99164204997118118578255571)
  ·
    refine ⟨148746307495677177867383357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99164204997118118578255571 148746307495677177867383357)
    ·
      refine ⟨55779865310878941700268759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148746307495677177867383357 55779865310878941700268759)
      ·
        refine ⟨83669797966318412550403139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55779865310878941700268759 83669797966318412550403139)
        ·
          refine ⟨125504696949477618825604709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83669797966318412550403139 125504696949477618825604709)
          ·
            refine ⟨23532130678027053529800883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125504696949477618825604709 23532130678027053529800883)
            ·
              refine ⟨35298196017040580294701325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23532130678027053529800883 35298196017040580294701325)
              ·
                refine ⟨13236823506390217610512997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35298196017040580294701325 13236823506390217610512997)
                ·
                  refine ⟨2481904407448165801971187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13236823506390217610512997 2481904407448165801971187)
                  ·
                    refine ⟨3722856611172248702956781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2481904407448165801971187 3722856611172248702956781)
                    ·
                      refine ⟨1396071229189593263608793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3722856611172248702956781 1396071229189593263608793)
                      ·
                        rfl

theorem cell23_2718839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_2718839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718839 prefixEnd_2718839 := by exact prefixLift 2718839
  have htrace : WordTrace (prefixWord ++ tailWord_2718839) baseStart_2718839 baseEnd_2718839 := by
    simpa [prefixWord, tailWord_2718839, baseEnd_2718839] using wordTrace_append hprefix tailTrace_2718839
  have hstable : (prefixWord ++ tailWord_2718839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718839).length < 2 ^ (prefixWord ++ tailWord_2718839).sum := by decide
  have hdescent : baseEnd_2718839 < baseStart_2718839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718890 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2718890 : Nat := 118140960795 + 2718890 * 2 ^ 59
def prefixEnd_2718890 : Nat := 4983230072969 + 3 ^ 40 * 2718890 * 2
def baseEnd_2718890 : Nat := 1396097416702972564071059

theorem tailTrace_2718890 : CollatzResearch.WordTrace tailWord_2718890 prefixEnd_2718890 1396097416702972564071059 := by
  unfold tailWord_2718890
  simp only [CollatzResearch.WordTrace]
  refine ⟨24791516279983338572090531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66110710079955569525574749 24791516279983338572090531)
  ·
    refine ⟨37187274419975007858135797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24791516279983338572090531 37187274419975007858135797)
    ·
      refine ⟨3486306976872656986700231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37187274419975007858135797 3486306976872656986700231)
      ·
        refine ⟨5229460465308985480050347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3486306976872656986700231 5229460465308985480050347)
        ·
          refine ⟨7844190697963478220075521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5229460465308985480050347 7844190697963478220075521)
          ·
            refine ⟨5883143023472608665056641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7844190697963478220075521 5883143023472608665056641)
            ·
              refine ⟨4412357267604456498792481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5883143023472608665056641 4412357267604456498792481)
              ·
                refine ⟨3309267950703342374094361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4412357267604456498792481 3309267950703342374094361)
                ·
                  refine ⟨2481950963027506780570771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3309267950703342374094361 2481950963027506780570771)
                  ·
                    refine ⟨3722926444541260170856157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2481950963027506780570771 3722926444541260170856157)
                    ·
                      refine ⟨1396097416702972564071059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3722926444541260170856157 1396097416702972564071059)
                      ·
                        rfl

theorem cell23_2718890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2718890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718890 prefixEnd_2718890 := by exact prefixLift 2718890
  have htrace : WordTrace (prefixWord ++ tailWord_2718890) baseStart_2718890 baseEnd_2718890 := by
    simpa [prefixWord, tailWord_2718890, baseEnd_2718890] using wordTrace_append hprefix tailTrace_2718890
  have hstable : (prefixWord ++ tailWord_2718890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718890).length < 2 ^ (prefixWord ++ tailWord_2718890).sum := by decide
  have hdescent : baseEnd_2718890 < baseStart_2718890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718913 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_2718913 : Nat := 118140960795 + 2718913 * 2 ^ 59
def prefixEnd_2718913 : Nat := 4983230072969 + 3 ^ 40 * 2718913 * 2
def baseEnd_2718913 : Nat := 1396109226758025974083453

theorem tailTrace_2718913 : CollatzResearch.WordTrace tailWord_2718913 prefixEnd_2718913 1396109226758025974083453 := by
  unfold tailWord_2718913
  simp only [CollatzResearch.WordTrace]
  refine ⟨99166903998850029216449393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66111269332566686144299595 99166903998850029216449393)
  ·
    refine ⟨74375177999137521912337045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99166903998850029216449393 74375177999137521912337045)
    ·
      refine ⟨3486336468709571339640799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74375177999137521912337045 3486336468709571339640799)
      ·
        refine ⟨5229504703064357009461199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3486336468709571339640799 5229504703064357009461199)
        ·
          refine ⟨7844257054596535514191799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5229504703064357009461199 7844257054596535514191799)
          ·
            refine ⟨11766385581894803271287699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7844257054596535514191799 11766385581894803271287699)
            ·
              refine ⟨17649578372842204906931549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11766385581894803271287699 17649578372842204906931549)
              ·
                refine ⟨6618591889815826840099331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17649578372842204906931549 6618591889815826840099331)
                ·
                  refine ⟨9927887834723740260148997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6618591889815826840099331 9927887834723740260148997)
                  ·
                    refine ⟨1861478969010701298777937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9927887834723740260148997 1861478969010701298777937)
                    ·
                      refine ⟨1396109226758025974083453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861478969010701298777937 1396109226758025974083453)
                      ·
                        rfl

theorem cell23_2718913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_2718913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718913 prefixEnd_2718913 := by exact prefixLift 2718913
  have htrace : WordTrace (prefixWord ++ tailWord_2718913) baseStart_2718913 baseEnd_2718913 := by
    simpa [prefixWord, tailWord_2718913, baseEnd_2718913] using wordTrace_append hprefix tailTrace_2718913
  have hstable : (prefixWord ++ tailWord_2718913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718913).length < 2 ^ (prefixWord ++ tailWord_2718913).sum := by decide
  have hdescent : baseEnd_2718913 < baseStart_2718913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718934 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_2718934 : Nat := 118140960795 + 2718934 * 2 ^ 59
def prefixEnd_2718934 : Nat := 4983230072969 + 3 ^ 40 * 2718934 * 2
def baseEnd_2718934 : Nat := 1396120009851770391920857

theorem tailTrace_2718934 : CollatzResearch.WordTrace tailWord_2718934 prefixEnd_2718934 1396120009851770391920857 := by
  unfold tailWord_2718934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6197979370735871862685241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66111779954515966535309237 6197979370735871862685241)
  ·
    refine ⟨4648484528051903897013931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6197979370735871862685241 4648484528051903897013931)
    ·
      refine ⟨6972726792077855845520897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4648484528051903897013931 6972726792077855845520897)
      ·
        refine ⟨5229545094058391884140673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6972726792077855845520897 5229545094058391884140673)
        ·
          refine ⟨3922158820543793913105505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5229545094058391884140673 3922158820543793913105505)
          ·
            refine ⟨2941619115407845434829129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3922158820543793913105505 2941619115407845434829129)
            ·
              refine ⟨2206214336555884076121847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2941619115407845434829129 2206214336555884076121847)
              ·
                refine ⟨3309321504833826114182771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206214336555884076121847 3309321504833826114182771)
                ·
                  refine ⟨4963982257250739171274157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3309321504833826114182771 4963982257250739171274157)
                  ·
                    refine ⟨1861493346469027189227809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4963982257250739171274157 1861493346469027189227809)
                    ·
                      refine ⟨1396120009851770391920857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861493346469027189227809 1396120009851770391920857)
                      ·
                        rfl

theorem cell23_2718934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_2718934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718934 prefixEnd_2718934 := by exact prefixLift 2718934
  have htrace : WordTrace (prefixWord ++ tailWord_2718934) baseStart_2718934 baseEnd_2718934 := by
    simpa [prefixWord, tailWord_2718934, baseEnd_2718934] using wordTrace_append hprefix tailTrace_2718934
  have hstable : (prefixWord ++ tailWord_2718934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718934).length < 2 ^ (prefixWord ++ tailWord_2718934).sum := by decide
  have hdescent : baseEnd_2718934 < baseStart_2718934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718964 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2718964 : Nat := 118140960795 + 2718964 * 2 ^ 59
def prefixEnd_2718964 : Nat := 4983230072969 + 3 ^ 40 * 2718964 * 2
def baseEnd_2718964 : Nat := 1396135414271405274545719

theorem tailTrace_2718964 : CollatzResearch.WordTrace tailWord_2718964 prefixEnd_2718964 1396135414271405274545719 := by
  unfold tailWord_2718964
  simp only [CollatzResearch.WordTrace]
  refine ⟨49584382060832632463277973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66112509414443509951037297 49584382060832632463277973)
  ·
    refine ⟨2324267909101529646716155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49584382060832632463277973 2324267909101529646716155)
    ·
      refine ⟨3486401863652294470074233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2324267909101529646716155 3486401863652294470074233)
      ·
        refine ⟨2614801397739220852555675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3486401863652294470074233 2614801397739220852555675)
        ·
          refine ⟨3922202096608831278833513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2614801397739220852555675 3922202096608831278833513)
          ·
            refine ⟨2941651572456623459125135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3922202096608831278833513 2941651572456623459125135)
            ·
              refine ⟨4412477358684935188687703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941651572456623459125135 4412477358684935188687703)
              ·
                refine ⟨6618716038027402783031555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4412477358684935188687703 6618716038027402783031555)
                ·
                  refine ⟨9928074057041104174547333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6618716038027402783031555 9928074057041104174547333)
                  ·
                    refine ⟨1861513885695207032727625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9928074057041104174547333 1861513885695207032727625)
                    ·
                      refine ⟨1396135414271405274545719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861513885695207032727625 1396135414271405274545719)
                      ·
                        rfl

theorem cell23_2718964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2718964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2718964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2718964 prefixEnd_2718964 := by exact prefixLift 2718964
  have htrace : WordTrace (prefixWord ++ tailWord_2718964) baseStart_2718964 baseEnd_2718964 := by
    simpa [prefixWord, tailWord_2718964, baseEnd_2718964] using wordTrace_append hprefix tailTrace_2718964
  have hstable : (prefixWord ++ tailWord_2718964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718964).length < 2 ^ (prefixWord ++ tailWord_2718964).sum := by decide
  have hdescent : baseEnd_2718964 < baseStart_2718964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719009 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 6]
def baseStart_2719009 : Nat := 118140960795 + 2719009 * 2 ^ 59
def prefixEnd_2719009 : Nat := 4983230072969 + 3 ^ 40 * 2719009 * 2
def baseEnd_2719009 : Nat := 155128724544539733164779

theorem tailTrace_2719009 : CollatzResearch.WordTrace tailWord_2719009 prefixEnd_2719009 155128724544539733164779 := by
  unfold tailWord_2719009
  simp only [CollatzResearch.WordTrace]
  refine ⟨99170405406502237611944081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66113603604334825074629387 99170405406502237611944081)
  ·
    refine ⟨74377804054876678208958061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99170405406502237611944081 74377804054876678208958061)
    ·
      refine ⟨27891676520578754328359273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74377804054876678208958061 27891676520578754328359273)
      ·
        refine ⟨20918757390434065746269455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27891676520578754328359273 20918757390434065746269455)
        ·
          refine ⟨31378136085651098619404183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20918757390434065746269455 31378136085651098619404183)
          ·
            refine ⟨47067204128476647929106275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31378136085651098619404183 47067204128476647929106275)
            ·
              refine ⟨70600806192714971893659413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47067204128476647929106275 70600806192714971893659413)
              ·
                refine ⟨3309412790283514307515285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70600806192714971893659413 3309412790283514307515285)
                ·
                  refine ⟨155128724544539733164779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3309412790283514307515285 155128724544539733164779)
                  ·
                    rfl

theorem cell23_2719009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 6].length) (baseStart_2719009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719009 prefixEnd_2719009 := by exact prefixLift 2719009
  have htrace : WordTrace (prefixWord ++ tailWord_2719009) baseStart_2719009 baseEnd_2719009 := by
    simpa [prefixWord, tailWord_2719009, baseEnd_2719009] using wordTrace_append hprefix tailTrace_2719009
  have hstable : (prefixWord ++ tailWord_2719009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719009).length < 2 ^ (prefixWord ++ tailWord_2719009).sum := by decide
  have hdescent : baseEnd_2719009 < baseStart_2719009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719013 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_2719013 : Nat := 118140960795 + 2719013 * 2 ^ 59
def prefixEnd_2719013 : Nat := 4983230072969 + 3 ^ 40 * 2719013 * 2
def baseEnd_2719013 : Nat := 465386858274491860944331

theorem tailTrace_2719013 : CollatzResearch.WordTrace tailWord_2719013 prefixEnd_2719013 465386858274491860944331 := by
  unfold tailWord_2719013
  simp only [CollatzResearch.WordTrace]
  refine ⟨99170551298487746295089693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66113700865658497530059795 99170551298487746295089693)
  ·
    refine ⟨37188956736932904860658635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99170551298487746295089693 37188956736932904860658635)
    ·
      refine ⟨55783435105399357290987953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37188956736932904860658635 55783435105399357290987953)
      ·
        refine ⟨41837576329049517968240965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55783435105399357290987953 41837576329049517968240965)
        ·
          refine ⟨7844545561696784619045181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41837576329049517968240965 7844545561696784619045181)
          ·
            refine ⟨2941704585636294232141943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7844545561696784619045181 2941704585636294232141943)
            ·
              refine ⟨4412556878454441348212915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941704585636294232141943 4412556878454441348212915)
              ·
                refine ⟨6618835317681662022319373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4412556878454441348212915 6618835317681662022319373)
                ·
                  refine ⟨2482063244130623258369765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6618835317681662022319373 2482063244130623258369765)
                  ·
                    refine ⟨465386858274491860944331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2482063244130623258369765 465386858274491860944331)
                    ·
                      rfl

theorem cell23_2719013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_2719013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719013 prefixEnd_2719013 := by exact prefixLift 2719013
  have htrace : WordTrace (prefixWord ++ tailWord_2719013) baseStart_2719013 baseEnd_2719013 := by
    simpa [prefixWord, tailWord_2719013, baseEnd_2719013] using wordTrace_append hprefix tailTrace_2719013
  have hstable : (prefixWord ++ tailWord_2719013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719013).length < 2 ^ (prefixWord ++ tailWord_2719013).sum := by decide
  have hdescent : baseEnd_2719013 < baseStart_2719013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719026 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 6]
def baseStart_2719026 : Nat := 118140960795 + 2719026 * 2 ^ 59
def prefixEnd_2719026 : Nat := 4983230072969 + 3 ^ 40 * 2719026 * 2
def baseEnd_2719026 : Nat := 155129694452442670218937

theorem tailTrace_2719026 : CollatzResearch.WordTrace tailWord_2719026 prefixEnd_2719026 155129694452442670218937 := by
  unfold tailWord_2719026
  simp only [CollatzResearch.WordTrace]
  refine ⟨24792756361860162378828233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66114016964960433010208621 24792756361860162378828233)
  ·
    refine ⟨18594567271395121784121175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24792756361860162378828233 18594567271395121784121175)
    ·
      refine ⟨27891850907092682676181763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18594567271395121784121175 27891850907092682676181763)
      ·
        refine ⟨41837776360639024014272645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27891850907092682676181763 41837776360639024014272645)
        ·
          refine ⟨7844583067619817002676121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41837776360639024014272645 7844583067619817002676121)
          ·
            refine ⟨5883437300714862752007091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7844583067619817002676121 5883437300714862752007091)
            ·
              refine ⟨8825155951072294128010637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5883437300714862752007091 8825155951072294128010637)
              ·
                refine ⟨3309433481652110298003989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8825155951072294128010637 3309433481652110298003989)
                ·
                  refine ⟨155129694452442670218937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3309433481652110298003989 155129694452442670218937)
                  ·
                    rfl

theorem cell23_2719026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_2719026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719026 prefixEnd_2719026 := by exact prefixLift 2719026
  have htrace : WordTrace (prefixWord ++ tailWord_2719026) baseStart_2719026 baseEnd_2719026 := by
    simpa [prefixWord, tailWord_2719026, baseEnd_2719026] using wordTrace_append hprefix tailTrace_2719026
  have hstable : (prefixWord ++ tailWord_2719026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719026).length < 2 ^ (prefixWord ++ tailWord_2719026).sum := by decide
  have hdescent : baseEnd_2719026 < baseStart_2719026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719063 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 2, 3, 2]
def baseStart_2719063 : Nat := 118140960795 + 2719063 * 2 ^ 59
def prefixEnd_2719063 : Nat := 4983230072969 + 3 ^ 40 * 2719063 * 2
def baseEnd_2719063 : Nat := 1396186248856200387207763

theorem tailTrace_2719063 : CollatzResearch.WordTrace tailWord_2719063 prefixEnd_2719063 1396186248856200387207763 := by
  unfold tailWord_2719063
  simp only [CollatzResearch.WordTrace]
  refine ⟨99172374948306604834409843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66114916632204403222939895 99172374948306604834409843)
  ·
    refine ⟨148758562422459907251614765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99172374948306604834409843 148758562422459907251614765)
    ·
      refine ⟨55784460908422465219355537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148758562422459907251614765 55784460908422465219355537)
      ·
        refine ⟨41838345681316848914516653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55784460908422465219355537 41838345681316848914516653)
        ·
          refine ⟨15689379630493818342943745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41838345681316848914516653 15689379630493818342943745)
          ·
            refine ⟨11767034722870363757207809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15689379630493818342943745 11767034722870363757207809)
            ·
              refine ⟨8825276042152772817905857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11767034722870363757207809 8825276042152772817905857)
              ·
                refine ⟨6618957031614579613429393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8825276042152772817905857 6618957031614579613429393)
                ·
                  refine ⟨4964217773710934710072045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6618957031614579613429393 4964217773710934710072045)
                  ·
                    refine ⟨1861581665141600516277017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4964217773710934710072045 1861581665141600516277017)
                    ·
                      refine ⟨1396186248856200387207763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861581665141600516277017 1396186248856200387207763)
                      ·
                        rfl

theorem cell23_2719063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_2719063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719063 prefixEnd_2719063 := by exact prefixLift 2719063
  have htrace : WordTrace (prefixWord ++ tailWord_2719063) baseStart_2719063 baseEnd_2719063 := by
    simpa [prefixWord, tailWord_2719063, baseEnd_2719063] using wordTrace_append hprefix tailTrace_2719063
  have hstable : (prefixWord ++ tailWord_2719063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719063).length < 2 ^ (prefixWord ++ tailWord_2719063).sum := by decide
  have hdescent : baseEnd_2719063 < baseStart_2719063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719076 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_2719076 : Nat := 118140960795 + 2719076 * 2 ^ 59
def prefixEnd_2719076 : Nat := 4983230072969 + 3 ^ 40 * 2719076 * 2
def baseEnd_2719076 : Nat := 1396192924104708836345203

theorem tailTrace_2719076 : CollatzResearch.WordTrace tailWord_2719076 prefixEnd_2719076 1396192924104708836345203 := by
  unfold tailWord_2719076
  simp only [CollatzResearch.WordTrace]
  refine ⟨49586424548629754027316541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66115232731506338703088721 49586424548629754027316541)
  ·
    refine ⟨18594909205736157760243703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49586424548629754027316541 18594909205736157760243703)
    ·
      refine ⟨27892363808604236640365555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18594909205736157760243703 27892363808604236640365555)
      ·
        refine ⟨41838545712906354960548333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27892363808604236640365555 41838545712906354960548333)
        ·
          refine ⟨15689454642339883110205625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41838545712906354960548333 15689454642339883110205625)
          ·
            refine ⟨11767090981754912332654219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15689454642339883110205625 11767090981754912332654219)
            ·
              refine ⟨17650636472632368498981329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11767090981754912332654219 17650636472632368498981329)
              ·
                refine ⟨13237977354474276374235997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17650636472632368498981329 13237977354474276374235997)
                ·
                  refine ⟨4964241507927853640338499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13237977354474276374235997 4964241507927853640338499)
                  ·
                    refine ⟨7446362261891780460507749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4964241507927853640338499 7446362261891780460507749)
                    ·
                      refine ⟨1396192924104708836345203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7446362261891780460507749 1396192924104708836345203)
                      ·
                        rfl

theorem cell23_2719076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_2719076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719076 prefixEnd_2719076 := by exact prefixLift 2719076
  have htrace : WordTrace (prefixWord ++ tailWord_2719076) baseStart_2719076 baseEnd_2719076 := by
    simpa [prefixWord, tailWord_2719076, baseEnd_2719076] using wordTrace_append hprefix tailTrace_2719076
  have hstable : (prefixWord ++ tailWord_2719076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719076).length < 2 ^ (prefixWord ++ tailWord_2719076).sum := by decide
  have hdescent : baseEnd_2719076 < baseStart_2719076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719089 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_2719089 : Nat := 118140960795 + 2719089 * 2 ^ 59
def prefixEnd_2719089 : Nat := 4983230072969 + 3 ^ 40 * 2719089 * 2
def baseEnd_2719089 : Nat := 1396199599353217285482643

theorem tailTrace_2719089 : CollatzResearch.WordTrace tailWord_2719089 prefixEnd_2719089 1396199599353217285482643 := by
  unfold tailWord_2719089
  simp only [CollatzResearch.WordTrace]
  refine ⟨99173323246212411274856321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66115548830808274183237547 99173323246212411274856321)
  ·
    refine ⟨74379992434659308456142241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99173323246212411274856321 74379992434659308456142241)
    ·
      refine ⟨55784994325994481342106681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74379992434659308456142241 55784994325994481342106681)
      ·
        refine ⟨41838745744495861006580011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55784994325994481342106681 41838745744495861006580011)
        ·
          refine ⟨62758118616743791509870017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41838745744495861006580011 62758118616743791509870017)
          ·
            refine ⟨47068588962557843632402513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62758118616743791509870017 47068588962557843632402513)
            ·
              refine ⟨35301441721918382724301885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47068588962557843632402513 35301441721918382724301885)
              ·
                refine ⟨13238040645719393521613207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35301441721918382724301885 13238040645719393521613207)
                ·
                  refine ⟨19857060968579090282419811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13238040645719393521613207 19857060968579090282419811)
                  ·
                    refine ⟨29785591452868635423629717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19857060968579090282419811 29785591452868635423629717)
                    ·
                      refine ⟨1396199599353217285482643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29785591452868635423629717 1396199599353217285482643)
                      ·
                        rfl

theorem cell23_2719089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_2719089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719089 prefixEnd_2719089 := by exact prefixLift 2719089
  have htrace : WordTrace (prefixWord ++ tailWord_2719089) baseStart_2719089 baseEnd_2719089 := by
    simpa [prefixWord, tailWord_2719089, baseEnd_2719089] using wordTrace_append hprefix tailTrace_2719089
  have hstable : (prefixWord ++ tailWord_2719089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719089).length < 2 ^ (prefixWord ++ tailWord_2719089).sum := by decide
  have hdescent : baseEnd_2719089 < baseStart_2719089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719161 : List Nat := [1, 2, 1, 4, 5, 1, 1, 3, 1, 2, 2]
def baseStart_2719161 : Nat := 118140960795 + 2719161 * 2 ^ 59
def prefixEnd_2719161 : Nat := 4983230072969 + 3 ^ 40 * 2719161 * 2
def baseEnd_2719161 : Nat := 1396236569960341003782313

theorem tailTrace_2719161 : CollatzResearch.WordTrace tailWord_2719161 prefixEnd_2719161 1396236569960341003782313 := by
  unfold tailWord_2719161
  simp only [CollatzResearch.WordTrace]
  refine ⟨99175949301951567571477337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66117299534634378380984891 99175949301951567571477337)
  ·
    refine ⟨74381961976463675678608003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99175949301951567571477337 74381961976463675678608003)
    ·
      refine ⟨111572942964695513517912005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74381961976463675678608003 111572942964695513517912005)
      ·
        refine ⟨20919926805880408784608501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111572942964695513517912005 20919926805880408784608501)
        ·
          refine ⟨1961243138051288323557047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20919926805880408784608501 1961243138051288323557047)
          ·
            refine ⟨2941864707076932485335571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961243138051288323557047 2941864707076932485335571)
            ·
              refine ⟨4412797060615398728003357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941864707076932485335571 4412797060615398728003357)
              ·
                refine ⟨1654798897730774523001259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4412797060615398728003357 1654798897730774523001259)
                ·
                  refine ⟨2482198346596161784501889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1654798897730774523001259 2482198346596161784501889)
                  ·
                    refine ⟨1861648759947121338376417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2482198346596161784501889 1861648759947121338376417)
                    ·
                      refine ⟨1396236569960341003782313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861648759947121338376417 1396236569960341003782313)
                      ·
                        rfl

theorem cell23_2719161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_2719161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719161 prefixEnd_2719161 := by exact prefixLift 2719161
  have htrace : WordTrace (prefixWord ++ tailWord_2719161) baseStart_2719161 baseEnd_2719161 := by
    simpa [prefixWord, tailWord_2719161, baseEnd_2719161] using wordTrace_append hprefix tailTrace_2719161
  have hstable : (prefixWord ++ tailWord_2719161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719161).length < 2 ^ (prefixWord ++ tailWord_2719161).sum := by decide
  have hdescent : baseEnd_2719161 < baseStart_2719161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719166 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2719166 : Nat := 118140960795 + 2719166 * 2 ^ 59
def prefixEnd_2719166 : Nat := 4983230072969 + 3 ^ 40 * 2719166 * 2
def baseEnd_2719166 : Nat := 1396239137363613484219789

theorem tailTrace_2719166 : CollatzResearch.WordTrace tailWord_2719166 prefixEnd_2719166 1396239137363613484219789 := by
  unfold tailWord_2719166
  simp only [CollatzResearch.WordTrace]
  refine ⟨12397016458366681678176169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66117421111288968950272901 12397016458366681678176169)
  ·
    refine ⟨9297762343775011258632127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12397016458366681678176169 9297762343775011258632127)
    ·
      refine ⟨13946643515662516887948191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9297762343775011258632127 13946643515662516887948191)
      ·
        refine ⟨20919965273493775331922287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13946643515662516887948191 20919965273493775331922287)
        ·
          refine ⟨31379947910240662997883431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20919965273493775331922287 31379947910240662997883431)
          ·
            refine ⟨47069921865360994496825147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31379947910240662997883431 47069921865360994496825147)
            ·
              refine ⟨70604882798041491745237721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47069921865360994496825147 70604882798041491745237721)
              ·
                refine ⟨52953662098531118808928291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70604882798041491745237721 52953662098531118808928291)
                ·
                  refine ⟨79430493147796678213392437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52953662098531118808928291 79430493147796678213392437)
                  ·
                    refine ⟨7446608732605938582505541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79430493147796678213392437 7446608732605938582505541)
                    ·
                      refine ⟨1396239137363613484219789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7446608732605938582505541 1396239137363613484219789)
                      ·
                        rfl

theorem cell23_2719166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2719166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719166 prefixEnd_2719166 := by exact prefixLift 2719166
  have htrace : WordTrace (prefixWord ++ tailWord_2719166) baseStart_2719166 baseEnd_2719166 := by
    simpa [prefixWord, tailWord_2719166, baseEnd_2719166] using wordTrace_append hprefix tailTrace_2719166
  have hstable : (prefixWord ++ tailWord_2719166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719166).length < 2 ^ (prefixWord ++ tailWord_2719166).sum := by decide
  have hdescent : baseEnd_2719166 < baseStart_2719166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719234 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_2719234 : Nat := 118140960795 + 2719234 * 2 ^ 59
def prefixEnd_2719234 : Nat := 4983230072969 + 3 ^ 40 * 2719234 * 2
def baseEnd_2719234 : Nat := 1396274054048119218169477

theorem tailTrace_2719234 : CollatzResearch.WordTrace tailWord_2719234 prefixEnd_2719234 1396274054048119218169477 := by
  unfold tailWord_2719234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24794652957671775259721189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66119074553791400692589837 24794652957671775259721189)
  ·
    refine ⟨4648997429563457861197723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24794652957671775259721189 4648997429563457861197723)
    ·
      refine ⟨6973496144345186791796585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4648997429563457861197723 6973496144345186791796585)
      ·
        refine ⟨5230122108258890093847439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6973496144345186791796585 5230122108258890093847439)
        ·
          refine ⟨7845183162388335140771159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5230122108258890093847439 7845183162388335140771159)
          ·
            refine ⟨11767774743582502711156739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7845183162388335140771159 11767774743582502711156739)
            ·
              refine ⟨17651662115373754066735109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11767774743582502711156739 17651662115373754066735109)
              ·
                refine ⟨3309686646632578887512833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17651662115373754066735109 3309686646632578887512833)
                ·
                  refine ⟨2482264984974434165634625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3309686646632578887512833 2482264984974434165634625)
                  ·
                    refine ⟨1861698738730825624225969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2482264984974434165634625 1861698738730825624225969)
                    ·
                      refine ⟨1396274054048119218169477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861698738730825624225969 1396274054048119218169477)
                      ·
                        rfl

theorem cell23_2719234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_2719234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719234 prefixEnd_2719234 := by exact prefixLift 2719234
  have htrace : WordTrace (prefixWord ++ tailWord_2719234) baseStart_2719234 baseEnd_2719234 := by
    simpa [prefixWord, tailWord_2719234, baseEnd_2719234] using wordTrace_append hprefix tailTrace_2719234
  have hstable : (prefixWord ++ tailWord_2719234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719234).length < 2 ^ (prefixWord ++ tailWord_2719234).sum := by decide
  have hdescent : baseEnd_2719234 < baseStart_2719234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719240 : List Nat := [2, 1, 3, 2, 1, 1, 6, 2, 5]
def baseStart_2719240 : Nat := 118140960795 + 2719240 * 2 ^ 59
def prefixEnd_2719240 : Nat := 4983230072969 + 3 ^ 40 * 2719240 * 2
def baseEnd_2719240 : Nat := 155141903881338466077161

theorem tailTrace_2719240 : CollatzResearch.WordTrace tailWord_2719240 prefixEnd_2719240 155141903881338466077161 := by
  unfold tailWord_2719240
  simp only [CollatzResearch.WordTrace]
  refine ⟨49589415334332682031801587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66119220445776909375735449 49589415334332682031801587)
  ·
    refine ⟨74384123001499023047702381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49589415334332682031801587 74384123001499023047702381)
    ·
      refine ⟨27894046125562133642888393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74384123001499023047702381 27894046125562133642888393)
      ·
        refine ⟨20920534594171600232166295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27894046125562133642888393 20920534594171600232166295)
        ·
          refine ⟨31380801891257400348249443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20920534594171600232166295 31380801891257400348249443)
          ·
            refine ⟨47071202836886100522374165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31380801891257400348249443 47071202836886100522374165)
            ·
              refine ⟨2206462632979035961986289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47071202836886100522374165 2206462632979035961986289)
              ·
                refine ⟨1654846974734276971489717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2206462632979035961986289 1654846974734276971489717)
                ·
                  refine ⟨155141903881338466077161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1654846974734276971489717 155141903881338466077161)
                  ·
                    rfl

theorem cell23_2719240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 5].length) (baseStart_2719240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719240 prefixEnd_2719240 := by exact prefixLift 2719240
  have htrace : WordTrace (prefixWord ++ tailWord_2719240) baseStart_2719240 baseEnd_2719240 := by
    simpa [prefixWord, tailWord_2719240, baseEnd_2719240] using wordTrace_append hprefix tailTrace_2719240
  have hstable : (prefixWord ++ tailWord_2719240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719240).length < 2 ^ (prefixWord ++ tailWord_2719240).sum := by decide
  have hdescent : baseEnd_2719240 < baseStart_2719240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719357 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_2719357 : Nat := 118140960795 + 2719357 * 2 ^ 59
def prefixEnd_2719357 : Nat := 4983230072969 + 3 ^ 40 * 2719357 * 2
def baseEnd_2719357 : Nat := 1396337212168622236931411

theorem tailTrace_2719357 : CollatzResearch.WordTrace tailWord_2719357 prefixEnd_2719357 1396337212168622236931411 := by
  unfold tailWord_2719357
  simp only [CollatzResearch.WordTrace]
  refine ⟨99183098009241493045612325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66122065339494328697074883 99183098009241493045612325)
  ·
    refine ⟨18596830876732779946052311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99183098009241493045612325 18596830876732779946052311)
    ·
      refine ⟨27895246315099169919078467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18596830876732779946052311 27895246315099169919078467)
      ·
        refine ⟨41842869472648754878617701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27895246315099169919078467 41842869472648754878617701)
        ·
          refine ⟨7845538026121641539740819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41842869472648754878617701 7845538026121641539740819)
          ·
            refine ⟨11768307039182462309611229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7845538026121641539740819 11768307039182462309611229)
            ·
              refine ⟨4413115139693423366104211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11768307039182462309611229 4413115139693423366104211)
              ·
                refine ⟨6619672709540135049156317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413115139693423366104211 6619672709540135049156317)
                ·
                  refine ⟨2482377266077550643433619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6619672709540135049156317 2482377266077550643433619)
                  ·
                    refine ⟨3723565899116325965150429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2482377266077550643433619 3723565899116325965150429)
                    ·
                      refine ⟨1396337212168622236931411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3723565899116325965150429 1396337212168622236931411)
                      ·
                        rfl

theorem cell23_2719357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_2719357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719357 prefixEnd_2719357 := by exact prefixLift 2719357
  have htrace : WordTrace (prefixWord ++ tailWord_2719357) baseStart_2719357 baseEnd_2719357 := by
    simpa [prefixWord, tailWord_2719357, baseEnd_2719357] using wordTrace_append hprefix tailTrace_2719357
  have hstable : (prefixWord ++ tailWord_2719357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719357).length < 2 ^ (prefixWord ++ tailWord_2719357).sum := by decide
  have hdescent : baseEnd_2719357 < baseStart_2719357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719363 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 4]
def baseStart_2719363 : Nat := 118140960795 + 2719363 * 2 ^ 59
def prefixEnd_2719363 : Nat := 4983230072969 + 3 ^ 40 * 2719363 * 2
def baseEnd_2719363 : Nat := 1396340293052549213456383

theorem tailTrace_2719363 : CollatzResearch.WordTrace tailWord_2719363 prefixEnd_2719363 1396340293052549213456383 := by
  unfold tailWord_2719363
  simp only [CollatzResearch.WordTrace]
  refine ⟨99183316847219756070330743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66122211231479837380220495 99183316847219756070330743)
  ·
    refine ⟨148774975270829634105496115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99183316847219756070330743 148774975270829634105496115)
    ·
      refine ⟨223162462906244451158244173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148774975270829634105496115 223162462906244451158244173)
      ·
        refine ⟨83685923589841669184341565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223162462906244451158244173 83685923589841669184341565)
        ·
          refine ⟨31382221346190625944128087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83685923589841669184341565 31382221346190625944128087)
          ·
            refine ⟨47073332019285938916192131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31382221346190625944128087 47073332019285938916192131)
            ·
              refine ⟨70609998028928908374288197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47073332019285938916192131 70609998028928908374288197)
              ·
                refine ⟨13239374630424170320179037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70609998028928908374288197 13239374630424170320179037)
                ·
                  refine ⟨4964765486409063870067139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13239374630424170320179037 4964765486409063870067139)
                  ·
                    refine ⟨7447148229613595805100709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4964765486409063870067139 7447148229613595805100709)
                    ·
                      refine ⟨1396340293052549213456383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7447148229613595805100709 1396340293052549213456383)
                      ·
                        rfl

theorem cell23_2719363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_2719363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719363 prefixEnd_2719363 := by exact prefixLift 2719363
  have htrace : WordTrace (prefixWord ++ tailWord_2719363) baseStart_2719363 baseEnd_2719363 := by
    simpa [prefixWord, tailWord_2719363, baseEnd_2719363] using wordTrace_append hprefix tailTrace_2719363
  have hstable : (prefixWord ++ tailWord_2719363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719363).length < 2 ^ (prefixWord ++ tailWord_2719363).sum := by decide
  have hdescent : baseEnd_2719363 < baseStart_2719363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719364 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 6]
def baseStart_2719364 : Nat := 118140960795 + 2719364 * 2 ^ 59
def prefixEnd_2719364 : Nat := 4983230072969 + 3 ^ 40 * 2719364 * 2
def baseEnd_2719364 : Nat := 155148978503689301060431

theorem tailTrace_2719364 : CollatzResearch.WordTrace tailWord_2719364 prefixEnd_2719364 155148978503689301060431 := by
  unfold tailWord_2719364
  simp only [CollatzResearch.WordTrace]
  refine ⟨49591676660108066620558573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66122235546810755494078097 49591676660108066620558573)
  ·
    refine ⟨18596878747540524982709465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49591676660108066620558573 18596878747540524982709465)
    ·
      refine ⟨13947659060655393737032099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18596878747540524982709465 13947659060655393737032099)
      ·
        refine ⟨20921488590983090605548149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13947659060655393737032099 20921488590983090605548149)
        ·
          refine ⟨1961389555404664744270139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20921488590983090605548149 1961389555404664744270139)
          ·
            refine ⟨2942084333106997116405209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961389555404664744270139 2942084333106997116405209)
            ·
              refine ⟨2206563249830247837303907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2942084333106997116405209 2206563249830247837303907)
              ·
                refine ⟨3309844874745371755955861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206563249830247837303907 3309844874745371755955861)
                ·
                  refine ⟨155148978503689301060431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3309844874745371755955861 155148978503689301060431)
                  ·
                    rfl

theorem cell23_2719364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_2719364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719364 prefixEnd_2719364 := by exact prefixLift 2719364
  have htrace : WordTrace (prefixWord ++ tailWord_2719364) baseStart_2719364 baseEnd_2719364 := by
    simpa [prefixWord, tailWord_2719364, baseEnd_2719364] using wordTrace_append hprefix tailTrace_2719364
  have hstable : (prefixWord ++ tailWord_2719364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719364).length < 2 ^ (prefixWord ++ tailWord_2719364).sum := by decide
  have hdescent : baseEnd_2719364 < baseStart_2719364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719390 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2719390 : Nat := 118140960795 + 2719390 * 2 ^ 59
def prefixEnd_2719390 : Nat := 4983230072969 + 3 ^ 40 * 2719390 * 2
def baseEnd_2719390 : Nat := 465451385676740202606253

theorem tailTrace_2719390 : CollatzResearch.WordTrace tailWord_2719390 prefixEnd_2719390 465451385676740202606253 := by
  unfold tailWord_2719390
  simp only [CollatzResearch.WordTrace]
  refine ⟨12398037702265242460195453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66122867745414626454375749 12398037702265242460195453)
  ·
    refine ⟨4649264138349465922573295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12398037702265242460195453 4649264138349465922573295)
    ·
      refine ⟨6973896207524198883859943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4649264138349465922573295 6973896207524198883859943)
      ·
        refine ⟨10460844311286298325789915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6973896207524198883859943 10460844311286298325789915)
        ·
          refine ⟨15691266466929447488684873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10460844311286298325789915 15691266466929447488684873)
          ·
            refine ⟨11768449850197085616513655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15691266466929447488684873 11768449850197085616513655)
            ·
              refine ⟨17652674775295628424770483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11768449850197085616513655 17652674775295628424770483)
              ·
                refine ⟨26479012162943442637155725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17652674775295628424770483 26479012162943442637155725)
                ·
                  refine ⟨9929629561103790988933397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26479012162943442637155725 9929629561103790988933397)
                  ·
                    refine ⟨465451385676740202606253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9929629561103790988933397 465451385676740202606253)
                    ·
                      rfl

theorem cell23_2719390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2719390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719390 prefixEnd_2719390 := by exact prefixLift 2719390
  have htrace : WordTrace (prefixWord ++ tailWord_2719390) baseStart_2719390 baseEnd_2719390 := by
    simpa [prefixWord, tailWord_2719390, baseEnd_2719390] using wordTrace_append hprefix tailTrace_2719390
  have hstable : (prefixWord ++ tailWord_2719390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719390).length < 2 ^ (prefixWord ++ tailWord_2719390).sum := by decide
  have hdescent : baseEnd_2719390 < baseStart_2719390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719420 : List Nat := [2, 2, 2, 3, 1, 4, 1, 8]
def baseStart_2719420 : Nat := 118140960795 + 2719420 * 2 ^ 59
def prefixEnd_2719420 : Nat := 4983230072969 + 3 ^ 40 * 2719420 * 2
def baseEnd_2719420 : Nat := 51717391164809462609023

theorem tailTrace_2719420 : CollatzResearch.WordTrace tailWord_2719420 prefixEnd_2719420 51717391164809462609023 := by
  unfold tailWord_2719420
  simp only [CollatzResearch.WordTrace]
  refine ⟨49592697904006627402577857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66123597205342169870103809 49592697904006627402577857)
  ·
    refine ⟨37194523428004970551933393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49592697904006627402577857 37194523428004970551933393)
    ·
      refine ⟨27895892571003727913950045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37194523428004970551933393 27895892571003727913950045)
      ·
        refine ⟨10460959714126397967731267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27895892571003727913950045 10460959714126397967731267)
        ·
          refine ⟨15691439571189596951596901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10460959714126397967731267 15691439571189596951596901)
          ·
            refine ⟨2942144919598049428424419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15691439571189596951596901 2942144919598049428424419)
            ·
              refine ⟨4413217379397074142636629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2942144919598049428424419 4413217379397074142636629)
              ·
                refine ⟨51717391164809462609023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4413217379397074142636629 51717391164809462609023)
                ·
                  rfl

theorem cell23_2719420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 8].length) (baseStart_2719420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719420 prefixEnd_2719420 := by exact prefixLift 2719420
  have htrace : WordTrace (prefixWord ++ tailWord_2719420) baseStart_2719420 baseEnd_2719420 := by
    simpa [prefixWord, tailWord_2719420, baseEnd_2719420] using wordTrace_append hprefix tailTrace_2719420
  have hstable : (prefixWord ++ tailWord_2719420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719420).length < 2 ^ (prefixWord ++ tailWord_2719420).sum := by decide
  have hdescent : baseEnd_2719420 < baseStart_2719420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719464 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_2719464 : Nat := 118140960795 + 2719464 * 2 ^ 59
def prefixEnd_2719464 : Nat := 4983230072969 + 3 ^ 40 * 2719464 * 2
def baseEnd_2719464 : Nat := 1396392154598653318293419

theorem tailTrace_2719464 : CollatzResearch.WordTrace tailWord_2719464 prefixEnd_2719464 1396392154598653318293419 := by
  unfold tailWord_2719464
  simp only [CollatzResearch.WordTrace]
  refine ⟨49593500309926925159878723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66124667079902566879838297 49593500309926925159878723)
  ·
    refine ⟨74390250464890387739818085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49593500309926925159878723 74390250464890387739818085)
    ·
      refine ⟨13948171962166947701215891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74390250464890387739818085 13948171962166947701215891)
      ·
        refine ⟨20922257943250421551823837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13948171962166947701215891 20922257943250421551823837)
        ·
          refine ⟨7845846728718908081933939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20922257943250421551823837 7845846728718908081933939)
          ·
            refine ⟨11768770093078362122900909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7845846728718908081933939 11768770093078362122900909)
            ·
              refine ⟨4413288784904385796087841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11768770093078362122900909 4413288784904385796087841)
              ·
                refine ⟨3309966588678289347065881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4413288784904385796087841 3309966588678289347065881)
                ·
                  refine ⟨2482474941508717010299411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3309966588678289347065881 2482474941508717010299411)
                  ·
                    refine ⟨3723712412263075515449117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2482474941508717010299411 3723712412263075515449117)
                    ·
                      refine ⟨1396392154598653318293419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3723712412263075515449117 1396392154598653318293419)
                      ·
                        rfl

theorem cell23_2719464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_2719464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719464 prefixEnd_2719464 := by exact prefixLift 2719464
  have htrace : WordTrace (prefixWord ++ tailWord_2719464) baseStart_2719464 baseEnd_2719464 := by
    simpa [prefixWord, tailWord_2719464, baseEnd_2719464] using wordTrace_append hprefix tailTrace_2719464
  have hstable : (prefixWord ++ tailWord_2719464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719464).length < 2 ^ (prefixWord ++ tailWord_2719464).sum := by decide
  have hdescent : baseEnd_2719464 < baseStart_2719464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719483 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 4]
def baseStart_2719483 : Nat := 118140960795 + 2719483 * 2 ^ 59
def prefixEnd_2719483 : Nat := 4983230072969 + 3 ^ 40 * 2719483 * 2
def baseEnd_2719483 : Nat := 1396401910731088743955831

theorem tailTrace_2719483 : CollatzResearch.WordTrace tailWord_2719483 prefixEnd_2719483 1396401910731088743955831 := by
  unfold tailWord_2719483
  simp only [CollatzResearch.WordTrace]
  refine ⟨99187693606785016564699103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66125129071190011043132735 99187693606785016564699103)
  ·
    refine ⟨148781540410177524847048655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99187693606785016564699103 148781540410177524847048655)
    ·
      refine ⟨223172310615266287270572983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148781540410177524847048655 223172310615266287270572983)
      ·
        refine ⟨334758465922899430905859475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223172310615266287270572983 334758465922899430905859475)
        ·
          refine ⟨502137698884349146358789213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334758465922899430905859475 502137698884349146358789213)
          ·
            refine ⟨188301637081630929884545955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 502137698884349146358789213 188301637081630929884545955)
            ·
              refine ⟨282452455622446394826818933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188301637081630929884545955 282452455622446394826818933)
              ·
                refine ⟨26479917714604349515014275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282452455622446394826818933 26479917714604349515014275)
                ·
                  refine ⟨39719876571906524272521413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26479917714604349515014275 39719876571906524272521413)
                  ·
                    refine ⟨7447476857232473301097765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39719876571906524272521413 7447476857232473301097765)
                    ·
                      refine ⟨1396401910731088743955831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7447476857232473301097765 1396401910731088743955831)
                      ·
                        rfl

theorem cell23_2719483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 4].length) (baseStart_2719483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719483 prefixEnd_2719483 := by exact prefixLift 2719483
  have htrace : WordTrace (prefixWord ++ tailWord_2719483) baseStart_2719483 baseEnd_2719483 := by
    simpa [prefixWord, tailWord_2719483, baseEnd_2719483] using wordTrace_append hprefix tailTrace_2719483
  have hstable : (prefixWord ++ tailWord_2719483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719483).length < 2 ^ (prefixWord ++ tailWord_2719483).sum := by decide
  have hdescent : baseEnd_2719483 < baseStart_2719483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719487 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 1, 4, 2]
def baseStart_2719487 : Nat := 118140960795 + 2719487 * 2 ^ 59
def prefixEnd_2719487 : Nat := 4983230072969 + 3 ^ 40 * 2719487 * 2
def baseEnd_2719487 : Nat := 1396403964653706728305813

theorem tailTrace_2719487 : CollatzResearch.WordTrace tailWord_2719487 prefixEnd_2719487 1396403964653706728305813 := by
  unfold tailWord_2719487
  simp only [CollatzResearch.WordTrace]
  refine ⟨99187839498770525247844715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66125226332513683498563143 99187839498770525247844715)
  ·
    refine ⟨148781759248155787871767073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99187839498770525247844715 148781759248155787871767073)
    ·
      refine ⟨111586319436116840903825305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148781759248155787871767073 111586319436116840903825305)
      ·
        refine ⟨83689739577087630677868979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111586319436116840903825305 83689739577087630677868979)
        ·
          refine ⟨125534609365631446016803469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83689739577087630677868979 125534609365631446016803469)
          ·
            refine ⟨47075478512111792256301301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125534609365631446016803469 47075478512111792256301301)
            ·
              refine ⟨4413326110510480524028247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47075478512111792256301301 4413326110510480524028247)
              ·
                refine ⟨6619989165765720786042371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413326110510480524028247 6619989165765720786042371)
                ·
                  refine ⟨9929983748648581179063557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6619989165765720786042371 9929983748648581179063557)
                  ·
                    refine ⟨1861871952871608971074417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9929983748648581179063557 1861871952871608971074417)
                    ·
                      refine ⟨1396403964653706728305813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861871952871608971074417 1396403964653706728305813)
                      ·
                        rfl

theorem cell23_2719487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_2719487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719487 prefixEnd_2719487 := by exact prefixLift 2719487
  have htrace : WordTrace (prefixWord ++ tailWord_2719487) baseStart_2719487 baseEnd_2719487 := by
    simpa [prefixWord, tailWord_2719487, baseEnd_2719487] using wordTrace_append hprefix tailTrace_2719487
  have hstable : (prefixWord ++ tailWord_2719487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719487).length < 2 ^ (prefixWord ++ tailWord_2719487).sum := by decide
  have hdescent : baseEnd_2719487 < baseStart_2719487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719538 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2]
def baseStart_2719538 : Nat := 118140960795 + 2719538 * 2 ^ 59
def prefixEnd_2719538 : Nat := 4983230072969 + 3 ^ 40 * 2719538 * 2
def baseEnd_2719538 : Nat := 1396430152167086028768079

theorem tailTrace_2719538 : CollatzResearch.WordTrace tailWord_2719538 prefixEnd_2719538 1396430152167086028768079 := by
  unfold tailWord_2719538
  simp only [CollatzResearch.WordTrace]
  refine ⟨24797424905396440239487817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66126466414390507305300845 24797424905396440239487817)
  ·
    refine ⟨18598068679047330179615863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24797424905396440239487817 18598068679047330179615863)
    ·
      refine ⟨27897103018570995269423795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18598068679047330179615863 27897103018570995269423795)
      ·
        refine ⟨41845654527856492904135693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27897103018570995269423795 41845654527856492904135693)
        ·
          refine ⟨15692120447946184839050885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41845654527856492904135693 15692120447946184839050885)
          ·
            refine ⟨2942272583989909657322041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15692120447946184839050885 2942272583989909657322041)
            ·
              refine ⟨2206704437992432242991531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2942272583989909657322041 2206704437992432242991531)
              ·
                refine ⟨3310056656988648364487297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206704437992432242991531 3310056656988648364487297)
                ·
                  refine ⟨2482542492741486273365473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310056656988648364487297 2482542492741486273365473)
                  ·
                    refine ⟨1861906869556114705024105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2482542492741486273365473 1861906869556114705024105)
                    ·
                      refine ⟨1396430152167086028768079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861906869556114705024105 1396430152167086028768079)
                      ·
                        rfl

theorem cell23_2719538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_2719538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719538 prefixEnd_2719538 := by exact prefixLift 2719538
  have htrace : WordTrace (prefixWord ++ tailWord_2719538) baseStart_2719538 baseEnd_2719538 := by
    simpa [prefixWord, tailWord_2719538, baseEnd_2719538] using wordTrace_append hprefix tailTrace_2719538
  have hstable : (prefixWord ++ tailWord_2719538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719538).length < 2 ^ (prefixWord ++ tailWord_2719538).sum := by decide
  have hdescent : baseEnd_2719538 < baseStart_2719538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719563 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 11]
def baseStart_2719563 : Nat := 118140960795 + 2719563 * 2 ^ 59
def prefixEnd_2719563 : Nat := 4983230072969 + 3 ^ 40 * 2719563 * 2
def baseEnd_2719563 : Nat := 1396442989183448430955463

theorem tailTrace_2719563 : CollatzResearch.WordTrace tailWord_2719563 prefixEnd_2719563 1396442989183448430955463 := by
  unfold tailWord_2719563
  simp only [CollatzResearch.WordTrace]
  refine ⟨99190611446495190227611343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66127074297663460151740895 99190611446495190227611343)
  ·
    refine ⟨148785917169742785341417015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99190611446495190227611343 148785917169742785341417015)
    ·
      refine ⟨223178875754614178012125523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148785917169742785341417015 223178875754614178012125523)
      ·
        refine ⟨334768313631921267018188285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223178875754614178012125523 334768313631921267018188285)
        ·
          refine ⟨125538117611970475131820607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334768313631921267018188285 125538117611970475131820607)
          ·
            refine ⟨188307176417955712697730911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125538117611970475131820607 188307176417955712697730911)
            ·
              refine ⟨282460764626933569046596367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188307176417955712697730911 282460764626933569046596367)
              ·
                refine ⟨423691146940400353569894551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282460764626933569046596367 423691146940400353569894551)
                ·
                  refine ⟨635536720410600530354841827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423691146940400353569894551 635536720410600530354841827)
                  ·
                    refine ⟨953305080615900795532262741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 635536720410600530354841827 953305080615900795532262741)
                    ·
                      refine ⟨1396442989183448430955463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 953305080615900795532262741 1396442989183448430955463)
                      ·
                        rfl

theorem cell23_2719563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_2719563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719563 prefixEnd_2719563 := by exact prefixLift 2719563
  have htrace : WordTrace (prefixWord ++ tailWord_2719563) baseStart_2719563 baseEnd_2719563 := by
    simpa [prefixWord, tailWord_2719563, baseEnd_2719563] using wordTrace_append hprefix tailTrace_2719563
  have hstable : (prefixWord ++ tailWord_2719563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719563).length < 2 ^ (prefixWord ++ tailWord_2719563).sum := by decide
  have hdescent : baseEnd_2719563 < baseStart_2719563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719577 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 2, 4, 2]
def baseStart_2719577 : Nat := 118140960795 + 2719577 * 2 ^ 59
def prefixEnd_2719577 : Nat := 4983230072969 + 3 ^ 40 * 2719577 * 2
def baseEnd_2719577 : Nat := 1396450177912611376180399

theorem tailTrace_2719577 : CollatzResearch.WordTrace tailWord_2719577 prefixEnd_2719577 1396450177912611376180399 := by
  unfold tailWord_2719577
  simp only [CollatzResearch.WordTrace]
  refine ⟨99191122068444470618620985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66127414712296313745747323 99191122068444470618620985)
  ·
    refine ⟨74393341551333352963965739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99191122068444470618620985 74393341551333352963965739)
    ·
      refine ⟨111590012327000029445948609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74393341551333352963965739 111590012327000029445948609)
      ·
        refine ⟨83692509245250022084461457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111590012327000029445948609 83692509245250022084461457)
        ·
          refine ⟨62769381933937516563346093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83692509245250022084461457 62769381933937516563346093)
          ·
            refine ⟨23538518225226568711254785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62769381933937516563346093 23538518225226568711254785)
            ·
              refine ⟨17653888668919926533441089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23538518225226568711254785 17653888668919926533441089)
              ·
                refine ⟨13240416501689944900080817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17653888668919926533441089 13240416501689944900080817)
                ·
                  refine ⟨9930312376267458675060613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13240416501689944900080817 9930312376267458675060613)
                  ·
                    refine ⟨1861933570550148501573865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9930312376267458675060613 1861933570550148501573865)
                    ·
                      refine ⟨1396450177912611376180399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861933570550148501573865 1396450177912611376180399)
                      ·
                        rfl

theorem cell23_2719577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_2719577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719577 prefixEnd_2719577 := by exact prefixLift 2719577
  have htrace : WordTrace (prefixWord ++ tailWord_2719577) baseStart_2719577 baseEnd_2719577 := by
    simpa [prefixWord, tailWord_2719577, baseEnd_2719577] using wordTrace_append hprefix tailTrace_2719577
  have hstable : (prefixWord ++ tailWord_2719577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719577).length < 2 ^ (prefixWord ++ tailWord_2719577).sum := by decide
  have hdescent : baseEnd_2719577 < baseStart_2719577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719597 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_2719597 : Nat := 118140960795 + 2719597 * 2 ^ 59
def prefixEnd_2719597 : Nat := 4983230072969 + 3 ^ 40 * 2719597 * 2
def baseEnd_2719597 : Nat := 1396460447525701297930307

theorem tailTrace_2719597 : CollatzResearch.WordTrace tailWord_2719597 prefixEnd_2719597 1396460447525701297930307 := by
  unfold tailWord_2719597
  simp only [CollatzResearch.WordTrace]
  refine ⟨99191851528372014034349045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66127901018914676022899363 99191851528372014034349045)
  ·
    refine ⟨9299236080784876315720223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99191851528372014034349045 9299236080784876315720223)
    ·
      refine ⟨13948854121177314473580335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9299236080784876315720223 13948854121177314473580335)
      ·
        refine ⟨20923281181765971710370503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13948854121177314473580335 20923281181765971710370503)
        ·
          refine ⟨31384921772648957565555755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20923281181765971710370503 31384921772648957565555755)
          ·
            refine ⟨47077382658973436348333633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31384921772648957565555755 47077382658973436348333633)
            ·
              refine ⟨35308036994230077261250225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47077382658973436348333633 35308036994230077261250225)
              ·
                refine ⟨26481027745672557945937669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35308036994230077261250225 26481027745672557945937669)
                ·
                  refine ⟨4965192702313604614863313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26481027745672557945937669 4965192702313604614863313)
                  ·
                    refine ⟨3723894526735203461147485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4965192702313604614863313 3723894526735203461147485)
                    ·
                      refine ⟨1396460447525701297930307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3723894526735203461147485 1396460447525701297930307)
                      ·
                        rfl

theorem cell23_2719597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_2719597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719597 prefixEnd_2719597 := by exact prefixLift 2719597
  have htrace : WordTrace (prefixWord ++ tailWord_2719597) baseStart_2719597 baseEnd_2719597 := by
    simpa [prefixWord, tailWord_2719597, baseEnd_2719597] using wordTrace_append hprefix tailTrace_2719597
  have hstable : (prefixWord ++ tailWord_2719597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719597).length < 2 ^ (prefixWord ++ tailWord_2719597).sum := by decide
  have hdescent : baseEnd_2719597 < baseStart_2719597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719627 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 7, 1, 3]
def baseStart_2719627 : Nat := 118140960795 + 2719627 * 2 ^ 59
def prefixEnd_2719627 : Nat := 4983230072969 + 3 ^ 40 * 2719627 * 2
def baseEnd_2719627 : Nat := 1396475851945336180555169

theorem tailTrace_2719627 : CollatzResearch.WordTrace tailWord_2719627 prefixEnd_2719627 1396475851945336180555169 := by
  unfold tailWord_2719627
  simp only [CollatzResearch.WordTrace]
  refine ⟨99192945718263329157941135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66128630478842219438627423 99192945718263329157941135)
  ·
    refine ⟨148789418577394993736911703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99192945718263329157941135 148789418577394993736911703)
    ·
      refine ⟨223184127866092490605367555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148789418577394993736911703 223184127866092490605367555)
      ·
        refine ⟨334776191799138735908051333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223184127866092490605367555 334776191799138735908051333)
        ·
          refine ⟨62770535962338512982759625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 334776191799138735908051333 62770535962338512982759625)
          ·
            refine ⟨47077901971753884737069719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62770535962338512982759625 47077901971753884737069719)
            ·
              refine ⟨70616852957630827105604579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47077901971753884737069719 70616852957630827105604579)
              ·
                refine ⟨105925279436446240658406869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70616852957630827105604579 105925279436446240658406869)
                ·
                  refine ⟨2482623736791708765431411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 105925279436446240658406869 2482623736791708765431411)
                  ·
                    refine ⟨3723935605187563148147117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2482623736791708765431411 3723935605187563148147117)
                    ·
                      refine ⟨1396475851945336180555169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3723935605187563148147117 1396475851945336180555169)
                      ·
                        rfl

theorem cell23_2719627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 1, 3].length) (baseStart_2719627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719627 prefixEnd_2719627 := by exact prefixLift 2719627
  have htrace : WordTrace (prefixWord ++ tailWord_2719627) baseStart_2719627 baseEnd_2719627 := by
    simpa [prefixWord, tailWord_2719627, baseEnd_2719627] using wordTrace_append hprefix tailTrace_2719627
  have hstable : (prefixWord ++ tailWord_2719627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719627).length < 2 ^ (prefixWord ++ tailWord_2719627).sum := by decide
  have hdescent : baseEnd_2719627 < baseStart_2719627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719634 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 6]
def baseStart_2719634 : Nat := 118140960795 + 2719634 * 2 ^ 59
def prefixEnd_2719634 : Nat := 4983230072969 + 3 ^ 40 * 2719634 * 2
def baseEnd_2719634 : Nat := 155164382923324183685293

theorem tailTrace_2719634 : CollatzResearch.WordTrace tailWord_2719634 prefixEnd_2719634 155164382923324183685293 := by
  unfold tailWord_2719634
  simp only [CollatzResearch.WordTrace]
  refine ⟨24798300257309492338361489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66128800686158646235630637 24798300257309492338361489)
  ·
    refine ⟨18598725192982119253771117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24798300257309492338361489 18598725192982119253771117)
    ·
      refine ⟨6974521947368294720164169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18598725192982119253771117 6974521947368294720164169)
      ·
        refine ⟨5230891460526221040123127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6974521947368294720164169 5230891460526221040123127)
        ·
          refine ⟨7846337190789331560184691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5230891460526221040123127 7846337190789331560184691)
          ·
            refine ⟨11769505786183997340277037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7846337190789331560184691 11769505786183997340277037)
            ·
              refine ⟨4413564669818999002603889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11769505786183997340277037 4413564669818999002603889)
              ·
                refine ⟨3310173502364249251952917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4413564669818999002603889 3310173502364249251952917)
                ·
                  refine ⟨155164382923324183685293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3310173502364249251952917 155164382923324183685293)
                  ·
                    rfl

theorem cell23_2719634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_2719634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719634 prefixEnd_2719634 := by exact prefixLift 2719634
  have htrace : WordTrace (prefixWord ++ tailWord_2719634) baseStart_2719634 baseEnd_2719634 := by
    simpa [prefixWord, tailWord_2719634, baseEnd_2719634] using wordTrace_append hprefix tailTrace_2719634
  have hstable : (prefixWord ++ tailWord_2719634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719634).length < 2 ^ (prefixWord ++ tailWord_2719634).sum := by decide
  have hdescent : baseEnd_2719634 < baseStart_2719634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719667 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 2, 6, 2]
def baseStart_2719667 : Nat := 118140960795 + 2719667 * 2 ^ 59
def prefixEnd_2719667 : Nat := 4983230072969 + 3 ^ 40 * 2719667 * 2
def baseEnd_2719667 : Nat := 1396496391171516024054985

theorem tailTrace_2719667 : CollatzResearch.WordTrace tailWord_2719667 prefixEnd_2719667 1396496391171516024054985 := by
  unfold tailWord_2719667
  simp only [CollatzResearch.WordTrace]
  refine ⟨99194404638118415989397255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66129603092078943992931503 99194404638118415989397255)
  ·
    refine ⟨148791606957177623984095883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99194404638118415989397255 148791606957177623984095883)
    ·
      refine ⟨223187410435766435976143825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148791606957177623984095883 223187410435766435976143825)
      ·
        refine ⟨167390557826824826982107869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223187410435766435976143825 167390557826824826982107869)
        ·
          refine ⟨62771459185059310118290451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167390557826824826982107869 62771459185059310118290451)
          ·
            refine ⟨94157188777588965177435677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62771459185059310118290451 94157188777588965177435677)
            ·
              refine ⟨35308945791595861941538379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94157188777588965177435677 35308945791595861941538379)
              ·
                refine ⟨52963418687393792912307569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35308945791595861941538379 52963418687393792912307569)
                ·
                  refine ⟨39722564015545344684230677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52963418687393792912307569 39722564015545344684230677)
                  ·
                    refine ⟨1861995188228688032073313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39722564015545344684230677 1861995188228688032073313)
                    ·
                      refine ⟨1396496391171516024054985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1861995188228688032073313 1396496391171516024054985)
                      ·
                        rfl

theorem cell23_2719667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 6, 2].length) (baseStart_2719667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719667 prefixEnd_2719667 := by exact prefixLift 2719667
  have htrace : WordTrace (prefixWord ++ tailWord_2719667) baseStart_2719667 baseEnd_2719667 := by
    simpa [prefixWord, tailWord_2719667, baseEnd_2719667] using wordTrace_append hprefix tailTrace_2719667
  have hstable : (prefixWord ++ tailWord_2719667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719667).length < 2 ^ (prefixWord ++ tailWord_2719667).sum := by decide
  have hdescent : baseEnd_2719667 < baseStart_2719667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719678 : List Nat := [4, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_2719678 : Nat := 118140960795 + 2719678 * 2 ^ 59
def prefixEnd_2719678 : Nat := 4983230072969 + 3 ^ 40 * 2719678 * 2
def baseEnd_2719678 : Nat := 1396502039458715481017435

theorem tailTrace_2719678 : CollatzResearch.WordTrace tailWord_2719678 prefixEnd_2719678 1396502039458715481017435 := by
  unfold tailWord_2719678
  simp only [CollatzResearch.WordTrace]
  refine ⟨12399350730134820608505961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66129870560719043245365125 12399350730134820608505961)
  ·
    refine ⟨9299513047601115456379471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12399350730134820608505961 9299513047601115456379471)
    ·
      refine ⟨13949269571401673184569207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9299513047601115456379471 13949269571401673184569207)
      ·
        refine ⟨20923904357102509776853811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13949269571401673184569207 20923904357102509776853811)
        ·
          refine ⟨31385856535653764665280717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20923904357102509776853811 31385856535653764665280717)
          ·
            refine ⟨11769696200870161749480269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31385856535653764665280717 11769696200870161749480269)
            ·
              refine ⟨4413636075326310656055101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11769696200870161749480269 4413636075326310656055101)
              ·
                refine ⟨1655113528247366496020663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4413636075326310656055101 1655113528247366496020663)
                ·
                  refine ⟨2482670292371049744030995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655113528247366496020663 2482670292371049744030995)
                  ·
                    refine ⟨3724005438556574616046493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2482670292371049744030995 3724005438556574616046493)
                    ·
                      refine ⟨1396502039458715481017435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3724005438556574616046493 1396502039458715481017435)
                      ·
                        rfl

theorem cell23_2719678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_2719678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719678 prefixEnd_2719678 := by exact prefixLift 2719678
  have htrace : WordTrace (prefixWord ++ tailWord_2719678) baseStart_2719678 baseEnd_2719678 := by
    simpa [prefixWord, tailWord_2719678, baseEnd_2719678] using wordTrace_append hprefix tailTrace_2719678
  have hstable : (prefixWord ++ tailWord_2719678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719678).length < 2 ^ (prefixWord ++ tailWord_2719678).sum := by decide
  have hdescent : baseEnd_2719678 < baseStart_2719678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719687 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_2719687 : Nat := 118140960795 + 2719687 * 2 ^ 59
def prefixEnd_2719687 : Nat := 4983230072969 + 3 ^ 40 * 2719687 * 2
def baseEnd_2719687 : Nat := 1396506660784605945804893

theorem tailTrace_2719687 : CollatzResearch.WordTrace tailWord_2719687 prefixEnd_2719687 1396506660784605945804893 := by
  unfold tailWord_2719687
  simp only [CollatzResearch.WordTrace]
  refine ⟨99195134098045959405125315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66130089398697306270083543 99195134098045959405125315)
  ·
    refine ⟨148792701147068939107687973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99195134098045959405125315 148792701147068939107687973)
    ·
      refine ⟨27898631465075426082691495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148792701147068939107687973 27898631465075426082691495)
      ·
        refine ⟨41847947197613139124037243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27898631465075426082691495 41847947197613139124037243)
        ·
          refine ⟨62771920796419708686055865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41847947197613139124037243 62771920796419708686055865)
          ·
            refine ⟨47078940597314781514541899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62771920796419708686055865 47078940597314781514541899)
            ·
              refine ⟨70618410895972172271812849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47078940597314781514541899 70618410895972172271812849)
              ·
                refine ⟨52963808171979129203859637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70618410895972172271812849 52963808171979129203859637)
                ·
                  refine ⟨4965357016123043362861841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52963808171979129203859637 4965357016123043362861841)
                  ·
                    refine ⟨3724017762092282522146381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4965357016123043362861841 3724017762092282522146381)
                    ·
                      refine ⟨1396506660784605945804893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3724017762092282522146381 1396506660784605945804893)
                      ·
                        rfl

theorem cell23_2719687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_2719687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719687 prefixEnd_2719687 := by exact prefixLift 2719687
  have htrace : WordTrace (prefixWord ++ tailWord_2719687) baseStart_2719687 baseEnd_2719687 := by
    simpa [prefixWord, tailWord_2719687, baseEnd_2719687] using wordTrace_append hprefix tailTrace_2719687
  have hstable : (prefixWord ++ tailWord_2719687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719687).length < 2 ^ (prefixWord ++ tailWord_2719687).sum := by decide
  have hdescent : baseEnd_2719687 < baseStart_2719687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719690 : List Nat := [3, 1, 2, 1, 2, 1, 13]
def baseStart_2719690 : Nat := 118140960795 + 2719690 * 2 ^ 59
def prefixEnd_2719690 : Nat := 4983230072969 + 3 ^ 40 * 2719690 * 2
def baseEnd_2719690 : Nat := 17240841990451474494659

theorem tailTrace_2719690 : CollatzResearch.WordTrace tailWord_2719690 prefixEnd_2719690 17240841990451474494659 := by
  unfold tailWord_2719690
  simp only [CollatzResearch.WordTrace]
  refine ⟨24798810879258772729371131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66130162344690060611656349 24798810879258772729371131)
  ·
    refine ⟨37198216318888159094056697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24798810879258772729371131 37198216318888159094056697)
    ·
      refine ⟨27898662239166119320542523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37198216318888159094056697 27898662239166119320542523)
      ·
        refine ⟨41847993358749178980813785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27898662239166119320542523 41847993358749178980813785)
        ·
          refine ⟨31385995019061884235610339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41847993358749178980813785 31385995019061884235610339)
          ·
            refine ⟨47078992528592826353415509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31385995019061884235610339 47078992528592826353415509)
            ·
              refine ⟨17240841990451474494659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 47078992528592826353415509 17240841990451474494659)
              ·
                rfl

theorem cell23_2719690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 13].length) (baseStart_2719690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719690 prefixEnd_2719690 := by exact prefixLift 2719690
  have htrace : WordTrace (prefixWord ++ tailWord_2719690) baseStart_2719690 baseEnd_2719690 := by
    simpa [prefixWord, tailWord_2719690, baseEnd_2719690] using wordTrace_append hprefix tailTrace_2719690
  have hstable : (prefixWord ++ tailWord_2719690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719690).length < 2 ^ (prefixWord ++ tailWord_2719690).sum := by decide
  have hdescent : baseEnd_2719690 < baseStart_2719690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719694 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_2719694 : Nat := 118140960795 + 2719694 * 2 ^ 59
def prefixEnd_2719694 : Nat := 4983230072969 + 3 ^ 40 * 2719694 * 2
def baseEnd_2719694 : Nat := 465503418383062472805787

theorem tailTrace_2719694 : CollatzResearch.WordTrace tailWord_2719694 prefixEnd_2719694 465503418383062472805787 := by
  unfold tailWord_2719694
  simp only [CollatzResearch.WordTrace]
  refine ⟨12399423676127574950078767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66130259606013733067086757 12399423676127574950078767)
  ·
    refine ⟨18599135514191362425118151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12399423676127574950078767 18599135514191362425118151)
    ·
      refine ⟨27898703271287043637677227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18599135514191362425118151 27898703271287043637677227)
      ·
        refine ⟨41848054906930565456515841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27898703271287043637677227 41848054906930565456515841)
        ·
          refine ⟨31386041180197924092386881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41848054906930565456515841 31386041180197924092386881)
          ·
            refine ⟨23539530885148443069290161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31386041180197924092386881 23539530885148443069290161)
            ·
              refine ⟨17654648163861332301967621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23539530885148443069290161 17654648163861332301967621)
              ·
                refine ⟨3310246530723999806618929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17654648163861332301967621 3310246530723999806618929)
                ·
                  refine ⟨2482684898042999854964197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310246530723999806618929 2482684898042999854964197)
                  ·
                    refine ⟨465503418383062472805787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2482684898042999854964197 465503418383062472805787)
                    ·
                      rfl

theorem cell23_2719694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_2719694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719694 prefixEnd_2719694 := by exact prefixLift 2719694
  have htrace : WordTrace (prefixWord ++ tailWord_2719694) baseStart_2719694 baseEnd_2719694 := by
    simpa [prefixWord, tailWord_2719694, baseEnd_2719694] using wordTrace_append hprefix tailTrace_2719694
  have hstable : (prefixWord ++ tailWord_2719694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719694).length < 2 ^ (prefixWord ++ tailWord_2719694).sum := by decide
  have hdescent : baseEnd_2719694 < baseStart_2719694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719711 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 2, 4]
def baseStart_2719711 : Nat := 118140960795 + 2719711 * 2 ^ 59
def prefixEnd_2719711 : Nat := 4983230072969 + 3 ^ 40 * 2719711 * 2
def baseEnd_2719711 : Nat := 465506328106771283968261

theorem tailTrace_2719711 : CollatzResearch.WordTrace tailWord_2719711 prefixEnd_2719711 465506328106771283968261 := by
  unfold tailWord_2719711
  simp only [CollatzResearch.WordTrace]
  refine ⟨99196009449959011503998987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66130672966639341002665991 99196009449959011503998987)
  ·
    refine ⟨148794014174938517255998481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99196009449959011503998987 148794014174938517255998481)
    ·
      refine ⟨111595510631203887941998861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148794014174938517255998481 111595510631203887941998861)
      ·
        refine ⟨41848316486701457978249573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111595510631203887941998861 41848316486701457978249573)
        ·
          refine ⟨7846559341256523370921795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41848316486701457978249573 7846559341256523370921795)
          ·
            refine ⟨11769839011884785056382693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7846559341256523370921795 11769839011884785056382693)
            ·
              refine ⟨2206844814728397198071755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11769839011884785056382693 2206844814728397198071755)
              ·
                refine ⟨3310267222092595797107633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206844814728397198071755 3310267222092595797107633)
                ·
                  refine ⟨2482700416569446847830725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310267222092595797107633 2482700416569446847830725)
                  ·
                    refine ⟨465506328106771283968261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2482700416569446847830725 465506328106771283968261)
                    ·
                      rfl

theorem cell23_2719711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 2, 4].length) (baseStart_2719711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719711 prefixEnd_2719711 := by exact prefixLift 2719711
  have htrace : WordTrace (prefixWord ++ tailWord_2719711) baseStart_2719711 baseEnd_2719711 := by
    simpa [prefixWord, tailWord_2719711, baseEnd_2719711] using wordTrace_append hprefix tailTrace_2719711
  have hstable : (prefixWord ++ tailWord_2719711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719711).length < 2 ^ (prefixWord ++ tailWord_2719711).sum := by decide
  have hdescent : baseEnd_2719711 < baseStart_2719711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719751 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2719751 : Nat := 118140960795 + 2719751 * 2 ^ 59
def prefixEnd_2719751 : Nat := 4983230072969 + 3 ^ 40 * 2719751 * 2
def baseEnd_2719751 : Nat := 1396539523546493695404599

theorem tailTrace_2719751 : CollatzResearch.WordTrace tailWord_2719751 prefixEnd_2719751 1396539523546493695404599 := by
  unfold tailWord_2719751
  simp only [CollatzResearch.WordTrace]
  refine ⟨99197468369814098335455107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66131645579876065556970071 99197468369814098335455107)
  ·
    refine ⟨148796202554721147503182661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99197468369814098335455107 148796202554721147503182661)
    ·
      refine ⟨27899287979010215156846749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148796202554721147503182661 27899287979010215156846749)
      ·
        refine ⟨10462232992128830683817531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27899287979010215156846749 10462232992128830683817531)
        ·
          refine ⟨15693349488193246025726297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10462232992128830683817531 15693349488193246025726297)
          ·
            refine ⟨11770012116144934519294723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15693349488193246025726297 11770012116144934519294723)
            ·
              refine ⟨17655018174217401778942085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11770012116144934519294723 17655018174217401778942085)
              ·
                refine ⟨3310315907665762833551641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17655018174217401778942085 3310315907665762833551641)
                ·
                  refine ⟨2482736930749322125163731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310315907665762833551641 2482736930749322125163731)
                  ·
                    refine ⟨3724105396123983187745597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2482736930749322125163731 3724105396123983187745597)
                    ·
                      refine ⟨1396539523546493695404599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3724105396123983187745597 1396539523546493695404599)
                      ·
                        rfl

theorem cell23_2719751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2719751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719751 prefixEnd_2719751 := by exact prefixLift 2719751
  have htrace : WordTrace (prefixWord ++ tailWord_2719751) baseStart_2719751 baseEnd_2719751 := by
    simpa [prefixWord, tailWord_2719751, baseEnd_2719751] using wordTrace_append hprefix tailTrace_2719751
  have hstable : (prefixWord ++ tailWord_2719751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719751).length < 2 ^ (prefixWord ++ tailWord_2719751).sum := by decide
  have hdescent : baseEnd_2719751 < baseStart_2719751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719808 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 2, 2, 2]
def baseStart_2719808 : Nat := 118140960795 + 2719808 * 2 ^ 59
def prefixEnd_2719808 : Nat := 4983230072969 + 3 ^ 40 * 2719808 * 2
def baseEnd_2719808 : Nat := 1396568791943799972391837

theorem tailTrace_2719808 : CollatzResearch.WordTrace tailWord_2719808 prefixEnd_2719808 1396568791943799972391837 := by
  unfold tailWord_2719808
  simp only [CollatzResearch.WordTrace]
  refine ⟨49599773665303798535140039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66133031553738398046853385 49599773665303798535140039)
  ·
    refine ⟨74399660497955697802710059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49599773665303798535140039 74399660497955697802710059)
    ·
      refine ⟨111599490746933546704065089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74399660497955697802710059 111599490746933546704065089)
      ·
        refine ⟨83699618060200160028048817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111599490746933546704065089 83699618060200160028048817)
        ·
          refine ⟨62774713545150120021036613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83699618060200160028048817 62774713545150120021036613)
          ·
            refine ⟨11770258789715647503944365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62774713545150120021036613 11770258789715647503944365)
            ·
              refine ⟨4413847046143367813979137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11770258789715647503944365 4413847046143367813979137)
              ·
                refine ⟨3310385284607525860484353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4413847046143367813979137 3310385284607525860484353)
                ·
                  refine ⟨2482788963455644395363265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310385284607525860484353 2482788963455644395363265)
                  ·
                    refine ⟨1862091722591733296522449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2482788963455644395363265 1862091722591733296522449)
                    ·
                      refine ⟨1396568791943799972391837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862091722591733296522449 1396568791943799972391837)
                      ·
                        rfl

theorem cell23_2719808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_2719808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719808 prefixEnd_2719808 := by exact prefixLift 2719808
  have htrace : WordTrace (prefixWord ++ tailWord_2719808) baseStart_2719808 baseEnd_2719808 := by
    simpa [prefixWord, tailWord_2719808, baseEnd_2719808] using wordTrace_append hprefix tailTrace_2719808
  have hstable : (prefixWord ++ tailWord_2719808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719808).length < 2 ^ (prefixWord ++ tailWord_2719808).sum := by decide
  have hdescent : baseEnd_2719808 < baseStart_2719808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719854 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2719854 : Nat := 118140960795 + 2719854 * 2 ^ 59
def prefixEnd_2719854 : Nat := 4983230072969 + 3 ^ 40 * 2719854 * 2
def baseEnd_2719854 : Nat := 1396592412053906792416625

theorem tailTrace_2719854 : CollatzResearch.WordTrace tailWord_2719854 prefixEnd_2719854 1396592412053906792416625 := by
  unfold tailWord_2719854
  simp only [CollatzResearch.WordTrace]
  refine ⟨12400153136055118365806827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66134150058960631284303077 12400153136055118365806827)
  ·
    refine ⟨18600229704082677548710241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12400153136055118365806827 18600229704082677548710241)
    ·
      refine ⟨13950172278062008161532681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18600229704082677548710241 13950172278062008161532681)
      ·
        refine ⟨10462629208546506121149511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13950172278062008161532681 10462629208546506121149511)
        ·
          refine ⟨15693943812819759181724267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10462629208546506121149511 15693943812819759181724267)
          ·
            refine ⟨23540915719229638772586401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15693943812819759181724267 23540915719229638772586401)
            ·
              refine ⟨17655686789422229079439801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23540915719229638772586401 17655686789422229079439801)
              ·
                refine ⟨13241765092066671809579851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17655686789422229079439801 13241765092066671809579851)
                ·
                  refine ⟨19862647638100007714369777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13241765092066671809579851 19862647638100007714369777)
                  ·
                    refine ⟨14896985728575005785777333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19862647638100007714369777 14896985728575005785777333)
                    ·
                      refine ⟨1396592412053906792416625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14896985728575005785777333 1396592412053906792416625)
                      ·
                        rfl

theorem cell23_2719854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2719854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719854 prefixEnd_2719854 := by exact prefixLift 2719854
  have htrace : WordTrace (prefixWord ++ tailWord_2719854) baseStart_2719854 baseEnd_2719854 := by
    simpa [prefixWord, tailWord_2719854, baseEnd_2719854] using wordTrace_append hprefix tailTrace_2719854
  have hstable : (prefixWord ++ tailWord_2719854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719854).length < 2 ^ (prefixWord ++ tailWord_2719854).sum := by decide
  have hdescent : baseEnd_2719854 < baseStart_2719854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719898 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2719898 : Nat := 118140960795 + 2719898 * 2 ^ 59
def prefixEnd_2719898 : Nat := 4983230072969 + 3 ^ 40 * 2719898 * 2
def baseEnd_2719898 : Nat := 1396615005202704620266423

theorem tailTrace_2719898 : CollatzResearch.WordTrace tailWord_2719898 prefixEnd_2719898 1396615005202704620266423 := by
  unfold tailWord_2719898
  simp only [CollatzResearch.WordTrace]
  refine ⟨24800707475070385610264087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66135219933521028294037565 24800707475070385610264087)
  ·
    refine ⟨37201061212605578415396131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24800707475070385610264087 37201061212605578415396131)
    ·
      refine ⟨55801591818908367623094197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37201061212605578415396131 55801591818908367623094197)
      ·
        refine ⟨5231399233022659464665081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55801591818908367623094197 5231399233022659464665081)
        ·
          refine ⟨3923549424766994598498811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5231399233022659464665081 3923549424766994598498811)
          ·
            refine ⟨5885324137150491897748217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3923549424766994598498811 5885324137150491897748217)
            ·
              refine ⟨4413993102862868923311163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5885324137150491897748217 4413993102862868923311163)
              ·
                refine ⟨6620989654294303384966745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413993102862868923311163 6620989654294303384966745)
                ·
                  refine ⟨4965742240720727538725059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6620989654294303384966745 4965742240720727538725059)
                  ·
                    refine ⟨7448613361081091308087589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4965742240720727538725059 7448613361081091308087589)
                    ·
                      refine ⟨1396615005202704620266423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7448613361081091308087589 1396615005202704620266423)
                      ·
                        rfl

theorem cell23_2719898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2719898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719898 prefixEnd_2719898 := by exact prefixLift 2719898
  have htrace : WordTrace (prefixWord ++ tailWord_2719898) baseStart_2719898 baseEnd_2719898 := by
    simpa [prefixWord, tailWord_2719898, baseEnd_2719898] using wordTrace_append hprefix tailTrace_2719898
  have hstable : (prefixWord ++ tailWord_2719898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719898).length < 2 ^ (prefixWord ++ tailWord_2719898).sum := by decide
  have hdescent : baseEnd_2719898 < baseStart_2719898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719901 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_2719901 : Nat := 118140960795 + 2719901 * 2 ^ 59
def prefixEnd_2719901 : Nat := 4983230072969 + 3 ^ 40 * 2719901 * 2
def baseEnd_2719901 : Nat := 1396616545644668108528909

theorem tailTrace_2719901 : CollatzResearch.WordTrace tailWord_2719901 prefixEnd_2719901 1396616545644668108528909 := by
  unfold tailWord_2719901
  simp only [CollatzResearch.WordTrace]
  refine ⟨99202939319270673953415557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66135292879513782635610371 99202939319270673953415557)
  ·
    refine ⟨18600551122363251366265417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99202939319270673953415557 18600551122363251366265417)
    ·
      refine ⟨13950413341772438524699063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18600551122363251366265417 13950413341772438524699063)
      ·
        refine ⟨20925620012658657787048595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13950413341772438524699063 20925620012658657787048595)
        ·
          refine ⟨31388430018987986680572893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20925620012658657787048595 31388430018987986680572893)
          ·
            refine ⟨11770661257120495005214835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31388430018987986680572893 11770661257120495005214835)
            ·
              refine ⟨17655991885680742507822253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11770661257120495005214835 17655991885680742507822253)
              ·
                refine ⟨6620996957130278440433345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17655991885680742507822253 6620996957130278440433345)
                ·
                  refine ⟨4965747717847708830325009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6620996957130278440433345 4965747717847708830325009)
                  ·
                    refine ⟨3724310788385781622743757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4965747717847708830325009 3724310788385781622743757)
                    ·
                      refine ⟨1396616545644668108528909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3724310788385781622743757 1396616545644668108528909)
                      ·
                        rfl

theorem cell23_2719901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_2719901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719901 prefixEnd_2719901 := by exact prefixLift 2719901
  have htrace : WordTrace (prefixWord ++ tailWord_2719901) baseStart_2719901 baseEnd_2719901 := by
    simpa [prefixWord, tailWord_2719901, baseEnd_2719901] using wordTrace_append hprefix tailTrace_2719901
  have hstable : (prefixWord ++ tailWord_2719901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719901).length < 2 ^ (prefixWord ++ tailWord_2719901).sum := by decide
  have hdescent : baseEnd_2719901 < baseStart_2719901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719907 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 8]
def baseStart_2719907 : Nat := 118140960795 + 2719907 * 2 ^ 59
def prefixEnd_2719907 : Nat := 4983230072969 + 3 ^ 40 * 2719907 * 2
def baseEnd_2719907 : Nat := 1396619626528595085053881

theorem tailTrace_2719907 : CollatzResearch.WordTrace tailWord_2719907 prefixEnd_2719907 1396619626528595085053881 := by
  unfold tailWord_2719907
  simp only [CollatzResearch.WordTrace]
  refine ⟨99203158157248936978133975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66135438771499291318755983 99203158157248936978133975)
  ·
    refine ⟨148804737235873405467200963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99203158157248936978133975 148804737235873405467200963)
    ·
      refine ⟨223207105853810108200801445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148804737235873405467200963 223207105853810108200801445)
      ·
        refine ⟨41851332347589395287650271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223207105853810108200801445 41851332347589395287650271)
        ·
          refine ⟨62776998521384092931475407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41851332347589395287650271 62776998521384092931475407)
          ·
            refine ⟨94165497782076139397213111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62776998521384092931475407 94165497782076139397213111)
            ·
              refine ⟨141248246673114209095819667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94165497782076139397213111 141248246673114209095819667)
              ·
                refine ⟨211872370009671313643729501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141248246673114209095819667 211872370009671313643729501)
                ·
                  refine ⟨79452138753626742616398563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211872370009671313643729501 79452138753626742616398563)
                  ·
                    refine ⟨119178208130440113924597845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79452138753626742616398563 119178208130440113924597845)
                    ·
                      refine ⟨1396619626528595085053881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 119178208130440113924597845 1396619626528595085053881)
                      ·
                        rfl

theorem cell23_2719907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_2719907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719907 prefixEnd_2719907 := by exact prefixLift 2719907
  have htrace : WordTrace (prefixWord ++ tailWord_2719907) baseStart_2719907 baseEnd_2719907 := by
    simpa [prefixWord, tailWord_2719907, baseEnd_2719907] using wordTrace_append hprefix tailTrace_2719907
  have hstable : (prefixWord ++ tailWord_2719907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719907).length < 2 ^ (prefixWord ++ tailWord_2719907).sum := by decide
  have hdescent : baseEnd_2719907 < baseStart_2719907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719931 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 3, 1, 3]
def baseStart_2719931 : Nat := 118140960795 + 2719931 * 2 ^ 59
def prefixEnd_2719931 : Nat := 4983230072969 + 3 ^ 40 * 2719931 * 2
def baseEnd_2719931 : Nat := 1396631950064302991153771

theorem tailTrace_2719931 : CollatzResearch.WordTrace tailWord_2719931 prefixEnd_2719931 1396631950064302991153771 := by
  unfold tailWord_2719931
  simp only [CollatzResearch.WordTrace]
  refine ⟨99204033509161989077007647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66136022339441326051338431 99204033509161989077007647)
  ·
    refine ⟨148806050263742983615511471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99204033509161989077007647 148806050263742983615511471)
    ·
      refine ⟨223209075395614475423267207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148806050263742983615511471 223209075395614475423267207)
      ·
        refine ⟨334813613093421713134900811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223209075395614475423267207 334813613093421713134900811)
        ·
          refine ⟨502220419640132569702351217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334813613093421713134900811 502220419640132569702351217)
          ·
            refine ⟨376665314730099427276763413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502220419640132569702351217 376665314730099427276763413)
            ·
              refine ⟨17656186627973410653598285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 376665314730099427276763413 17656186627973410653598285)
              ·
                refine ⟨6621069985490028995099357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17656186627973410653598285 6621069985490028995099357)
                ·
                  refine ⟨2482901244558760873162259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6621069985490028995099357 2482901244558760873162259)
                  ·
                    refine ⟨3724351866838141309743389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2482901244558760873162259 3724351866838141309743389)
                    ·
                      refine ⟨1396631950064302991153771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3724351866838141309743389 1396631950064302991153771)
                      ·
                        rfl

theorem cell23_2719931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 1, 3].length) (baseStart_2719931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719931 prefixEnd_2719931 := by exact prefixLift 2719931
  have htrace : WordTrace (prefixWord ++ tailWord_2719931) baseStart_2719931 baseEnd_2719931 := by
    simpa [prefixWord, tailWord_2719931, baseEnd_2719931] using wordTrace_append hprefix tailTrace_2719931
  have hstable : (prefixWord ++ tailWord_2719931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719931).length < 2 ^ (prefixWord ++ tailWord_2719931).sum := by decide
  have hdescent : baseEnd_2719931 < baseStart_2719931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719941 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 4, 3, 2]
def baseStart_2719941 : Nat := 118140960795 + 2719941 * 2 ^ 59
def prefixEnd_2719941 : Nat := 4983230072969 + 3 ^ 40 * 2719941 * 2
def baseEnd_2719941 : Nat := 1396637084870847952028725

theorem tailTrace_2719941 : CollatzResearch.WordTrace tailWord_2719941 prefixEnd_2719941 1396637084870847952028725 := by
  unfold tailWord_2719941
  simp only [CollatzResearch.WordTrace]
  refine ⟨99204398239125760784871677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66136265492750507189914451 99204398239125760784871677)
  ·
    refine ⟨37201649339672160294326879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99204398239125760784871677 37201649339672160294326879)
    ·
      refine ⟨55802474009508240441490319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37201649339672160294326879 55802474009508240441490319)
      ·
        refine ⟨83703711014262360662235479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55802474009508240441490319 83703711014262360662235479)
        ·
          refine ⟨125555566521393540993353219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83703711014262360662235479 125555566521393540993353219)
          ·
            refine ⟨188333349782090311490029829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125555566521393540993353219 188333349782090311490029829)
            ·
              refine ⟨35312503084141933404380593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188333349782090311490029829 35312503084141933404380593)
              ·
                refine ⟨26484377313106450053285445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35312503084141933404380593 26484377313106450053285445)
                ·
                  refine ⟨4965820746207459384991021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26484377313106450053285445 4965820746207459384991021)
                  ·
                    refine ⟨1862182779827797269371633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4965820746207459384991021 1862182779827797269371633)
                    ·
                      refine ⟨1396637084870847952028725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862182779827797269371633 1396637084870847952028725)
                      ·
                        rfl

theorem cell23_2719941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_2719941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719941 prefixEnd_2719941 := by exact prefixLift 2719941
  have htrace : WordTrace (prefixWord ++ tailWord_2719941) baseStart_2719941 baseEnd_2719941 := by
    simpa [prefixWord, tailWord_2719941, baseEnd_2719941] using wordTrace_append hprefix tailTrace_2719941
  have hstable : (prefixWord ++ tailWord_2719941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719941).length < 2 ^ (prefixWord ++ tailWord_2719941).sum := by decide
  have hdescent : baseEnd_2719941 < baseStart_2719941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719984 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_2719984 : Nat := 118140960795 + 2719984 * 2 ^ 59
def prefixEnd_2719984 : Nat := 4983230072969 + 3 ^ 40 * 2719984 * 2
def baseEnd_2719984 : Nat := 1396659164538991283791027

theorem tailTrace_2719984 : CollatzResearch.WordTrace tailWord_2719984 prefixEnd_2719984 1396659164538991283791027 := by
  unfold tailWord_2719984
  simp only [CollatzResearch.WordTrace]
  refine ⟨49602983288984989564343503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66137311051979986085791337 49602983288984989564343503)
  ·
    refine ⟨74404474933477484346515255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49602983288984989564343503 74404474933477484346515255)
    ·
      refine ⟨111606712400216226519772883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74404474933477484346515255 111606712400216226519772883)
      ·
        refine ⟨167410068600324339779659325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111606712400216226519772883 167410068600324339779659325)
        ·
          refine ⟨62778775725121627417372247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167410068600324339779659325 62778775725121627417372247)
          ·
            refine ⟨94168163587682441126058371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62778775725121627417372247 94168163587682441126058371)
            ·
              refine ⟨141252245381523661689087557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94168163587682441126058371 141252245381523661689087557)
              ·
                refine ⟨26484796009035686566703917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141252245381523661689087557 26484796009035686566703917)
                ·
                  refine ⟨9931798503388382462513969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26484796009035686566703917 9931798503388382462513969)
                  ·
                    refine ⟨7448848877541286846885477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9931798503388382462513969 7448848877541286846885477)
                    ·
                      refine ⟨1396659164538991283791027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7448848877541286846885477 1396659164538991283791027)
                      ·
                        rfl

theorem cell23_2719984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_2719984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2719984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2719984 prefixEnd_2719984 := by exact prefixLift 2719984
  have htrace : WordTrace (prefixWord ++ tailWord_2719984) baseStart_2719984 baseEnd_2719984 := by
    simpa [prefixWord, tailWord_2719984, baseEnd_2719984] using wordTrace_append hprefix tailTrace_2719984
  have hstable : (prefixWord ++ tailWord_2719984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719984).length < 2 ^ (prefixWord ++ tailWord_2719984).sum := by decide
  have hdescent : baseEnd_2719984 < baseStart_2719984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720008 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_2720008 : Nat := 118140960795 + 2720008 * 2 ^ 59
def prefixEnd_2720008 : Nat := 4983230072969 + 3 ^ 40 * 2720008 * 2
def baseEnd_2720008 : Nat := 1396671488074699189890917

theorem tailTrace_2720008 : CollatzResearch.WordTrace tailWord_2720008 prefixEnd_2720008 1396671488074699189890917 := by
  unfold tailWord_2720008
  simp only [CollatzResearch.WordTrace]
  refine ⟨49603420964941515613780339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66137894619922020818373785 49603420964941515613780339)
  ·
    refine ⟨74405131447412273420670509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49603420964941515613780339 74405131447412273420670509)
    ·
      refine ⟨27901924292779602532751441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74405131447412273420670509 27901924292779602532751441)
      ·
        refine ⟨20926443219584701899563581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27901924292779602532751441 20926443219584701899563581)
        ·
          refine ⟨7847416207344263212336343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20926443219584701899563581 7847416207344263212336343)
          ·
            refine ⟨11771124311016394818504515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7847416207344263212336343 11771124311016394818504515)
            ·
              refine ⟨17656686466524592227756773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11771124311016394818504515 17656686466524592227756773)
              ·
                refine ⟨3310628712473361042704395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17656686466524592227756773 3310628712473361042704395)
                ·
                  refine ⟨4965943068710041564056593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310628712473361042704395 4965943068710041564056593)
                  ·
                    refine ⟨3724457301532531173042445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4965943068710041564056593 3724457301532531173042445)
                    ·
                      refine ⟨1396671488074699189890917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3724457301532531173042445 1396671488074699189890917)
                      ·
                        rfl

theorem cell23_2720008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_2720008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720008 prefixEnd_2720008 := by exact prefixLift 2720008
  have htrace : WordTrace (prefixWord ++ tailWord_2720008) baseStart_2720008 baseEnd_2720008 := by
    simpa [prefixWord, tailWord_2720008, baseEnd_2720008] using wordTrace_append hprefix tailTrace_2720008
  have hstable : (prefixWord ++ tailWord_2720008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720008).length < 2 ^ (prefixWord ++ tailWord_2720008).sum := by decide
  have hdescent : baseEnd_2720008 < baseStart_2720008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720021 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_2720021 : Nat := 118140960795 + 2720021 * 2 ^ 59
def prefixEnd_2720021 : Nat := 4983230072969 + 3 ^ 40 * 2720021 * 2
def baseEnd_2720021 : Nat := 1396678163323207639028357

theorem tailTrace_2720021 : CollatzResearch.WordTrace tailWord_2720021 prefixEnd_2720021 1396678163323207639028357 := by
  unfold tailWord_2720021
  simp only [CollatzResearch.WordTrace]
  refine ⟨99207316078835934447783917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66138210719223956298522611 99207316078835934447783917)
  ·
    refine ⟨37202743529563475417918969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99207316078835934447783917 37202743529563475417918969)
    ·
      refine ⟨27902057647172606563439227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37202743529563475417918969 27902057647172606563439227)
      ·
        refine ⟨41853086470758909845158841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27902057647172606563439227 41853086470758909845158841)
        ·
          refine ⟨31389814853069182383869131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41853086470758909845158841 31389814853069182383869131)
          ·
            refine ⟨47084722279603773575803697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31389814853069182383869131 47084722279603773575803697)
            ·
              refine ⟨35313541709702830181852773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47084722279603773575803697 35313541709702830181852773)
              ·
                refine ⟨6621289070569280659097395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35313541709702830181852773 6621289070569280659097395)
                ·
                  refine ⟨9931933605853920988646093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6621289070569280659097395 9931933605853920988646093)
                  ·
                    refine ⟨3724475102195220370742285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9931933605853920988646093 3724475102195220370742285)
                    ·
                      refine ⟨1396678163323207639028357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3724475102195220370742285 1396678163323207639028357)
                      ·
                        rfl

theorem cell23_2720021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_2720021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720021 prefixEnd_2720021 := by exact prefixLift 2720021
  have htrace : WordTrace (prefixWord ++ tailWord_2720021) baseStart_2720021 baseEnd_2720021 := by
    simpa [prefixWord, tailWord_2720021, baseEnd_2720021] using wordTrace_append hprefix tailTrace_2720021
  have hstable : (prefixWord ++ tailWord_2720021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720021).length < 2 ^ (prefixWord ++ tailWord_2720021).sum := by decide
  have hdescent : baseEnd_2720021 < baseStart_2720021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720081 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_2720081 : Nat := 118140960795 + 2720081 * 2 ^ 59
def prefixEnd_2720081 : Nat := 4983230072969 + 3 ^ 40 * 2720081 * 2
def baseEnd_2720081 : Nat := 1396708972162477404278081

theorem tailTrace_2720081 : CollatzResearch.WordTrace tailWord_2720081 prefixEnd_2720081 1396708972162477404278081 := by
  unfold tailWord_2720081
  simp only [CollatzResearch.WordTrace]
  refine ⟨99209504458618564694968097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66139669639079043129978731 99209504458618564694968097)
  ·
    refine ⟨74407128343963923521226073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99209504458618564694968097 74407128343963923521226073)
    ·
      refine ⟨55805346257972942640919555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74407128343963923521226073 55805346257972942640919555)
      ·
        refine ⟨83708019386959413961379333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55805346257972942640919555 83708019386959413961379333)
        ·
          refine ⟨15695253635054890117758625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83708019386959413961379333 15695253635054890117758625)
          ·
            refine ⟨11771440226291167588318969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15695253635054890117758625 11771440226291167588318969)
            ·
              refine ⟨8828580169718375691239227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11771440226291167588318969 8828580169718375691239227)
              ·
                refine ⟨13242870254577563536858841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8828580169718375691239227 13242870254577563536858841)
                ·
                  refine ⟨9932152690933172652644131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13242870254577563536858841 9932152690933172652644131)
                  ·
                    refine ⟨14898229036399758978966197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9932152690933172652644131 14898229036399758978966197)
                    ·
                      refine ⟨1396708972162477404278081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14898229036399758978966197 1396708972162477404278081)
                      ·
                        rfl

theorem cell23_2720081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_2720081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720081 prefixEnd_2720081 := by exact prefixLift 2720081
  have htrace : WordTrace (prefixWord ++ tailWord_2720081) baseStart_2720081 baseEnd_2720081 := by
    simpa [prefixWord, tailWord_2720081, baseEnd_2720081] using wordTrace_append hprefix tailTrace_2720081
  have hstable : (prefixWord ++ tailWord_2720081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720081).length < 2 ^ (prefixWord ++ tailWord_2720081).sum := by decide
  have hdescent : baseEnd_2720081 < baseStart_2720081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720095 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 2, 2, 2]
def baseStart_2720095 : Nat := 118140960795 + 2720095 * 2 ^ 59
def prefixEnd_2720095 : Nat := 4983230072969 + 3 ^ 40 * 2720095 * 2
def baseEnd_2720095 : Nat := 1396716160891640349503017

theorem tailTrace_2720095 : CollatzResearch.WordTrace tailWord_2720095 prefixEnd_2720095 1396716160891640349503017 := by
  unfold tailWord_2720095
  simp only [CollatzResearch.WordTrace]
  refine ⟨99210015080567845085977739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66140010053711896723985159 99210015080567845085977739)
  ·
    refine ⟨148815022620851767628966609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99210015080567845085977739 148815022620851767628966609)
    ·
      refine ⟨111611266965638825721724957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148815022620851767628966609 111611266965638825721724957)
      ·
        refine ⟨41854225112114559645646859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111611266965638825721724957 41854225112114559645646859)
        ·
          refine ⟨62781337668171839468470289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41854225112114559645646859 62781337668171839468470289)
          ·
            refine ⟨47086003251128879601352717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62781337668171839468470289 47086003251128879601352717)
            ·
              refine ⟨17657251219173329850507269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47086003251128879601352717 17657251219173329850507269)
              ·
                refine ⟨3310734603594999346970113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17657251219173329850507269 3310734603594999346970113)
                ·
                  refine ⟨2483050952696249510227585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310734603594999346970113 2483050952696249510227585)
                  ·
                    refine ⟨1862288214522187132670689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2483050952696249510227585 1862288214522187132670689)
                    ·
                      refine ⟨1396716160891640349503017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862288214522187132670689 1396716160891640349503017)
                      ·
                        rfl

theorem cell23_2720095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_2720095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720095 prefixEnd_2720095 := by exact prefixLift 2720095
  have htrace : WordTrace (prefixWord ++ tailWord_2720095) baseStart_2720095 baseEnd_2720095 := by
    simpa [prefixWord, tailWord_2720095, baseEnd_2720095] using wordTrace_append hprefix tailTrace_2720095
  have hstable : (prefixWord ++ tailWord_2720095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720095).length < 2 ^ (prefixWord ++ tailWord_2720095).sum := by decide
  have hdescent : baseEnd_2720095 < baseStart_2720095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720098 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2720098 : Nat := 118140960795 + 2720098 * 2 ^ 59
def prefixEnd_2720098 : Nat := 4983230072969 + 3 ^ 40 * 2720098 * 2
def baseEnd_2720098 : Nat := 1396717701333603837765503

theorem tailTrace_2720098 : CollatzResearch.WordTrace tailWord_2720098 prefixEnd_2720098 1396717701333603837765503 := by
  unfold tailWord_2720098
  simp only [CollatzResearch.WordTrace]
  refine ⟨24802531124889244149584237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66140082999704651065557965 24802531124889244149584237)
  ·
    refine ⟨9300949171833466556094089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24802531124889244149584237 9300949171833466556094089)
    ·
      refine ⟨6975711878875099917070567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9300949171833466556094089 6975711878875099917070567)
      ·
        refine ⟨10463567818312649875605851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6975711878875099917070567 10463567818312649875605851)
        ·
          refine ⟨15695351727468974813408777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10463567818312649875605851 15695351727468974813408777)
          ·
            refine ⟨11771513795601731110056583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15695351727468974813408777 11771513795601731110056583)
            ·
              refine ⟨17657270693402596665084875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11771513795601731110056583 17657270693402596665084875)
              ·
                refine ⟨26485906040103894997627313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17657270693402596665084875 26485906040103894997627313)
                ·
                  refine ⟨19864429530077921248220485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26485906040103894997627313 19864429530077921248220485)
                  ·
                    refine ⟨3724580536889610234041341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19864429530077921248220485 3724580536889610234041341)
                    ·
                      refine ⟨1396717701333603837765503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3724580536889610234041341 1396717701333603837765503)
                      ·
                        rfl

theorem cell23_2720098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2720098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720098 prefixEnd_2720098 := by exact prefixLift 2720098
  have htrace : WordTrace (prefixWord ++ tailWord_2720098) baseStart_2720098 baseEnd_2720098 := by
    simpa [prefixWord, tailWord_2720098, baseEnd_2720098] using wordTrace_append hprefix tailTrace_2720098
  have hstable : (prefixWord ++ tailWord_2720098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720098).length < 2 ^ (prefixWord ++ tailWord_2720098).sum := by decide
  have hdescent : baseEnd_2720098 < baseStart_2720098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720108 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 4]
def baseStart_2720108 : Nat := 118140960795 + 2720108 * 2 ^ 59
def prefixEnd_2720108 : Nat := 4983230072969 + 3 ^ 40 * 2720108 * 2
def baseEnd_2720108 : Nat := 1396722836140148798640457

theorem tailTrace_2720108 : CollatzResearch.WordTrace tailWord_2720108 prefixEnd_2720108 1396722836140148798640457 := by
  unfold tailWord_2720108
  simp only [CollatzResearch.WordTrace]
  refine ⟨49605244614760374153100489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66140326153013832204133985 49605244614760374153100489)
  ·
    refine ⟨37203933461070280614825367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49605244614760374153100489 37203933461070280614825367)
    ·
      refine ⟨55805900191605420922238051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37203933461070280614825367 55805900191605420922238051)
      ·
        refine ⟨83708850287408131383357077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55805900191605420922238051 83708850287408131383357077)
        ·
          refine ⟨3923852357222256158594863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83708850287408131383357077 3923852357222256158594863)
          ·
            refine ⟨5885778535833384237892295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3923852357222256158594863 5885778535833384237892295)
            ·
              refine ⟨8828667803750076356838443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5885778535833384237892295 8828667803750076356838443)
              ·
                refine ⟨13243001705625114535257665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8828667803750076356838443 13243001705625114535257665)
                ·
                  refine ⟨9932251279218835901443249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13243001705625114535257665 9932251279218835901443249)
                  ·
                    refine ⟨7449188459414126926082437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9932251279218835901443249 7449188459414126926082437)
                    ·
                      refine ⟨1396722836140148798640457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7449188459414126926082437 1396722836140148798640457)
                      ·
                        rfl

theorem cell23_2720108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_2720108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720108 prefixEnd_2720108 := by exact prefixLift 2720108
  have htrace : WordTrace (prefixWord ++ tailWord_2720108) baseStart_2720108 baseEnd_2720108 := by
    simpa [prefixWord, tailWord_2720108, baseEnd_2720108] using wordTrace_append hprefix tailTrace_2720108
  have hstable : (prefixWord ++ tailWord_2720108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720108).length < 2 ^ (prefixWord ++ tailWord_2720108).sum := by decide
  have hdescent : baseEnd_2720108 < baseStart_2720108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720178 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_2720178 : Nat := 118140960795 + 2720178 * 2 ^ 59
def prefixEnd_2720178 : Nat := 4983230072969 + 3 ^ 40 * 2720178 * 2
def baseEnd_2720178 : Nat := 465586259928654508255045

theorem tailTrace_2720178 : CollatzResearch.WordTrace tailWord_2720178 prefixEnd_2720178 465586259928654508255045 := by
  unfold tailWord_2720178
  simp only [CollatzResearch.WordTrace]
  refine ⟨24803260584816787565312297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66142028226178100174166125 24803260584816787565312297)
  ·
    refine ⟨18602445438612590673984223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24803260584816787565312297 18602445438612590673984223)
    ·
      refine ⟨27903668157918886010976335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18602445438612590673984223 27903668157918886010976335)
      ·
        refine ⟨41855502236878329016464503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27903668157918886010976335 41855502236878329016464503)
        ·
          refine ⟨62783253355317493524696755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41855502236878329016464503 62783253355317493524696755)
          ·
            refine ⟨94174880032976240287045133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62783253355317493524696755 94174880032976240287045133)
            ·
              refine ⟨35315580012366090107641925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94174880032976240287045133 35315580012366090107641925)
              ·
                refine ⟨6621671252318641895182861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35315580012366090107641925 6621671252318641895182861)
                ·
                  refine ⟨2483126719619490710693573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6621671252318641895182861 2483126719619490710693573)
                  ·
                    refine ⟨465586259928654508255045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2483126719619490710693573 465586259928654508255045)
                    ·
                      rfl

theorem cell23_2720178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_2720178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720178 prefixEnd_2720178 := by exact prefixLift 2720178
  have htrace : WordTrace (prefixWord ++ tailWord_2720178) baseStart_2720178 baseEnd_2720178 := by
    simpa [prefixWord, tailWord_2720178, baseEnd_2720178] using wordTrace_append hprefix tailTrace_2720178
  have hstable : (prefixWord ++ tailWord_2720178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720178).length < 2 ^ (prefixWord ++ tailWord_2720178).sum := by decide
  have hdescent : baseEnd_2720178 < baseStart_2720178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720212 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_2720212 : Nat := 118140960795 + 2720212 * 2 ^ 59
def prefixEnd_2720212 : Nat := 4983230072969 + 3 ^ 40 * 2720212 * 2
def baseEnd_2720212 : Nat := 465592079376072130579993

theorem tailTrace_2720212 : CollatzResearch.WordTrace tailWord_2720212 prefixEnd_2720212 465592079376072130579993 := by
  unfold tailWord_2720212
  simp only [CollatzResearch.WordTrace]
  refine ⟨49607141210571987033993445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66142854947429316045324593 49607141210571987033993445)
  ·
    refine ⟨9301338976982247568873771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49607141210571987033993445 9301338976982247568873771)
    ·
      refine ⟨13952008465473371353310657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9301338976982247568873771 13952008465473371353310657)
      ·
        refine ⟨10464006349105028514982993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13952008465473371353310657 10464006349105028514982993)
        ·
          refine ⟨7848004761828771386237245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10464006349105028514982993 7848004761828771386237245)
          ·
            refine ⟨2943001785685789269838967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7848004761828771386237245 2943001785685789269838967)
            ·
              refine ⟨4414502678528683904758451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943001785685789269838967 4414502678528683904758451)
              ·
                refine ⟨6621754017793025857137677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414502678528683904758451 6621754017793025857137677)
                ·
                  refine ⟨2483157756672384696426629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6621754017793025857137677 2483157756672384696426629)
                  ·
                    refine ⟨465592079376072130579993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2483157756672384696426629 465592079376072130579993)
                    ·
                      rfl

theorem cell23_2720212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_2720212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720212 prefixEnd_2720212 := by exact prefixLift 2720212
  have htrace : WordTrace (prefixWord ++ tailWord_2720212) baseStart_2720212 baseEnd_2720212 := by
    simpa [prefixWord, tailWord_2720212, baseEnd_2720212] using wordTrace_append hprefix tailTrace_2720212
  have hstable : (prefixWord ++ tailWord_2720212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720212).length < 2 ^ (prefixWord ++ tailWord_2720212).sum := by decide
  have hdescent : baseEnd_2720212 < baseStart_2720212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720252 : List Nat := [2, 2, 2, 1, 2, 1, 1, 7, 1, 1, 3]
def baseStart_2720252 : Nat := 118140960795 + 2720252 * 2 ^ 59
def prefixEnd_2720252 : Nat := 4983230072969 + 3 ^ 40 * 2720252 * 2
def baseEnd_2720252 : Nat := 1396796777354396235239795

theorem tailTrace_2720252 : CollatzResearch.WordTrace tailWord_2720252 prefixEnd_2720252 1396796777354396235239795 := by
  unfold tailWord_2720252
  simp only [CollatzResearch.WordTrace]
  refine ⟨49607870670499530449721505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66143827560666040599628673 49607870670499530449721505)
  ·
    refine ⟨37205903002874647837291129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49607870670499530449721505 37205903002874647837291129)
    ·
      refine ⟨27904427252155985877968347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37205903002874647837291129 27904427252155985877968347)
      ·
        refine ⟨41856640878233978816952521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27904427252155985877968347 41856640878233978816952521)
        ·
          refine ⟨31392480658675484112714391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41856640878233978816952521 31392480658675484112714391)
          ·
            refine ⟨47088720988013226169071587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31392480658675484112714391 47088720988013226169071587)
            ·
              refine ⟨70633081482019839253607381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47088720988013226169071587 70633081482019839253607381)
              ·
                refine ⟨1655462847234839982506423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70633081482019839253607381 1655462847234839982506423)
                ·
                  refine ⟨2483194270852259973759635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655462847234839982506423 2483194270852259973759635)
                  ·
                    refine ⟨3724791406278389960639453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2483194270852259973759635 3724791406278389960639453)
                    ·
                      refine ⟨1396796777354396235239795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3724791406278389960639453 1396796777354396235239795)
                      ·
                        rfl

theorem cell23_2720252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_2720252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720252 prefixEnd_2720252 := by exact prefixLift 2720252
  have htrace : WordTrace (prefixWord ++ tailWord_2720252) baseStart_2720252 baseEnd_2720252 := by
    simpa [prefixWord, tailWord_2720252, baseEnd_2720252] using wordTrace_append hprefix tailTrace_2720252
  have hstable : (prefixWord ++ tailWord_2720252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720252).length < 2 ^ (prefixWord ++ tailWord_2720252).sum := by decide
  have hdescent : baseEnd_2720252 < baseStart_2720252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720255 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 1, 5]
def baseStart_2720255 : Nat := 118140960795 + 2720255 * 2 ^ 59
def prefixEnd_2720255 : Nat := 4983230072969 + 3 ^ 40 * 2720255 * 2
def baseEnd_2720255 : Nat := 465599439265453241167427

theorem tailTrace_2720255 : CollatzResearch.WordTrace tailWord_2720255 prefixEnd_2720255 465599439265453241167427 := by
  unfold tailWord_2720255
  simp only [CollatzResearch.WordTrace]
  refine ⟨99215850759988192411802219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66143900506658794941201479 99215850759988192411802219)
  ·
    refine ⟨148823776139982288617703329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99215850759988192411802219 148823776139982288617703329)
    ·
      refine ⟨111617832104986716463277497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148823776139982288617703329 111617832104986716463277497)
      ·
        refine ⟨83713374078740037347458123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111617832104986716463277497 83713374078740037347458123)
        ·
          refine ⟨125570061118110056021187185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83713374078740037347458123 125570061118110056021187185)
          ·
            refine ⟨94177545838582542015890389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125570061118110056021187185 94177545838582542015890389)
            ·
              refine ⟨2207286230591778328497431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94177545838582542015890389 2207286230591778328497431)
              ·
                refine ⟨3310929345887667492746147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207286230591778328497431 3310929345887667492746147)
                ·
                  refine ⟨4966394018831501239119221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310929345887667492746147 4966394018831501239119221)
                  ·
                    refine ⟨465599439265453241167427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4966394018831501239119221 465599439265453241167427)
                    ·
                      rfl

theorem cell23_2720255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 5].length) (baseStart_2720255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720255 prefixEnd_2720255 := by exact prefixLift 2720255
  have htrace : WordTrace (prefixWord ++ tailWord_2720255) baseStart_2720255 baseEnd_2720255 := by
    simpa [prefixWord, tailWord_2720255, baseEnd_2720255] using wordTrace_append hprefix tailTrace_2720255
  have hstable : (prefixWord ++ tailWord_2720255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720255).length < 2 ^ (prefixWord ++ tailWord_2720255).sum := by decide
  have hdescent : baseEnd_2720255 < baseStart_2720255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720285 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2720285 : Nat := 118140960795 + 2720285 * 2 ^ 59
def prefixEnd_2720285 : Nat := 4983230072969 + 3 ^ 40 * 2720285 * 2
def baseEnd_2720285 : Nat := 465604574071998202042381

theorem tailTrace_2720285 : CollatzResearch.WordTrace tailWord_2720285 prefixEnd_2720285 465604574071998202042381 := by
  unfold tailWord_2720285
  simp only [CollatzResearch.WordTrace]
  refine ⟨99216944949879507535394309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66144629966586338356929539 99216944949879507535394309)
  ·
    refine ⟨18603177178102407662886433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99216944949879507535394309 18603177178102407662886433)
    ·
      refine ⟨13952382883576805747164825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18603177178102407662886433 13952382883576805747164825)
      ·
        refine ⟨10464287162682604310373619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13952382883576805747164825 10464287162682604310373619)
        ·
          refine ⟨15696430744023906465560429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10464287162682604310373619 15696430744023906465560429)
          ·
            refine ⟨5886161529008964924585161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15696430744023906465560429 5886161529008964924585161)
            ·
              refine ⟨4414621146756723693438871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5886161529008964924585161 4414621146756723693438871)
              ·
                refine ⟨6621931720135085540158307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414621146756723693438871 6621931720135085540158307)
                ·
                  refine ⟨9932897580202628310237461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6621931720135085540158307 9932897580202628310237461)
                  ·
                    refine ⟨465604574071998202042381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9932897580202628310237461 465604574071998202042381)
                    ·
                      rfl

theorem cell23_2720285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2720285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720285 prefixEnd_2720285 := by exact prefixLift 2720285
  have htrace : WordTrace (prefixWord ++ tailWord_2720285) baseStart_2720285 baseEnd_2720285 := by
    simpa [prefixWord, tailWord_2720285, baseEnd_2720285] using wordTrace_append hprefix tailTrace_2720285
  have hstable : (prefixWord ++ tailWord_2720285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720285).length < 2 ^ (prefixWord ++ tailWord_2720285).sum := by decide
  have hdescent : baseEnd_2720285 < baseStart_2720285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720326 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_2720326 : Nat := 118140960795 + 2720326 * 2 ^ 59
def prefixEnd_2720326 : Nat := 4983230072969 + 3 ^ 40 * 2720326 * 2
def baseEnd_2720326 : Nat := 1396834774922828945714455

theorem tailTrace_2720326 : CollatzResearch.WordTrace tailWord_2720326 prefixEnd_2720326 1396834774922828945714455 := by
  unfold tailWord_2720326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100576260710342860551151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66145626895153981025091221 3100576260710342860551151)
  ·
    refine ⟨4650864391065514290826727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3100576260710342860551151 4650864391065514290826727)
    ·
      refine ⟨6976296586598271436240091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4650864391065514290826727 6976296586598271436240091)
      ·
        refine ⟨10464444879897407154360137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6976296586598271436240091 10464444879897407154360137)
        ·
          refine ⟨7848333659923055365770103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10464444879897407154360137 7848333659923055365770103)
          ·
            refine ⟨11772500489884583048655155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7848333659923055365770103 11772500489884583048655155)
            ·
              refine ⟨17658750734826874572982733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11772500489884583048655155 17658750734826874572982733)
              ·
                refine ⟨6622031525560077964868525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17658750734826874572982733 6622031525560077964868525)
                ·
                  refine ⟨2483261822085029236825697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6622031525560077964868525 2483261822085029236825697)
                  ·
                    refine ⟨1862446366563771927619273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2483261822085029236825697 1862446366563771927619273)
                    ·
                      refine ⟨1396834774922828945714455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862446366563771927619273 1396834774922828945714455)
                      ·
                        rfl

theorem cell23_2720326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_2720326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720326 prefixEnd_2720326 := by exact prefixLift 2720326
  have htrace : WordTrace (prefixWord ++ tailWord_2720326) baseStart_2720326 baseEnd_2720326 := by
    simpa [prefixWord, tailWord_2720326, baseEnd_2720326] using wordTrace_append hprefix tailTrace_2720326
  have hstable : (prefixWord ++ tailWord_2720326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720326).length < 2 ^ (prefixWord ++ tailWord_2720326).sum := by decide
  have hdescent : baseEnd_2720326 < baseStart_2720326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720335 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 5, 3, 2]
def baseStart_2720335 : Nat := 118140960795 + 2720335 * 2 ^ 59
def prefixEnd_2720335 : Nat := 4983230072969 + 3 ^ 40 * 2720335 * 2
def baseEnd_2720335 : Nat := 1396839396248719410501913

theorem tailTrace_2720335 : CollatzResearch.WordTrace tailWord_2720335 prefixEnd_2720335 1396839396248719410501913 := by
  unfold tailWord_2720335
  simp only [CollatzResearch.WordTrace]
  refine ⟨99218768599698366074714459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66145845733132244049809639 99218768599698366074714459)
  ·
    refine ⟨148828152899547549112071689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99218768599698366074714459 148828152899547549112071689)
    ·
      refine ⟨111621114674660661834053767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148828152899547549112071689 111621114674660661834053767)
      ·
        refine ⟨167431672011990992751080651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111621114674660661834053767 167431672011990992751080651)
        ·
          refine ⟨251147508017986489126620977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167431672011990992751080651 251147508017986489126620977)
          ·
            refine ⟨188360631013489866844965733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251147508017986489126620977 188360631013489866844965733)
            ·
              refine ⟨35317618315029350033431075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188360631013489866844965733 35317618315029350033431075)
              ·
                refine ⟨52976427472544025050146613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35317618315029350033431075 52976427472544025050146613)
                ·
                  refine ⟨4966540075551002348451245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52976427472544025050146613 4966540075551002348451245)
                  ·
                    refine ⟨1862452528331625880669217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4966540075551002348451245 1862452528331625880669217)
                    ·
                      refine ⟨1396839396248719410501913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862452528331625880669217 1396839396248719410501913)
                      ·
                        rfl

theorem cell23_2720335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 3, 2].length) (baseStart_2720335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720335 prefixEnd_2720335 := by exact prefixLift 2720335
  have htrace : WordTrace (prefixWord ++ tailWord_2720335) baseStart_2720335 baseEnd_2720335 := by
    simpa [prefixWord, tailWord_2720335, baseEnd_2720335] using wordTrace_append hprefix tailTrace_2720335
  have hstable : (prefixWord ++ tailWord_2720335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720335).length < 2 ^ (prefixWord ++ tailWord_2720335).sum := by decide
  have hdescent : baseEnd_2720335 < baseStart_2720335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720352 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 1, 3, 2]
def baseStart_2720352 : Nat := 118140960795 + 2720352 * 2 ^ 59
def prefixEnd_2720352 : Nat := 4983230072969 + 3 ^ 40 * 2720352 * 2
def baseEnd_2720352 : Nat := 1396848125419845843989335

theorem tailTrace_2720352 : CollatzResearch.WordTrace tailWord_2720352 prefixEnd_2720352 1396848125419845843989335 := by
  unfold tailWord_2720352
  simp only [CollatzResearch.WordTrace]
  refine ⟨49609694320318388989041655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66146259093757851985388873 49609694320318388989041655)
  ·
    refine ⟨74414541480477583483562483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49609694320318388989041655 74414541480477583483562483)
    ·
      refine ⟨111621812220716375225343725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74414541480477583483562483 111621812220716375225343725)
      ·
        refine ⟨41858179582768640709503897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111621812220716375225343725 41858179582768640709503897)
        ·
          refine ⟨31393634687076480532127923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41858179582768640709503897 31393634687076480532127923)
          ·
            refine ⟨47090452030614720798191885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31393634687076480532127923 47090452030614720798191885)
            ·
              refine ⟨17658919511480520299321957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47090452030614720798191885 17658919511480520299321957)
              ·
                refine ⟨3311047408402597556122867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17658919511480520299321957 3311047408402597556122867)
                ·
                  refine ⟨4966571112603896334184301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311047408402597556122867 4966571112603896334184301)
                  ·
                    refine ⟨1862464167226461125319113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4966571112603896334184301 1862464167226461125319113)
                    ·
                      refine ⟨1396848125419845843989335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862464167226461125319113 1396848125419845843989335)
                      ·
                        rfl

theorem cell23_2720352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_2720352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720352 prefixEnd_2720352 := by exact prefixLift 2720352
  have htrace : WordTrace (prefixWord ++ tailWord_2720352) baseStart_2720352 baseEnd_2720352 := by
    simpa [prefixWord, tailWord_2720352, baseEnd_2720352] using wordTrace_append hprefix tailTrace_2720352
  have hstable : (prefixWord ++ tailWord_2720352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720352).length < 2 ^ (prefixWord ++ tailWord_2720352).sum := by decide
  have hdescent : baseEnd_2720352 < baseStart_2720352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720360 : List Nat := [2, 1, 4, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2720360 : Nat := 118140960795 + 2720360 * 2 ^ 59
def prefixEnd_2720360 : Nat := 4983230072969 + 3 ^ 40 * 2720360 * 2
def baseEnd_2720360 : Nat := 1396852233265081812689299

theorem tailTrace_2720360 : CollatzResearch.WordTrace tailWord_2720360 prefixEnd_2720360 1396852233265081812689299 := by
  unfold tailWord_2720360
  simp only [CollatzResearch.WordTrace]
  refine ⟨49609840212303897672187267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66146453616405196896249689 49609840212303897672187267)
  ·
    refine ⟨74414760318455846508280901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49609840212303897672187267 74414760318455846508280901)
    ·
      refine ⟨13952767559710471220302669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74414760318455846508280901 13952767559710471220302669)
      ·
        refine ⟨5232287834891426707613501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13952767559710471220302669 5232287834891426707613501)
        ·
          refine ⟨1962107938084285015355063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5232287834891426707613501 1962107938084285015355063)
          ·
            refine ⟨2943161907126427523032595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962107938084285015355063 2943161907126427523032595)
            ·
              refine ⟨4414742860689641284548893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943161907126427523032595 4414742860689641284548893)
              ·
                refine ⟨1655528572758615481705835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4414742860689641284548893 1655528572758615481705835)
                ·
                  refine ⟨2483292859137923222558753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655528572758615481705835 2483292859137923222558753)
                  ·
                    refine ⟨1862469644353442416919065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2483292859137923222558753 1862469644353442416919065)
                    ·
                      refine ⟨1396852233265081812689299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862469644353442416919065 1396852233265081812689299)
                      ·
                        rfl

theorem cell23_2720360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2720360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720360 prefixEnd_2720360 := by exact prefixLift 2720360
  have htrace : WordTrace (prefixWord ++ tailWord_2720360) baseStart_2720360 baseEnd_2720360 := by
    simpa [prefixWord, tailWord_2720360, baseEnd_2720360] using wordTrace_append hprefix tailTrace_2720360
  have hstable : (prefixWord ++ tailWord_2720360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720360).length < 2 ^ (prefixWord ++ tailWord_2720360).sum := by decide
  have hdescent : baseEnd_2720360 < baseStart_2720360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720385 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2720385 : Nat := 118140960795 + 2720385 * 2 ^ 59
def prefixEnd_2720385 : Nat := 4983230072969 + 3 ^ 40 * 2720385 * 2
def baseEnd_2720385 : Nat := 1396865070281444214876683

theorem tailTrace_2720385 : CollatzResearch.WordTrace tailWord_2720385 prefixEnd_2720385 1396865070281444214876683 := by
  unfold tailWord_2720385
  simp only [CollatzResearch.WordTrace]
  refine ⟨99220592249517224614034609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66147061499678149742689739 99220592249517224614034609)
  ·
    refine ⟨74415444187137918460525957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99220592249517224614034609 74415444187137918460525957)
    ·
      refine ⟨13952895785088359711348617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74415444187137918460525957 13952895785088359711348617)
      ·
        refine ⟨10464671838816269783511463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13952895785088359711348617 10464671838816269783511463)
        ·
          refine ⟨15697007758224404675267195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10464671838816269783511463 15697007758224404675267195)
          ·
            refine ⟨23545511637336607012900793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15697007758224404675267195 23545511637336607012900793)
            ·
              refine ⟨17659133728002455259675595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23545511637336607012900793 17659133728002455259675595)
              ·
                refine ⟨26488700592003682889513393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17659133728002455259675595 26488700592003682889513393)
                ·
                  refine ⟨19866525444002762167135045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26488700592003682889513393 19866525444002762167135045)
                  ·
                    refine ⟨3724973520750517906337821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19866525444002762167135045 3724973520750517906337821)
                    ·
                      refine ⟨1396865070281444214876683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3724973520750517906337821 1396865070281444214876683)
                      ·
                        rfl

theorem cell23_2720385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2720385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720385 prefixEnd_2720385 := by exact prefixLift 2720385
  have htrace : WordTrace (prefixWord ++ tailWord_2720385) baseStart_2720385 baseEnd_2720385 := by
    simpa [prefixWord, tailWord_2720385, baseEnd_2720385] using wordTrace_append hprefix tailTrace_2720385
  have hstable : (prefixWord ++ tailWord_2720385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720385).length < 2 ^ (prefixWord ++ tailWord_2720385).sum := by decide
  have hdescent : baseEnd_2720385 < baseStart_2720385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720425 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 1, 7, 2]
def baseStart_2720425 : Nat := 118140960795 + 2720425 * 2 ^ 59
def prefixEnd_2720425 : Nat := 4983230072969 + 3 ^ 40 * 2720425 * 2
def baseEnd_2720425 : Nat := 1396885609507624058376499

theorem tailTrace_2720425 : CollatzResearch.WordTrace tailWord_2720425 prefixEnd_2720425 1396885609507624058376499 := by
  unfold tailWord_2720425
  simp only [CollatzResearch.WordTrace]
  refine ⟨99222051169372311445490729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66148034112914874296993819 99222051169372311445490729)
  ·
    refine ⟨74416538377029233584118047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99222051169372311445490729 74416538377029233584118047)
    ·
      refine ⟨111624807565543850376177071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74416538377029233584118047 111624807565543850376177071)
      ·
        refine ⟨167437211348315775564265607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111624807565543850376177071 167437211348315775564265607)
        ·
          refine ⟨251155817022473663346398411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167437211348315775564265607 251155817022473663346398411)
          ·
            refine ⟨376733725533710495019597617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251155817022473663346398411 376733725533710495019597617)
            ·
              refine ⟨282550294150282871264698213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376733725533710495019597617 282550294150282871264698213)
              ·
                refine ⟨52978180153178038362130915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282550294150282871264698213 52978180153178038362130915)
                ·
                  refine ⟨79467270229767057543196373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52978180153178038362130915 79467270229767057543196373)
                  ·
                    refine ⟨1862514146010165411168665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 79467270229767057543196373 1862514146010165411168665)
                    ·
                      refine ⟨1396885609507624058376499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862514146010165411168665 1396885609507624058376499)
                      ·
                        rfl

theorem cell23_2720425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 7, 2].length) (baseStart_2720425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720425 prefixEnd_2720425 := by exact prefixLift 2720425
  have htrace : WordTrace (prefixWord ++ tailWord_2720425) baseStart_2720425 baseEnd_2720425 := by
    simpa [prefixWord, tailWord_2720425, baseEnd_2720425] using wordTrace_append hprefix tailTrace_2720425
  have hstable : (prefixWord ++ tailWord_2720425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720425).length < 2 ^ (prefixWord ++ tailWord_2720425).sum := by decide
  have hdescent : baseEnd_2720425 < baseStart_2720425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720433 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2720433 : Nat := 118140960795 + 2720433 * 2 ^ 59
def prefixEnd_2720433 : Nat := 4983230072969 + 3 ^ 40 * 2720433 * 2
def baseEnd_2720433 : Nat := 1396889717352860027076463

theorem tailTrace_2720433 : CollatzResearch.WordTrace tailWord_2720433 prefixEnd_2720433 1396889717352860027076463 := by
  unfold tailWord_2720433
  simp only [CollatzResearch.WordTrace]
  refine ⟨99222342953343328811781953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66148228635562219207854635 99222342953343328811781953)
  ·
    refine ⟨74416757215007496608836465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99222342953343328811781953 74416757215007496608836465)
    ·
      refine ⟨55812567911255622456627349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74416757215007496608836465 55812567911255622456627349)
      ·
        refine ⟨2616214120840107302654407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55812567911255622456627349 2616214120840107302654407)
        ·
          refine ⟨3924321181260160953981611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2616214120840107302654407 3924321181260160953981611)
          ·
            refine ⟨5886481771890241430972417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3924321181260160953981611 5886481771890241430972417)
            ·
              refine ⟨4414861328917681073229313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5886481771890241430972417 4414861328917681073229313)
              ·
                refine ⟨3311145996688260804921985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4414861328917681073229313 3311145996688260804921985)
                ·
                  refine ⟨2483359497516195603691489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3311145996688260804921985 2483359497516195603691489)
                  ·
                    refine ⟨1862519623137146702768617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2483359497516195603691489 1862519623137146702768617)
                    ·
                      refine ⟨1396889717352860027076463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862519623137146702768617 1396889717352860027076463)
                      ·
                        rfl

theorem cell23_2720433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2720433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720433 prefixEnd_2720433 := by exact prefixLift 2720433
  have htrace : WordTrace (prefixWord ++ tailWord_2720433) baseStart_2720433 baseEnd_2720433 := by
    simpa [prefixWord, tailWord_2720433, baseEnd_2720433] using wordTrace_append hprefix tailTrace_2720433
  have hstable : (prefixWord ++ tailWord_2720433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720433).length < 2 ^ (prefixWord ++ tailWord_2720433).sum := by decide
  have hdescent : baseEnd_2720433 < baseStart_2720433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720435 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 2, 5]
def baseStart_2720435 : Nat := 118140960795 + 2720435 * 2 ^ 59
def prefixEnd_2720435 : Nat := 4983230072969 + 3 ^ 40 * 2720435 * 2
def baseEnd_2720435 : Nat := 465630248104723006417151

theorem tailTrace_2720435 : CollatzResearch.WordTrace tailWord_2720435 prefixEnd_2720435 465630248104723006417151 := by
  unfold tailWord_2720435
  simp only [CollatzResearch.WordTrace]
  refine ⟨99222415899336083153354759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66148277266224055435569839 99222415899336083153354759)
  ·
    refine ⟨148833623849004124730032139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99222415899336083153354759 148833623849004124730032139)
    ·
      refine ⟨223250435773506187095048209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148833623849004124730032139 223250435773506187095048209)
      ·
        refine ⟨167437826830129640321286157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223250435773506187095048209 167437826830129640321286157)
        ·
          refine ⟨62789185061298615120482309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167437826830129640321286157 62789185061298615120482309)
          ·
            refine ⟨11772972198993490335090433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62789185061298615120482309 11772972198993490335090433)
            ·
              refine ⟨8829729149245117751317825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11772972198993490335090433 8829729149245117751317825)
              ·
                refine ⟨6622296861933838313488369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8829729149245117751317825 6622296861933838313488369)
                ·
                  refine ⟨4966722646450378735116277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6622296861933838313488369 4966722646450378735116277)
                  ·
                    refine ⟨465630248104723006417151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4966722646450378735116277 465630248104723006417151)
                    ·
                      rfl

theorem cell23_2720435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 5].length) (baseStart_2720435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720435 prefixEnd_2720435 := by exact prefixLift 2720435
  have htrace : WordTrace (prefixWord ++ tailWord_2720435) baseStart_2720435 baseEnd_2720435 := by
    simpa [prefixWord, tailWord_2720435, baseEnd_2720435] using wordTrace_append hprefix tailTrace_2720435
  have hstable : (prefixWord ++ tailWord_2720435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720435).length < 2 ^ (prefixWord ++ tailWord_2720435).sum := by decide
  have hdescent : baseEnd_2720435 < baseStart_2720435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720445 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2720445 : Nat := 118140960795 + 2720445 * 2 ^ 59
def prefixEnd_2720445 : Nat := 4983230072969 + 3 ^ 40 * 2720445 * 2
def baseEnd_2720445 : Nat := 1396895879120713980126407

theorem tailTrace_2720445 : CollatzResearch.WordTrace tailWord_2720445 prefixEnd_2720445 1396895879120713980126407 := by
  unfold tailWord_2720445
  simp only [CollatzResearch.WordTrace]
  refine ⟨99222780629299854861218789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66148520419533236574145859 99222780629299854861218789)
  ·
    refine ⟨18604271367993722786478523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99222780629299854861218789 18604271367993722786478523)
    ·
      refine ⟨27906407051990584179717785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18604271367993722786478523 27906407051990584179717785)
      ·
        refine ⟨20929805288992938134788339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27906407051990584179717785 20929805288992938134788339)
        ·
          refine ⟨31394707933489407202182509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20929805288992938134788339 31394707933489407202182509)
          ·
            refine ⟨11773015475058527700818441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31394707933489407202182509 11773015475058527700818441)
            ·
              refine ⟨8829761606293895775613831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11773015475058527700818441 8829761606293895775613831)
              ·
                refine ⟨13244642409440843663420747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8829761606293895775613831 13244642409440843663420747)
                ·
                  refine ⟨19866963614161265495131121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13244642409440843663420747 19866963614161265495131121)
                  ·
                    refine ⟨14900222710620949121348341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19866963614161265495131121 14900222710620949121348341)
                    ·
                      refine ⟨1396895879120713980126407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14900222710620949121348341 1396895879120713980126407)
                      ·
                        rfl

theorem cell23_2720445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2720445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720445 prefixEnd_2720445 := by exact prefixLift 2720445
  have htrace : WordTrace (prefixWord ++ tailWord_2720445) baseStart_2720445 baseEnd_2720445 := by
    simpa [prefixWord, tailWord_2720445, baseEnd_2720445] using wordTrace_append hprefix tailTrace_2720445
  have hstable : (prefixWord ++ tailWord_2720445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720445).length < 2 ^ (prefixWord ++ tailWord_2720445).sum := by decide
  have hdescent : baseEnd_2720445 < baseStart_2720445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720472 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 2, 1, 4]
def baseStart_2720472 : Nat := 118140960795 + 2720472 * 2 ^ 59
def prefixEnd_2720472 : Nat := 4983230072969 + 3 ^ 40 * 2720472 * 2
def baseEnd_2720472 : Nat := 1396909743098385374488783

theorem tailTrace_2720472 : CollatzResearch.WordTrace tailWord_2720472 prefixEnd_2720472 1396909743098385374488783 := by
  unfold tailWord_2720472
  simp only [CollatzResearch.WordTrace]
  refine ⟨49611882700101019236225835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66149176933468025648301113 49611882700101019236225835)
  ·
    refine ⟨74417824050151528854338753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49611882700101019236225835 74417824050151528854338753)
    ·
      refine ⟨55813368037613646640754065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74417824050151528854338753 55813368037613646640754065)
      ·
        refine ⟨41860026028210234980565549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55813368037613646640754065 41860026028210234980565549)
        ·
          refine ⟨15697509760578838117712081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41860026028210234980565549 15697509760578838117712081)
          ·
            refine ⟨11773132320434128588284061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15697509760578838117712081 11773132320434128588284061)
            ·
              refine ⟨4414924620162798220606523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11773132320434128588284061 4414924620162798220606523)
              ·
                refine ⟨6622386930244197330909785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414924620162798220606523 6622386930244197330909785)
                ·
                  refine ⟨4966790197683147998182339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6622386930244197330909785 4966790197683147998182339)
                  ·
                    refine ⟨7450185296524721997273509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4966790197683147998182339 7450185296524721997273509)
                    ·
                      refine ⟨1396909743098385374488783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7450185296524721997273509 1396909743098385374488783)
                      ·
                        rfl

theorem cell23_2720472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_2720472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720472 prefixEnd_2720472 := by exact prefixLift 2720472
  have htrace : WordTrace (prefixWord ++ tailWord_2720472) baseStart_2720472 baseEnd_2720472 := by
    simpa [prefixWord, tailWord_2720472, baseEnd_2720472] using wordTrace_append hprefix tailTrace_2720472
  have hstable : (prefixWord ++ tailWord_2720472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720472).length < 2 ^ (prefixWord ++ tailWord_2720472).sum := by decide
  have hdescent : baseEnd_2720472 < baseStart_2720472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720475 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 3]
def baseStart_2720475 : Nat := 118140960795 + 2720475 * 2 ^ 59
def prefixEnd_2720475 : Nat := 4983230072969 + 3 ^ 40 * 2720475 * 2
def baseEnd_2720475 : Nat := 1396911283540348862751269

theorem tailTrace_2720475 : CollatzResearch.WordTrace tailWord_2720475 prefixEnd_2720475 1396911283540348862751269 := by
  unfold tailWord_2720475
  simp only [CollatzResearch.WordTrace]
  refine ⟨99223874819191169984810879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66149249879460779989873919 99223874819191169984810879)
  ·
    refine ⟨148835812228786754977216319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99223874819191169984810879 148835812228786754977216319)
    ·
      refine ⟨223253718343180132465824479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148835812228786754977216319 223253718343180132465824479)
      ·
        refine ⟨334880577514770198698736719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223253718343180132465824479 334880577514770198698736719)
        ·
          refine ⟨502320866272155298048105079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334880577514770198698736719 502320866272155298048105079)
          ·
            refine ⟨753481299408232947072157619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502320866272155298048105079 753481299408232947072157619)
            ·
              refine ⟨1130221949112349420608236429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753481299408232947072157619 1130221949112349420608236429)
              ·
                refine ⟨423833230917131032728088661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130221949112349420608236429 423833230917131032728088661)
                ·
                  refine ⟨4966795674810129289782289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 423833230917131032728088661 4966795674810129289782289)
                  ·
                    refine ⟨3725096756107596967336717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4966795674810129289782289 3725096756107596967336717)
                    ·
                      refine ⟨1396911283540348862751269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3725096756107596967336717 1396911283540348862751269)
                      ·
                        rfl

theorem cell23_2720475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 3].length) (baseStart_2720475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720475 prefixEnd_2720475 := by exact prefixLift 2720475
  have htrace : WordTrace (prefixWord ++ tailWord_2720475) baseStart_2720475 baseEnd_2720475 := by
    simpa [prefixWord, tailWord_2720475, baseEnd_2720475] using wordTrace_append hprefix tailTrace_2720475
  have hstable : (prefixWord ++ tailWord_2720475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720475).length < 2 ^ (prefixWord ++ tailWord_2720475).sum := by decide
  have hdescent : baseEnd_2720475 < baseStart_2720475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720485 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2720485 : Nat := 118140960795 + 2720485 * 2 ^ 59
def prefixEnd_2720485 : Nat := 4983230072969 + 3 ^ 40 * 2720485 * 2
def baseEnd_2720485 : Nat := 1396916418346893823626223

theorem tailTrace_2720485 : CollatzResearch.WordTrace tailWord_2720485 prefixEnd_2720485 1396916418346893823626223 := by
  unfold tailWord_2720485
  simp only [CollatzResearch.WordTrace]
  refine ⟨99224239549154941692674909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66149493032769961128449939 99224239549154941692674909)
  ·
    refine ⟨37209089830933103134753091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99224239549154941692674909 37209089830933103134753091)
    ·
      refine ⟨55813634746399654702129637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37209089830933103134753091 55813634746399654702129637)
      ·
        refine ⟨10465056514949935256649307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55813634746399654702129637 10465056514949935256649307)
        ·
          refine ⟨15697584772424902884973961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10465056514949935256649307 15697584772424902884973961)
          ·
            refine ⟨11773188579318677163730471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15697584772424902884973961 11773188579318677163730471)
            ·
              refine ⟨17659782868978015745595707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11773188579318677163730471 17659782868978015745595707)
              ·
                refine ⟨26489674303467023618393561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17659782868978015745595707 26489674303467023618393561)
                ·
                  refine ⟨19867255727600267713795171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26489674303467023618393561 19867255727600267713795171)
                  ·
                    refine ⟨29800883591400401570692757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19867255727600267713795171 29800883591400401570692757)
                    ·
                      refine ⟨1396916418346893823626223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29800883591400401570692757 1396916418346893823626223)
                      ·
                        rfl

theorem cell23_2720485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2720485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720485 prefixEnd_2720485 := by exact prefixLift 2720485
  have htrace : WordTrace (prefixWord ++ tailWord_2720485) baseStart_2720485 baseEnd_2720485 := by
    simpa [prefixWord, tailWord_2720485, baseEnd_2720485] using wordTrace_append hprefix tailTrace_2720485
  have hstable : (prefixWord ++ tailWord_2720485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720485).length < 2 ^ (prefixWord ++ tailWord_2720485).sum := by decide
  have hdescent : baseEnd_2720485 < baseStart_2720485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720495 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 8]
def baseStart_2720495 : Nat := 118140960795 + 2720495 * 2 ^ 59
def prefixEnd_2720495 : Nat := 4983230072969 + 3 ^ 40 * 2720495 * 2
def baseEnd_2720495 : Nat := 155213505905937642722353

theorem tailTrace_2720495 : CollatzResearch.WordTrace tailWord_2720495 prefixEnd_2720495 155213505905937642722353 := by
  unfold tailWord_2720495
  simp only [CollatzResearch.WordTrace]
  refine ⟨99224604279118713400538939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66149736186079142267025959 99224604279118713400538939)
  ·
    refine ⟨148836906418678070100808409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99224604279118713400538939 148836906418678070100808409)
    ·
      refine ⟨111627679814008552575606307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148836906418678070100808409 111627679814008552575606307)
      ·
        refine ⟨167441519721012828863409461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111627679814008552575606307 167441519721012828863409461)
        ·
          refine ⟨15697642473844952705944637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167441519721012828863409461 15697642473844952705944637)
          ·
            refine ⟨5886615927691857264729239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15697642473844952705944637 5886615927691857264729239)
            ·
              refine ⟨8829923891537785897093859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5886615927691857264729239 8829923891537785897093859)
              ·
                refine ⟨13244885837306678845640789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8829923891537785897093859 13244885837306678845640789)
                ·
                  refine ⟨155213505905937642722353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13244885837306678845640789 155213505905937642722353)
                  ·
                    rfl

theorem cell23_2720495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 8].length) (baseStart_2720495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720495 prefixEnd_2720495 := by exact prefixLift 2720495
  have htrace : WordTrace (prefixWord ++ tailWord_2720495) baseStart_2720495 baseEnd_2720495 := by
    simpa [prefixWord, tailWord_2720495, baseEnd_2720495] using wordTrace_append hprefix tailTrace_2720495
  have hstable : (prefixWord ++ tailWord_2720495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720495).length < 2 ^ (prefixWord ++ tailWord_2720495).sum := by decide
  have hdescent : baseEnd_2720495 < baseStart_2720495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720549 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 2, 3, 2]
def baseStart_2720549 : Nat := 118140960795 + 2720549 * 2 ^ 59
def prefixEnd_2720549 : Nat := 4983230072969 + 3 ^ 40 * 2720549 * 2
def baseEnd_2720549 : Nat := 1396949281108781573225929

theorem tailTrace_2720549 : CollatzResearch.WordTrace tailWord_2720549 prefixEnd_2720549 1396949281108781573225929 := by
  unfold tailWord_2720549
  simp only [CollatzResearch.WordTrace]
  refine ⟨99226573820923080623004701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66151049213948720415336467 99226573820923080623004701)
  ·
    refine ⟨37209965182846155233626763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99226573820923080623004701 37209965182846155233626763)
    ·
      refine ⟨55814947774269232850440145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37209965182846155233626763 55814947774269232850440145)
      ·
        refine ⟨41861210830701924637830109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55814947774269232850440145 41861210830701924637830109)
        ·
          refine ⟨15697954061513221739186291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41861210830701924637830109 15697954061513221739186291)
          ·
            refine ⟨23546931092269832608779437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15697954061513221739186291 23546931092269832608779437)
            ·
              refine ⟨8830099159601187228292289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23546931092269832608779437 8830099159601187228292289)
              ·
                refine ⟨6622574369700890421219217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8830099159601187228292289 6622574369700890421219217)
                ·
                  refine ⟨4966930777275667815914413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6622574369700890421219217 4966930777275667815914413)
                  ·
                    refine ⟨1862599041478375430967905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4966930777275667815914413 1862599041478375430967905)
                    ·
                      refine ⟨1396949281108781573225929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862599041478375430967905 1396949281108781573225929)
                      ·
                        rfl

theorem cell23_2720549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_2720549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720549 prefixEnd_2720549 := by exact prefixLift 2720549
  have htrace : WordTrace (prefixWord ++ tailWord_2720549) baseStart_2720549 baseEnd_2720549 := by
    simpa [prefixWord, tailWord_2720549, baseEnd_2720549] using wordTrace_append hprefix tailTrace_2720549
  have hstable : (prefixWord ++ tailWord_2720549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720549).length < 2 ^ (prefixWord ++ tailWord_2720549).sum := by decide
  have hdescent : baseEnd_2720549 < baseStart_2720549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720562 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_2720562 : Nat := 118140960795 + 2720562 * 2 ^ 59
def prefixEnd_2720562 : Nat := 4983230072969 + 3 ^ 40 * 2720562 * 2
def baseEnd_2720562 : Nat := 1396955956357290022363369

theorem tailTrace_2720562 : CollatzResearch.WordTrace tailWord_2720562 prefixEnd_2720562 1396955956357290022363369 := by
  unfold tailWord_2720562
  simp only [CollatzResearch.WordTrace]
  refine ⟨24806761992468995960806985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66151365313250655895485293 24806761992468995960806985)
  ·
    refine ⟨18605071494351746970605239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24806761992468995960806985 18605071494351746970605239)
    ·
      refine ⟨27907607241527620455907859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18605071494351746970605239 27907607241527620455907859)
      ·
        refine ⟨41861410862291430683861789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27907607241527620455907859 41861410862291430683861789)
        ·
          refine ⟨15698029073359286506448171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41861410862291430683861789 15698029073359286506448171)
          ·
            refine ⟨23547043610038929759672257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15698029073359286506448171 23547043610038929759672257)
            ·
              refine ⟨17660282707529197319754193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23547043610038929759672257 17660282707529197319754193)
              ·
                refine ⟨13245212030646897989815645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17660282707529197319754193 13245212030646897989815645)
                ·
                  refine ⟨4966954511492586746180867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13245212030646897989815645 4966954511492586746180867)
                  ·
                    refine ⟨7450431767238880119271301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4966954511492586746180867 7450431767238880119271301)
                    ·
                      refine ⟨1396955956357290022363369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7450431767238880119271301 1396955956357290022363369)
                      ·
                        rfl

theorem cell23_2720562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_2720562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720562 prefixEnd_2720562 := by exact prefixLift 2720562
  have htrace : WordTrace (prefixWord ++ tailWord_2720562) baseStart_2720562 baseEnd_2720562 := by
    simpa [prefixWord, tailWord_2720562, baseEnd_2720562] using wordTrace_append hprefix tailTrace_2720562
  have hstable : (prefixWord ++ tailWord_2720562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720562).length < 2 ^ (prefixWord ++ tailWord_2720562).sum := by decide
  have hdescent : baseEnd_2720562 < baseStart_2720562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720579 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 5, 2, 2]
def baseStart_2720579 : Nat := 118140960795 + 2720579 * 2 ^ 59
def prefixEnd_2720579 : Nat := 4983230072969 + 3 ^ 40 * 2720579 * 2
def baseEnd_2720579 : Nat := 1396964685528416455850791

theorem tailTrace_2720579 : CollatzResearch.WordTrace tailWord_2720579 prefixEnd_2720579 1396964685528416455850791 := by
  unfold tailWord_2720579
  simp only [CollatzResearch.WordTrace]
  refine ⟨99227668010814395746596791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66151778673876263831064527 99227668010814395746596791)
  ·
    refine ⟨148841502016221593619895187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99227668010814395746596791 148841502016221593619895187)
    ·
      refine ⟨223262253024332390429842781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148841502016221593619895187 223262253024332390429842781)
      ·
        refine ⟨83723344884124646411191043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223262253024332390429842781 83723344884124646411191043)
        ·
          refine ⟨125585017326186969616786565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83723344884124646411191043 125585017326186969616786565)
          ·
            refine ⟨23547190748660056803147481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125585017326186969616786565 23547190748660056803147481)
            ·
              refine ⟨17660393061495042602360611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23547190748660056803147481 17660393061495042602360611)
              ·
                refine ⟨26490589592242563903540917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17660393061495042602360611 26490589592242563903540917)
                ·
                  refine ⟨2483492774272740365956961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26490589592242563903540917 2483492774272740365956961)
                  ·
                    refine ⟨1862619580704555274467721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2483492774272740365956961 1862619580704555274467721)
                    ·
                      refine ⟨1396964685528416455850791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862619580704555274467721 1396964685528416455850791)
                      ·
                        rfl

theorem cell23_2720579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_2720579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720579 prefixEnd_2720579 := by exact prefixLift 2720579
  have htrace : WordTrace (prefixWord ++ tailWord_2720579) baseStart_2720579 baseEnd_2720579 := by
    simpa [prefixWord, tailWord_2720579, baseEnd_2720579] using wordTrace_append hprefix tailTrace_2720579
  have hstable : (prefixWord ++ tailWord_2720579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720579).length < 2 ^ (prefixWord ++ tailWord_2720579).sum := by decide
  have hdescent : baseEnd_2720579 < baseStart_2720579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720585 : List Nat := [1, 2, 1, 1, 2, 5, 2, 9]
def baseStart_2720585 : Nat := 118140960795 + 2720585 * 2 ^ 59
def prefixEnd_2720585 : Nat := 4983230072969 + 3 ^ 40 * 2720585 * 2
def baseEnd_2720585 : Nat := 51739546904160867865769

theorem tailTrace_2720585 : CollatzResearch.WordTrace tailWord_2720585 prefixEnd_2720585 51739546904160867865769 := by
  unfold tailWord_2720585
  simp only [CollatzResearch.WordTrace]
  refine ⟨99227886848792658771315209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66151924565861772514210139 99227886848792658771315209)
  ·
    refine ⟨74420915136594494078486407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99227886848792658771315209 74420915136594494078486407)
    ·
      refine ⟨111631372704891741117729611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74420915136594494078486407 111631372704891741117729611)
      ·
        refine ⟨167447059057337611676594417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111631372704891741117729611 167447059057337611676594417)
        ·
          refine ⟨125585294293003208757445813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167447059057337611676594417 125585294293003208757445813)
          ·
            refine ⟨11773621339969050821010545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125585294293003208757445813 11773621339969050821010545)
            ·
              refine ⟨8830216004976788115757909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11773621339969050821010545 8830216004976788115757909)
              ·
                refine ⟨51739546904160867865769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8830216004976788115757909 51739546904160867865769)
                ·
                  rfl

theorem cell23_2720585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 9].length) (baseStart_2720585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720585 prefixEnd_2720585 := by exact prefixLift 2720585
  have htrace : WordTrace (prefixWord ++ tailWord_2720585) baseStart_2720585 baseEnd_2720585 := by
    simpa [prefixWord, tailWord_2720585, baseEnd_2720585] using wordTrace_append hprefix tailTrace_2720585
  have hstable : (prefixWord ++ tailWord_2720585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720585).length < 2 ^ (prefixWord ++ tailWord_2720585).sum := by decide
  have hdescent : baseEnd_2720585 < baseStart_2720585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720599 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 5]
def baseStart_2720599 : Nat := 118140960795 + 2720599 * 2 ^ 59
def prefixEnd_2720599 : Nat := 4983230072969 + 3 ^ 40 * 2720599 * 2
def baseEnd_2720599 : Nat := 1396974955141506377600699

theorem tailTrace_2720599 : CollatzResearch.WordTrace tailWord_2720599 prefixEnd_2720599 1396974955141506377600699 := by
  unfold tailWord_2720599
  simp only [CollatzResearch.WordTrace]
  refine ⟨99228397470741939162324851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66152264980494626108216567 99228397470741939162324851)
  ·
    refine ⟨148842596206112908743487277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99228397470741939162324851 148842596206112908743487277)
    ·
      refine ⟨55815973577292340778807729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148842596206112908743487277 55815973577292340778807729)
      ·
        refine ⟨41861980182969255584105797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55815973577292340778807729 41861980182969255584105797)
        ·
          refine ⟨7849121284306735422019837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41861980182969255584105797 7849121284306735422019837)
          ·
            refine ⟨2943420481615025783257439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7849121284306735422019837 2943420481615025783257439)
            ·
              refine ⟨4415130722422538674886159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943420481615025783257439 4415130722422538674886159)
              ·
                refine ⟨6622696083633808012329239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4415130722422538674886159 6622696083633808012329239)
                ·
                  refine ⟨9934044125450712018493859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6622696083633808012329239 9934044125450712018493859)
                  ·
                    refine ⟨14901066188176068027740789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9934044125450712018493859 14901066188176068027740789)
                    ·
                      refine ⟨1396974955141506377600699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14901066188176068027740789 1396974955141506377600699)
                      ·
                        rfl

theorem cell23_2720599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_2720599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720599 prefixEnd_2720599 := by exact prefixLift 2720599
  have htrace : WordTrace (prefixWord ++ tailWord_2720599) baseStart_2720599 baseEnd_2720599 := by
    simpa [prefixWord, tailWord_2720599, baseEnd_2720599] using wordTrace_append hprefix tailTrace_2720599
  have hstable : (prefixWord ++ tailWord_2720599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720599).length < 2 ^ (prefixWord ++ tailWord_2720599).sum := by decide
  have hdescent : baseEnd_2720599 < baseStart_2720599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720629 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2720629 : Nat := 118140960795 + 2720629 * 2 ^ 59
def prefixEnd_2720629 : Nat := 4983230072969 + 3 ^ 40 * 2720629 * 2
def baseEnd_2720629 : Nat := 1396990359561141260225561

theorem tailTrace_2720629 : CollatzResearch.WordTrace tailWord_2720629 prefixEnd_2720629 1396990359561141260225561 := by
  unfold tailWord_2720629
  simp only [CollatzResearch.WordTrace]
  refine ⟨99229491660633254285916941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66152994440422169523944627 99229491660633254285916941)
  ·
    refine ⟨37211059372737470357218853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99229491660633254285916941 37211059372737470357218853)
    ·
      refine ⟨6977073632388275691978535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37211059372737470357218853 6977073632388275691978535)
      ·
        refine ⟨10465610448582413537967803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6977073632388275691978535 10465610448582413537967803)
        ·
          refine ⟨15698415672873620306951705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10465610448582413537967803 15698415672873620306951705)
          ·
            refine ⟨11773811754655215230213779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15698415672873620306951705 11773811754655215230213779)
            ·
              refine ⟨17660717631982822845320669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11773811754655215230213779 17660717631982822845320669)
              ·
                refine ⟨6622769111993558566995251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17660717631982822845320669 6622769111993558566995251)
                ·
                  refine ⟨9934153667990337850492877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6622769111993558566995251 9934153667990337850492877)
                  ·
                    refine ⟨3725307625496376693934829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9934153667990337850492877 3725307625496376693934829)
                    ·
                      refine ⟨1396990359561141260225561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3725307625496376693934829 1396990359561141260225561)
                      ·
                        rfl

theorem cell23_2720629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2720629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720629 prefixEnd_2720629 := by exact prefixLift 2720629
  have htrace : WordTrace (prefixWord ++ tailWord_2720629) baseStart_2720629 baseEnd_2720629 := by
    simpa [prefixWord, tailWord_2720629, baseEnd_2720629] using wordTrace_append hprefix tailTrace_2720629
  have hstable : (prefixWord ++ tailWord_2720629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720629).length < 2 ^ (prefixWord ++ tailWord_2720629).sum := by decide
  have hdescent : baseEnd_2720629 < baseStart_2720629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720639 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 3, 3, 2]
def baseStart_2720639 : Nat := 118140960795 + 2720639 * 2 ^ 59
def prefixEnd_2720639 : Nat := 4983230072969 + 3 ^ 40 * 2720639 * 2
def baseEnd_2720639 : Nat := 1396995494367686221100515

theorem tailTrace_2720639 : CollatzResearch.WordTrace tailWord_2720639 prefixEnd_2720639 1396995494367686221100515 := by
  unfold tailWord_2720639
  simp only [CollatzResearch.WordTrace]
  refine ⟨99229856390597025993780971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66153237593731350662520647 99229856390597025993780971)
  ·
    refine ⟨148844784585895538990671457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99229856390597025993780971 148844784585895538990671457)
    ·
      refine ⟨111633588439421654243003593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148844784585895538990671457 111633588439421654243003593)
      ·
        refine ⟨83725191329566240682252695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111633588439421654243003593 83725191329566240682252695)
        ·
          refine ⟨125587786994349361023379043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83725191329566240682252695 125587786994349361023379043)
          ·
            refine ⟨188381680491524041535068565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125587786994349361023379043 188381680491524041535068565)
            ·
              refine ⟨8830391273040189446956339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 188381680491524041535068565 8830391273040189446956339)
              ·
                refine ⟨13245586909560284170434509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8830391273040189446956339 13245586909560284170434509)
                ·
                  refine ⟨4967095091085106563912941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13245586909560284170434509 4967095091085106563912941)
                  ·
                    refine ⟨1862660659156914961467353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4967095091085106563912941 1862660659156914961467353)
                    ·
                      refine ⟨1396995494367686221100515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862660659156914961467353 1396995494367686221100515)
                      ·
                        rfl

theorem cell23_2720639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_2720639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720639 prefixEnd_2720639 := by exact prefixLift 2720639
  have htrace : WordTrace (prefixWord ++ tailWord_2720639) baseStart_2720639 baseEnd_2720639 := by
    simpa [prefixWord, tailWord_2720639, baseEnd_2720639] using wordTrace_append hprefix tailTrace_2720639
  have hstable : (prefixWord ++ tailWord_2720639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720639).length < 2 ^ (prefixWord ++ tailWord_2720639).sum := by decide
  have hdescent : baseEnd_2720639 < baseStart_2720639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720672 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 3]
def baseStart_2720672 : Nat := 118140960795 + 2720672 * 2 ^ 59
def prefixEnd_2720672 : Nat := 4983230072969 + 3 ^ 40 * 2720672 * 2
def baseEnd_2720672 : Nat := 1397012439229284591987863

theorem tailTrace_2720672 : CollatzResearch.WordTrace tailWord_2720672 prefixEnd_2720672 1397012439229284591987863 := by
  unfold tailWord_2720672
  simp only [CollatzResearch.WordTrace]
  refine ⟨49615529999738736314866135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66154039999651648419821513 49615529999738736314866135)
  ·
    refine ⟨74423294999608104472299203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49615529999738736314866135 74423294999608104472299203)
    ·
      refine ⟨111634942499412156708448805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74423294999608104472299203 111634942499412156708448805)
      ·
        refine ⟨20931551718639779382834151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111634942499412156708448805 20931551718639779382834151)
        ·
          refine ⟨31397327577959669074251227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20931551718639779382834151 31397327577959669074251227)
          ·
            refine ⟨47095991366939503611376841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31397327577959669074251227 47095991366939503611376841)
            ·
              refine ⟨35321993525204627708532631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47095991366939503611376841 35321993525204627708532631)
              ·
                refine ⟨52982990287806941562798947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35321993525204627708532631 52982990287806941562798947)
                ·
                  refine ⟨79474485431710412344198421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52982990287806941562798947 79474485431710412344198421)
                  ·
                    refine ⟨3725366504611425578634301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79474485431710412344198421 3725366504611425578634301)
                    ·
                      refine ⟨1397012439229284591987863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3725366504611425578634301 1397012439229284591987863)
                      ·
                        rfl

theorem cell23_2720672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_2720672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720672 prefixEnd_2720672 := by exact prefixLift 2720672
  have htrace : WordTrace (prefixWord ++ tailWord_2720672) baseStart_2720672 baseEnd_2720672 := by
    simpa [prefixWord, tailWord_2720672, baseEnd_2720672] using wordTrace_append hprefix tailTrace_2720672
  have hstable : (prefixWord ++ tailWord_2720672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720672).length < 2 ^ (prefixWord ++ tailWord_2720672).sum := by decide
  have hdescent : baseEnd_2720672 < baseStart_2720672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720726 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_2720726 : Nat := 118140960795 + 2720726 * 2 ^ 59
def prefixEnd_2720726 : Nat := 4983230072969 + 3 ^ 40 * 2720726 * 2
def baseEnd_2720726 : Nat := 155226685242736375634735

theorem tailTrace_2720726 : CollatzResearch.WordTrace tailWord_2720726 prefixEnd_2720726 155226685242736375634735 := by
  unfold tailWord_2720726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6202064346330114990762377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66155353027521226568132021 6202064346330114990762377)
  ·
    refine ⟨4651548259747586243071783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6202064346330114990762377 4651548259747586243071783)
    ·
      refine ⟨6977322389621379364607675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4651548259747586243071783 6977322389621379364607675)
      ·
        refine ⟨10465983584432069046911513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6977322389621379364607675 10465983584432069046911513)
        ·
          refine ⟨7849487688324051785183635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10465983584432069046911513 7849487688324051785183635)
          ·
            refine ⟨11774231532486077677775453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849487688324051785183635 11774231532486077677775453)
            ·
              refine ⟨4415336824682279129165795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11774231532486077677775453 4415336824682279129165795)
              ·
                refine ⟨6623005237023418693748693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4415336824682279129165795 6623005237023418693748693)
                ·
                  refine ⟨155226685242736375634735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6623005237023418693748693 155226685242736375634735)
                  ·
                    rfl

theorem cell23_2720726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_2720726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720726 prefixEnd_2720726 := by exact prefixLift 2720726
  have htrace : WordTrace (prefixWord ++ tailWord_2720726) baseStart_2720726 baseEnd_2720726 := by
    simpa [prefixWord, tailWord_2720726, baseEnd_2720726] using wordTrace_append hprefix tailTrace_2720726
  have hstable : (prefixWord ++ tailWord_2720726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720726).length < 2 ^ (prefixWord ++ tailWord_2720726).sum := by decide
  have hdescent : baseEnd_2720726 < baseStart_2720726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720799 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 6]
def baseStart_2720799 : Nat := 118140960795 + 2720799 * 2 ^ 59
def prefixEnd_2720799 : Nat := 4983230072969 + 3 ^ 40 * 2720799 * 2
def baseEnd_2720799 : Nat := 155230850141378399455531

theorem tailTrace_2720799 : CollatzResearch.WordTrace tailWord_2720799 prefixEnd_2720799 155230850141378399455531 := by
  unfold tailWord_2720799
  simp only [CollatzResearch.WordTrace]
  refine ⟨99235692070017373319605451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66157128046678248879736967 99235692070017373319605451)
  ·
    refine ⟨148853538105026059979408177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99235692070017373319605451 148853538105026059979408177)
    ·
      refine ⟨111640153578769544984556133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148853538105026059979408177 111640153578769544984556133)
      ·
        refine ⟨20932528796019289684604275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111640153578769544984556133 20932528796019289684604275)
        ·
          refine ⟨31398793194028934526906413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20932528796019289684604275 31398793194028934526906413)
          ·
            refine ⟨11774547447760850447589905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31398793194028934526906413 11774547447760850447589905)
            ·
              refine ⟨8830910585820637835692429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11774547447760850447589905 8830910585820637835692429)
              ·
                refine ⟨3311591469682739188384661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8830910585820637835692429 3311591469682739188384661)
                ·
                  refine ⟨155230850141378399455531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3311591469682739188384661 155230850141378399455531)
                  ·
                    rfl

theorem cell23_2720799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 6].length) (baseStart_2720799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720799 prefixEnd_2720799 := by exact prefixLift 2720799
  have htrace : WordTrace (prefixWord ++ tailWord_2720799) baseStart_2720799 baseEnd_2720799 := by
    simpa [prefixWord, tailWord_2720799, baseEnd_2720799] using wordTrace_append hprefix tailTrace_2720799
  have hstable : (prefixWord ++ tailWord_2720799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720799).length < 2 ^ (prefixWord ++ tailWord_2720799).sum := by decide
  have hdescent : baseEnd_2720799 < baseStart_2720799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720810 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_2720810 : Nat := 118140960795 + 2720810 * 2 ^ 59
def prefixEnd_2720810 : Nat := 4983230072969 + 3 ^ 40 * 2720810 * 2
def baseEnd_2720810 : Nat := 1397083299559605052062229

theorem tailTrace_2720810 : CollatzResearch.WordTrace tailWord_2720810 prefixEnd_2720810 1397083299559605052062229 := by
  unfold tailWord_2720810
  simp only [CollatzResearch.WordTrace]
  refine ⟨24809023318244380549563971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66157395515318348132170589 24809023318244380549563971)
  ·
    refine ⟨37213534977366570824345957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24809023318244380549563971 37213534977366570824345957)
    ·
      refine ⟨6977537808256232029564867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37213534977366570824345957 6977537808256232029564867)
      ·
        refine ⟨10466306712384348044347301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6977537808256232029564867 10466306712384348044347301)
        ·
          refine ⟨1962432508572065258315119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10466306712384348044347301 1962432508572065258315119)
          ·
            refine ⟨2943648762858097887472679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962432508572065258315119 2943648762858097887472679)
            ·
              refine ⟨4415473144287146831209019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943648762858097887472679 4415473144287146831209019)
              ·
                refine ⟨6623209716430720246813529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4415473144287146831209019 6623209716430720246813529)
                ·
                  refine ⟨4967407287323040185110147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6623209716430720246813529 4967407287323040185110147)
                  ·
                    refine ⟨7451110930984560277665221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4967407287323040185110147 7451110930984560277665221)
                    ·
                      refine ⟨1397083299559605052062229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7451110930984560277665221 1397083299559605052062229)
                      ·
                        rfl

theorem cell23_2720810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_2720810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720810 prefixEnd_2720810 := by exact prefixLift 2720810
  have htrace : WordTrace (prefixWord ++ tailWord_2720810) baseStart_2720810 baseEnd_2720810 := by
    simpa [prefixWord, tailWord_2720810, baseEnd_2720810] using wordTrace_append hprefix tailTrace_2720810
  have hstable : (prefixWord ++ tailWord_2720810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720810).length < 2 ^ (prefixWord ++ tailWord_2720810).sum := by decide
  have hdescent : baseEnd_2720810 < baseStart_2720810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720820 : List Nat := [2, 5, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_2720820 : Nat := 118140960795 + 2720820 * 2 ^ 59
def prefixEnd_2720820 : Nat := 4983230072969 + 3 ^ 40 * 2720820 * 2
def baseEnd_2720820 : Nat := 465696144788716670979061

theorem tailTrace_2720820 : CollatzResearch.WordTrace tailWord_2720820 prefixEnd_2720820 465696144788716670979061 := by
  unfold tailWord_2720820
  simp only [CollatzResearch.WordTrace]
  refine ⟨49618229001470646953059957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66157638668627529270746609 49618229001470646953059957)
  ·
    refine ⟨4651708968887873151849371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49618229001470646953059957 4651708968887873151849371)
    ·
      refine ⟨6977563453331809727774057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4651708968887873151849371 6977563453331809727774057)
      ·
        refine ⟨5233172589998857295830543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6977563453331809727774057 5233172589998857295830543)
        ·
          refine ⟨7849758884998285943745815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5233172589998857295830543 7849758884998285943745815)
          ·
            refine ⟨11774638327497428915618723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849758884998285943745815 11774638327497428915618723)
            ·
              refine ⟨17661957491246143373428085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11774638327497428915618723 17661957491246143373428085)
              ·
                refine ⟨1655808514804325941258883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17661957491246143373428085 1655808514804325941258883)
                ·
                  refine ⟨2483712772206488911888325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655808514804325941258883 2483712772206488911888325)
                  ·
                    refine ⟨465696144788716670979061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2483712772206488911888325 465696144788716670979061)
                    ·
                      rfl

theorem cell23_2720820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_2720820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720820 prefixEnd_2720820 := by exact prefixLift 2720820
  have htrace : WordTrace (prefixWord ++ tailWord_2720820) baseStart_2720820 baseEnd_2720820 := by
    simpa [prefixWord, tailWord_2720820, baseEnd_2720820] using wordTrace_append hprefix tailTrace_2720820
  have hstable : (prefixWord ++ tailWord_2720820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720820).length < 2 ^ (prefixWord ++ tailWord_2720820).sum := by decide
  have hdescent : baseEnd_2720820 < baseStart_2720820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720833 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 6]
def baseStart_2720833 : Nat := 118140960795 + 2720833 * 2 ^ 59
def prefixEnd_2720833 : Nat := 4983230072969 + 3 ^ 40 * 2720833 * 2
def baseEnd_2720833 : Nat := 155232789957184273563847

theorem tailTrace_2720833 : CollatzResearch.WordTrace tailWord_2720833 prefixEnd_2720833 155232789957184273563847 := by
  unfold tailWord_2720833
  simp only [CollatzResearch.WordTrace]
  refine ⟨99236932151894197126343153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66157954767929464750895435 99236932151894197126343153)
  ·
    refine ⟨74427699113920647844757365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99236932151894197126343153 74427699113920647844757365)
    ·
      refine ⟨6977596791930060735446003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74427699113920647844757365 6977596791930060735446003)
      ·
        refine ⟨10466395187895091103169005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6977596791930060735446003 10466395187895091103169005)
        ·
          refine ⟨3924898195460659163688377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10466395187895091103169005 3924898195460659163688377)
          ·
            refine ⟨2943673646595494372766283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3924898195460659163688377 2943673646595494372766283)
            ·
              refine ⟨4415510469893241559149425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943673646595494372766283 4415510469893241559149425)
              ·
                refine ⟨3311632852419931169362069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4415510469893241559149425 3311632852419931169362069)
                ·
                  refine ⟨155232789957184273563847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3311632852419931169362069 155232789957184273563847)
                  ·
                    rfl

theorem cell23_2720833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 6].length) (baseStart_2720833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720833 prefixEnd_2720833 := by exact prefixLift 2720833
  have htrace : WordTrace (prefixWord ++ tailWord_2720833) baseStart_2720833 baseEnd_2720833 := by
    simpa [prefixWord, tailWord_2720833, baseEnd_2720833] using wordTrace_append hprefix tailTrace_2720833
  have hstable : (prefixWord ++ tailWord_2720833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720833).length < 2 ^ (prefixWord ++ tailWord_2720833).sum := by decide
  have hdescent : baseEnd_2720833 < baseStart_2720833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720849 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_2720849 : Nat := 118140960795 + 2720849 * 2 ^ 59
def prefixEnd_2720849 : Nat := 4983230072969 + 3 ^ 40 * 2720849 * 2
def baseEnd_2720849 : Nat := 1397103325305130399474549

theorem tailTrace_2720849 : CollatzResearch.WordTrace tailWord_2720849 prefixEnd_2720849 1397103325305130399474549 := by
  unfold tailWord_2720849
  simp only [CollatzResearch.WordTrace]
  refine ⟨99237515719836231858925601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66158343813224154572617067 99237515719836231858925601)
  ·
    refine ⟨74428136789877173894194201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99237515719836231858925601 74428136789877173894194201)
    ·
      refine ⟨55821102592407880420645651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74428136789877173894194201 55821102592407880420645651)
      ·
        refine ⟨83731653888611820630968477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55821102592407880420645651 83731653888611820630968477)
        ·
          refine ⟨31399370208229432736613179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83731653888611820630968477 31399370208229432736613179)
          ·
            refine ⟨47099055312344149104919769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31399370208229432736613179 47099055312344149104919769)
            ·
              refine ⟨35324291484258111828689827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47099055312344149104919769 35324291484258111828689827)
              ·
                refine ⟨52986437226387167743034741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35324291484258111828689827 52986437226387167743034741)
                ·
                  refine ⟨4967478489973796975909507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52986437226387167743034741 4967478489973796975909507)
                  ·
                    refine ⟨7451217734960695463864261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4967478489973796975909507 7451217734960695463864261)
                    ·
                      refine ⟨1397103325305130399474549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7451217734960695463864261 1397103325305130399474549)
                      ·
                        rfl

theorem cell23_2720849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_2720849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720849 prefixEnd_2720849 := by exact prefixLift 2720849
  have htrace : WordTrace (prefixWord ++ tailWord_2720849) baseStart_2720849 baseEnd_2720849 := by
    simpa [prefixWord, tailWord_2720849, baseEnd_2720849] using wordTrace_append hprefix tailTrace_2720849
  have hstable : (prefixWord ++ tailWord_2720849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720849).length < 2 ^ (prefixWord ++ tailWord_2720849).sum := by decide
  have hdescent : baseEnd_2720849 < baseStart_2720849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720869 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2720869 : Nat := 118140960795 + 2720869 * 2 ^ 59
def prefixEnd_2720869 : Nat := 4983230072969 + 3 ^ 40 * 2720869 * 2
def baseEnd_2720869 : Nat := 1397113594918220321224457

theorem tailTrace_2720869 : CollatzResearch.WordTrace tailWord_2720869 prefixEnd_2720869 1397113594918220321224457 := by
  unfold tailWord_2720869
  simp only [CollatzResearch.WordTrace]
  refine ⟨99238245179763775274653661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66158830119842516849769107 99238245179763775274653661)
  ·
    refine ⟨37214341942411415727995123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99238245179763775274653661 37214341942411415727995123)
    ·
      refine ⟨55821512913617123591992685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37214341942411415727995123 55821512913617123591992685)
      ·
        refine ⟨20933067342606421346997257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55821512913617123591992685 20933067342606421346997257)
        ·
          refine ⟨15699800506954816010247943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20933067342606421346997257 15699800506954816010247943)
          ·
            refine ⟨23549700760432224015371915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15699800506954816010247943 23549700760432224015371915)
            ·
              refine ⟨35324551140648336023057873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23549700760432224015371915 35324551140648336023057873)
              ·
                refine ⟨26493413355486252017293405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35324551140648336023057873 26493413355486252017293405)
                ·
                  refine ⟨9935030008307344506485027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26493413355486252017293405 9935030008307344506485027)
                  ·
                    refine ⟨14902545012461016759727541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9935030008307344506485027 14902545012461016759727541)
                    ·
                      refine ⟨1397113594918220321224457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14902545012461016759727541 1397113594918220321224457)
                      ·
                        rfl

theorem cell23_2720869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2720869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720869 prefixEnd_2720869 := by exact prefixLift 2720869
  have htrace : WordTrace (prefixWord ++ tailWord_2720869) baseStart_2720869 baseEnd_2720869 := by
    simpa [prefixWord, tailWord_2720869, baseEnd_2720869] using wordTrace_append hprefix tailTrace_2720869
  have hstable : (prefixWord ++ tailWord_2720869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720869).length < 2 ^ (prefixWord ++ tailWord_2720869).sum := by decide
  have hdescent : baseEnd_2720869 < baseStart_2720869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720877 : List Nat := [1, 5, 1, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_2720877 : Nat := 118140960795 + 2720877 * 2 ^ 59
def prefixEnd_2720877 : Nat := 4983230072969 + 3 ^ 40 * 2720877 * 2
def baseEnd_2720877 : Nat := 1397117702763456289924421

theorem tailTrace_2720877 : CollatzResearch.WordTrace tailWord_2720877 prefixEnd_2720877 1397117702763456289924421 := by
  unfold tailWord_2720877
  simp only [CollatzResearch.WordTrace]
  refine ⟨99238536963734792640944885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66159024642489861760629923 99238536963734792640944885)
  ·
    refine ⟨9303612840350136810088583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99238536963734792640944885 9303612840350136810088583)
    ·
      refine ⟨13955419260525205215132875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9303612840350136810088583 13955419260525205215132875)
      ·
        refine ⟨20933128890787807822699313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13955419260525205215132875 20933128890787807822699313)
        ·
          refine ⟨15699846668090855867024485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20933128890787807822699313 15699846668090855867024485)
          ·
            refine ⟨2943721250267035475067091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15699846668090855867024485 2943721250267035475067091)
            ·
              refine ⟨4415581875400553212600637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943721250267035475067091 4415581875400553212600637)
              ·
                refine ⟨1655843203275207454725239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4415581875400553212600637 1655843203275207454725239)
                ·
                  refine ⟨2483764804912811182087859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655843203275207454725239 2483764804912811182087859)
                  ·
                    refine ⟨3725647207369216773131789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2483764804912811182087859 3725647207369216773131789)
                    ·
                      refine ⟨1397117702763456289924421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3725647207369216773131789 1397117702763456289924421)
                      ·
                        rfl

theorem cell23_2720877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_2720877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720877 prefixEnd_2720877 := by exact prefixLift 2720877
  have htrace : WordTrace (prefixWord ++ tailWord_2720877) baseStart_2720877 baseEnd_2720877 := by
    simpa [prefixWord, tailWord_2720877, baseEnd_2720877] using wordTrace_append hprefix tailTrace_2720877
  have hstable : (prefixWord ++ tailWord_2720877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720877).length < 2 ^ (prefixWord ++ tailWord_2720877).sum := by decide
  have hdescent : baseEnd_2720877 < baseStart_2720877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720879 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_2720879 : Nat := 118140960795 + 2720879 * 2 ^ 59
def prefixEnd_2720879 : Nat := 4983230072969 + 3 ^ 40 * 2720879 * 2
def baseEnd_2720879 : Nat := 1397118729724765282099411

theorem tailTrace_2720879 : CollatzResearch.WordTrace tailWord_2720879 prefixEnd_2720879 1397118729724765282099411 := by
  unfold tailWord_2720879
  simp only [CollatzResearch.WordTrace]
  refine ⟨99238609909727546982517691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66159073273151697988345127 99238609909727546982517691)
  ·
    refine ⟨148857914864591320473776537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99238609909727546982517691 148857914864591320473776537)
    ·
      refine ⟨111643436148443490355332403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148857914864591320473776537 111643436148443490355332403)
      ·
        refine ⟨167465154222665235532998605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111643436148443490355332403 167465154222665235532998605)
        ·
          refine ⟨62799432833499463324874477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167465154222665235532998605 62799432833499463324874477)
          ·
            refine ⟨23549787312562298746827929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62799432833499463324874477 23549787312562298746827929)
            ·
              refine ⟨17662340484421724060120947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23549787312562298746827929 17662340484421724060120947)
              ·
                refine ⟨26493510726632586090181421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17662340484421724060120947 26493510726632586090181421)
                ·
                  refine ⟨9935066522487219783818033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26493510726632586090181421 9935066522487219783818033)
                  ·
                    refine ⟨7451299891865414837863525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9935066522487219783818033 7451299891865414837863525)
                    ·
                      refine ⟨1397118729724765282099411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7451299891865414837863525 1397118729724765282099411)
                      ·
                        rfl

theorem cell23_2720879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_2720879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720879 prefixEnd_2720879 := by exact prefixLift 2720879
  have htrace : WordTrace (prefixWord ++ tailWord_2720879) baseStart_2720879 baseEnd_2720879 := by
    simpa [prefixWord, tailWord_2720879, baseEnd_2720879] using wordTrace_append hprefix tailTrace_2720879
  have hstable : (prefixWord ++ tailWord_2720879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720879).length < 2 ^ (prefixWord ++ tailWord_2720879).sum := by decide
  have hdescent : baseEnd_2720879 < baseStart_2720879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720900 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_2720900 : Nat := 118140960795 + 2720900 * 2 ^ 59
def prefixEnd_2720900 : Nat := 4983230072969 + 3 ^ 40 * 2720900 * 2
def baseEnd_2720900 : Nat := 1397129512818509699936815

theorem tailTrace_2720900 : CollatzResearch.WordTrace tailWord_2720900 prefixEnd_2720900 1397129512818509699936815 := by
  unfold tailWord_2720900
  simp only [CollatzResearch.WordTrace]
  refine ⟨49619687921325733784516077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66159583895100978379354769 49619687921325733784516077)
  ·
    refine ⟨18607382970497150169193529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49619687921325733784516077 18607382970497150169193529)
    ·
      refine ⟨13955537227872862626895147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18607382970497150169193529 13955537227872862626895147)
      ·
        refine ⟨20933305841809293940342721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13955537227872862626895147 20933305841809293940342721)
        ·
          refine ⟨15699979381356970455257041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20933305841809293940342721 15699979381356970455257041)
          ·
            refine ⟨11774984536017727841442781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15699979381356970455257041 11774984536017727841442781)
            ·
              refine ⟨4415619201006647940541043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11774984536017727841442781 4415619201006647940541043)
              ·
                refine ⟨6623428801509971910811565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4415619201006647940541043 6623428801509971910811565)
                ·
                  refine ⟨2483785800566239466554337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6623428801509971910811565 2483785800566239466554337)
                  ·
                    refine ⟨1862839350424679599915753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2483785800566239466554337 1862839350424679599915753)
                    ·
                      refine ⟨1397129512818509699936815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862839350424679599915753 1397129512818509699936815)
                      ·
                        rfl

theorem cell23_2720900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_2720900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720900 prefixEnd_2720900 := by exact prefixLift 2720900
  have htrace : WordTrace (prefixWord ++ tailWord_2720900) baseStart_2720900 baseEnd_2720900 := by
    simpa [prefixWord, tailWord_2720900, baseEnd_2720900] using wordTrace_append hprefix tailTrace_2720900
  have hstable : (prefixWord ++ tailWord_2720900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720900).length < 2 ^ (prefixWord ++ tailWord_2720900).sum := by decide
  have hdescent : baseEnd_2720900 < baseStart_2720900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720910 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_2720910 : Nat := 118140960795 + 2720910 * 2 ^ 59
def prefixEnd_2720910 : Nat := 4983230072969 + 3 ^ 40 * 2720910 * 2
def baseEnd_2720910 : Nat := 465711549208351553603923

theorem tailTrace_2720910 : CollatzResearch.WordTrace tailWord_2720910 prefixEnd_2720910 465711549208351553603923 := by
  unfold tailWord_2720910
  simp only [CollatzResearch.WordTrace]
  refine ⟨12404967571576904909612023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66159827048410159517930789 12404967571576904909612023)
  ·
    refine ⟨18607451357365357364418035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12404967571576904909612023 18607451357365357364418035)
    ·
      refine ⟨27911177036048036046627053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18607451357365357364418035 27911177036048036046627053)
      ·
        refine ⟨10466691388518013517485145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27911177036048036046627053 10466691388518013517485145)
        ·
          refine ⟨7850018541388510138113859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10466691388518013517485145 7850018541388510138113859)
          ·
            refine ⟨11775027812082765207170789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7850018541388510138113859 11775027812082765207170789)
            ·
              refine ⟨2207817714765518476344523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11775027812082765207170789 2207817714765518476344523)
              ·
                refine ⟨3311726572148277714516785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207817714765518476344523 3311726572148277714516785)
                ·
                  refine ⟨2483794929111208285887589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3311726572148277714516785 2483794929111208285887589)
                  ·
                    refine ⟨465711549208351553603923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2483794929111208285887589 465711549208351553603923)
                    ·
                      rfl

theorem cell23_2720910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_2720910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720910 prefixEnd_2720910 := by exact prefixLift 2720910
  have htrace : WordTrace (prefixWord ++ tailWord_2720910) baseStart_2720910 baseEnd_2720910 := by
    simpa [prefixWord, tailWord_2720910, baseEnd_2720910] using wordTrace_append hprefix tailTrace_2720910
  have hstable : (prefixWord ++ tailWord_2720910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720910).length < 2 ^ (prefixWord ++ tailWord_2720910).sum := by decide
  have hdescent : baseEnd_2720910 < baseStart_2720910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720920 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2720920 : Nat := 118140960795 + 2720920 * 2 ^ 59
def prefixEnd_2720920 : Nat := 4983230072969 + 3 ^ 40 * 2720920 * 2
def baseEnd_2720920 : Nat := 1397139782431599621686723

theorem tailTrace_2720920 : CollatzResearch.WordTrace tailWord_2720920 prefixEnd_2720920 1397139782431599621686723 := by
  unfold tailWord_2720920
  simp only [CollatzResearch.WordTrace]
  refine ⟨49620052651289505492380107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66160070201719340656506809 49620052651289505492380107)
  ·
    refine ⟨74430078976934258238570161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49620052651289505492380107 74430078976934258238570161)
    ·
      refine ⟨55822559232700693678927621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74430078976934258238570161 55822559232700693678927621)
      ·
        refine ⟨10466729856131380064798929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55822559232700693678927621 10466729856131380064798929)
        ·
          refine ⟨7850047392098535048599197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10466729856131380064798929 7850047392098535048599197)
          ·
            refine ⟨2943767772036950643224699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7850047392098535048599197 2943767772036950643224699)
            ·
              refine ⟨4415651658055425964837049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943767772036950643224699 4415651658055425964837049)
              ·
                refine ⟨3311738743541569473627787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4415651658055425964837049 3311738743541569473627787)
                ·
                  refine ⟨4967608115312354210441681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311738743541569473627787 4967608115312354210441681)
                  ·
                    refine ⟨3725706086484265657831261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4967608115312354210441681 3725706086484265657831261)
                    ·
                      refine ⟨1397139782431599621686723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3725706086484265657831261 1397139782431599621686723)
                      ·
                        rfl

theorem cell23_2720920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2720920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720920 prefixEnd_2720920 := by exact prefixLift 2720920
  have htrace : WordTrace (prefixWord ++ tailWord_2720920) baseStart_2720920 baseEnd_2720920 := by
    simpa [prefixWord, tailWord_2720920, baseEnd_2720920] using wordTrace_append hprefix tailTrace_2720920
  have hstable : (prefixWord ++ tailWord_2720920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720920).length < 2 ^ (prefixWord ++ tailWord_2720920).sum := by decide
  have hdescent : baseEnd_2720920 < baseStart_2720920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720943 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 1, 3, 2]
def baseStart_2720943 : Nat := 118140960795 + 2720943 * 2 ^ 59
def prefixEnd_2720943 : Nat := 4983230072969 + 3 ^ 40 * 2720943 * 2
def baseEnd_2720943 : Nat := 1397151592486653031699117

theorem tailTrace_2720943 : CollatzResearch.WordTrace tailWord_2720943 prefixEnd_2720943 1397151592486653031699117 := by
  unfold tailWord_2720943
  simp only [CollatzResearch.WordTrace]
  refine ⟨99240944181495685912847483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66160629454330457275231655 99240944181495685912847483)
  ·
    refine ⟨148861416272243528869271225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99240944181495685912847483 148861416272243528869271225)
    ·
      refine ⟨111646062204182646651953419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148861416272243528869271225 111646062204182646651953419)
      ·
        refine ⟨167469093306273969977930129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111646062204182646651953419 167469093306273969977930129)
        ·
          refine ⟨125601819979705477483447597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167469093306273969977930129 125601819979705477483447597)
          ·
            refine ⟨47100682492389554056292849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125601819979705477483447597 47100682492389554056292849)
            ·
              refine ⟨35325511869292165542219637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47100682492389554056292849 35325511869292165542219637)
              ·
                refine ⟨3311766737746140519583091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35325511869292165542219637 3311766737746140519583091)
                ·
                  refine ⟨4967650106619210779374637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311766737746140519583091 4967650106619210779374637)
                  ·
                    refine ⟨1862868789982204042265489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4967650106619210779374637 1862868789982204042265489)
                    ·
                      refine ⟨1397151592486653031699117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1862868789982204042265489 1397151592486653031699117)
                      ·
                        rfl

theorem cell23_2720943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 3, 2].length) (baseStart_2720943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720943 prefixEnd_2720943 := by exact prefixLift 2720943
  have htrace : WordTrace (prefixWord ++ tailWord_2720943) baseStart_2720943 baseEnd_2720943 := by
    simpa [prefixWord, tailWord_2720943, baseEnd_2720943] using wordTrace_append hprefix tailTrace_2720943
  have hstable : (prefixWord ++ tailWord_2720943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720943).length < 2 ^ (prefixWord ++ tailWord_2720943).sum := by decide
  have hdescent : baseEnd_2720943 < baseStart_2720943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720956 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2720956 : Nat := 118140960795 + 2720956 * 2 ^ 59
def prefixEnd_2720956 : Nat := 4983230072969 + 3 ^ 40 * 2720956 * 2
def baseEnd_2720956 : Nat := 1397158267735161480836557

theorem tailTrace_2720956 : CollatzResearch.WordTrace tailWord_2720956 prefixEnd_2720956 1397158267735161480836557 := by
  unfold tailWord_2720956
  simp only [CollatzResearch.WordTrace]
  refine ⟨49620709165224294566535361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66160945553632392755380481 49620709165224294566535361)
  ·
    refine ⟨37215531873918220924901521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49620709165224294566535361 37215531873918220924901521)
    ·
      refine ⟨27911648905438665693676141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37215531873918220924901521 27911648905438665693676141)
      ·
        refine ⟨10466868339539499635128553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27911648905438665693676141 10466868339539499635128553)
        ·
          refine ⟨7850151254654624726346415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10466868339539499635128553 7850151254654624726346415)
          ·
            refine ⟨11775226881981937089519623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7850151254654624726346415 11775226881981937089519623)
            ·
              refine ⟨17662840322972905634279435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11775226881981937089519623 17662840322972905634279435)
              ·
                refine ⟨26494260484459358451419153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17662840322972905634279435 26494260484459358451419153)
                ·
                  refine ⟨19870695363344518838564365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26494260484459358451419153 19870695363344518838564365)
                  ·
                    refine ⟨7451510761254194564461637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19870695363344518838564365 7451510761254194564461637)
                    ·
                      refine ⟨1397158267735161480836557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7451510761254194564461637 1397158267735161480836557)
                      ·
                        rfl

theorem cell23_2720956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2720956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720956 prefixEnd_2720956 := by exact prefixLift 2720956
  have htrace : WordTrace (prefixWord ++ tailWord_2720956) baseStart_2720956 baseEnd_2720956 := by
    simpa [prefixWord, tailWord_2720956, baseEnd_2720956] using wordTrace_append hprefix tailTrace_2720956
  have hstable : (prefixWord ++ tailWord_2720956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720956).length < 2 ^ (prefixWord ++ tailWord_2720956).sum := by decide
  have hdescent : baseEnd_2720956 < baseStart_2720956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720959 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_2720959 : Nat := 118140960795 + 2720959 * 2 ^ 59
def prefixEnd_2720959 : Nat := 4983230072969 + 3 ^ 40 * 2720959 * 2
def baseEnd_2720959 : Nat := 1397159808177124969099043

theorem tailTrace_2720959 : CollatzResearch.WordTrace tailWord_2720959 prefixEnd_2720959 1397159808177124969099043 := by
  unfold tailWord_2720959
  simp only [CollatzResearch.WordTrace]
  refine ⟨99241527749437720645429931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66161018499625147096953287 99241527749437720645429931)
  ·
    refine ⟨148862291624156580968144897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99241527749437720645429931 148862291624156580968144897)
    ·
      refine ⟨111646718718117435726108673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148862291624156580968144897 111646718718117435726108673)
      ·
        refine ⟨83735039038588076794581505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111646718718117435726108673 83735039038588076794581505)
        ·
          refine ⟨62801279278941057595936129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83735039038588076794581505 62801279278941057595936129)
          ·
            refine ⟨47100959459205793196952097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62801279278941057595936129 47100959459205793196952097)
            ·
              refine ⟨35325719594404344897714073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47100959459205793196952097 35325719594404344897714073)
              ·
                refine ⟨26494289695803258673285555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35325719594404344897714073 26494289695803258673285555)
                ·
                  refine ⟨39741434543704888009928333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26494289695803258673285555 39741434543704888009928333)
                  ·
                    refine ⟨14903037953889333003723125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39741434543704888009928333 14903037953889333003723125)
                    ·
                      refine ⟨1397159808177124969099043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14903037953889333003723125 1397159808177124969099043)
                      ·
                        rfl

theorem cell23_2720959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_2720959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720959 prefixEnd_2720959 := by exact prefixLift 2720959
  have htrace : WordTrace (prefixWord ++ tailWord_2720959) baseStart_2720959 baseEnd_2720959 := by
    simpa [prefixWord, tailWord_2720959, baseEnd_2720959] using wordTrace_append hprefix tailTrace_2720959
  have hstable : (prefixWord ++ tailWord_2720959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720959).length < 2 ^ (prefixWord ++ tailWord_2720959).sum := by decide
  have hdescent : baseEnd_2720959 < baseStart_2720959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720979 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 7]
def baseStart_2720979 : Nat := 118140960795 + 2720979 * 2 ^ 59
def prefixEnd_2720979 : Nat := 4983230072969 + 3 ^ 40 * 2720979 * 2
def baseEnd_2720979 : Nat := 155241119754468321205439

theorem tailTrace_2720979 : CollatzResearch.WordTrace tailWord_2720979 prefixEnd_2720979 155241119754468321205439 := by
  unfold tailWord_2720979
  simp only [CollatzResearch.WordTrace]
  refine ⟨99242257209365264061157991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66161504806243509374105327 99242257209365264061157991)
  ·
    refine ⟨148863385814047896091736987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99242257209365264061157991 148863385814047896091736987)
    ·
      refine ⟨223295078721071844137605481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148863385814047896091736987 223295078721071844137605481)
      ·
        refine ⟨167471309040803883103204111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223295078721071844137605481 167471309040803883103204111)
        ·
          refine ⟨251206963561205824654806167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167471309040803883103204111 251206963561205824654806167)
          ·
            refine ⟨376810445341808736982209251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251206963561205824654806167 376810445341808736982209251)
            ·
              refine ⟨565215668012713105473313877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376810445341808736982209251 565215668012713105473313877)
              ·
                refine ⟨6623621109523981704765397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 565215668012713105473313877 6623621109523981704765397)
                ·
                  refine ⟨155241119754468321205439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6623621109523981704765397 155241119754468321205439)
                  ·
                    rfl

theorem cell23_2720979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 7].length) (baseStart_2720979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2720979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2720979 prefixEnd_2720979 := by exact prefixLift 2720979
  have htrace : WordTrace (prefixWord ++ tailWord_2720979) baseStart_2720979 baseEnd_2720979 := by
    simpa [prefixWord, tailWord_2720979, baseEnd_2720979] using wordTrace_append hprefix tailTrace_2720979
  have hstable : (prefixWord ++ tailWord_2720979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720979).length < 2 ^ (prefixWord ++ tailWord_2720979).sum := by decide
  have hdescent : baseEnd_2720979 < baseStart_2720979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721094 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_2721094 : Nat := 118140960795 + 2721094 * 2 ^ 59
def prefixEnd_2721094 : Nat := 4983230072969 + 3 ^ 40 * 2721094 * 2
def baseEnd_2721094 : Nat := 465743042688493980303641

theorem tailTrace_2721094 : CollatzResearch.WordTrace tailWord_2721094 prefixEnd_2721094 465743042688493980303641 := by
  unfold tailWord_2721094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101451612623394959424823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66164301069299092467729557 3101451612623394959424823)
  ·
    refine ⟨4652177418935092439137235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3101451612623394959424823 4652177418935092439137235)
    ·
      refine ⟨6978266128402638658705853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4652177418935092439137235 6978266128402638658705853)
      ·
        refine ⟨2616849798150989497014695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6978266128402638658705853 2616849798150989497014695)
        ·
          refine ⟨3925274697226484245522043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2616849798150989497014695 3925274697226484245522043)
          ·
            refine ⟨5887912045839726368283065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925274697226484245522043 5887912045839726368283065)
            ·
              refine ⟨4415934034379794776212299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5887912045839726368283065 4415934034379794776212299)
              ·
                refine ⟨6623901051569692164318449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4415934034379794776212299 6623901051569692164318449)
                ·
                  refine ⟨4967925788677269123238837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6623901051569692164318449 4967925788677269123238837)
                  ·
                    refine ⟨465743042688493980303641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4967925788677269123238837 465743042688493980303641)
                    ·
                      rfl

theorem cell23_2721094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_2721094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721094 prefixEnd_2721094 := by exact prefixLift 2721094
  have htrace : WordTrace (prefixWord ++ tailWord_2721094) baseStart_2721094 baseEnd_2721094 := by
    simpa [prefixWord, tailWord_2721094, baseEnd_2721094] using wordTrace_append hprefix tailTrace_2721094
  have hstable : (prefixWord ++ tailWord_2721094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721094).length < 2 ^ (prefixWord ++ tailWord_2721094).sum := by decide
  have hdescent : baseEnd_2721094 < baseStart_2721094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721100 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2721100 : Nat := 118140960795 + 2721100 * 2 ^ 59
def prefixEnd_2721100 : Nat := 4983230072969 + 3 ^ 40 * 2721100 * 2
def baseEnd_2721100 : Nat := 1397232208949408917435895

theorem tailTrace_2721100 : CollatzResearch.WordTrace tailWord_2721100 prefixEnd_2721100 1397232208949408917435895 := by
  unfold tailWord_2721100
  simp only [CollatzResearch.WordTrace]
  refine ⟨49623335220963450863156377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66164446961284601150875169 49623335220963450863156377)
  ·
    refine ⟨37217501415722588147367283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49623335220963450863156377 37217501415722588147367283)
    ·
      refine ⟨55826252123583882221050925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37217501415722588147367283 55826252123583882221050925)
      ·
        refine ⟨20934844546343955832894097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55826252123583882221050925 20934844546343955832894097)
        ·
          refine ⟨15701133409757966874670573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20934844546343955832894097 15701133409757966874670573)
          ·
            refine ⟨5887925028659237578001465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15701133409757966874670573 5887925028659237578001465)
            ·
              refine ⟨4415943771494428183501099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5887925028659237578001465 4415943771494428183501099)
              ·
                refine ⟨6623915657241642275251649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4415943771494428183501099 6623915657241642275251649)
                ·
                  refine ⟨4967936742931231706438737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6623915657241642275251649 4967936742931231706438737)
                  ·
                    refine ⟨3725952557198423779829053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4967936742931231706438737 3725952557198423779829053)
                    ·
                      refine ⟨1397232208949408917435895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3725952557198423779829053 1397232208949408917435895)
                      ·
                        rfl

theorem cell23_2721100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2721100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721100 prefixEnd_2721100 := by exact prefixLift 2721100
  have htrace : WordTrace (prefixWord ++ tailWord_2721100) baseStart_2721100 baseEnd_2721100 := by
    simpa [prefixWord, tailWord_2721100, baseEnd_2721100] using wordTrace_append hprefix tailTrace_2721100
  have hstable : (prefixWord ++ tailWord_2721100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721100).length < 2 ^ (prefixWord ++ tailWord_2721100).sum := by decide
  have hdescent : baseEnd_2721100 < baseStart_2721100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721106 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2721106 : Nat := 118140960795 + 2721106 * 2 ^ 59
def prefixEnd_2721106 : Nat := 4983230072969 + 3 ^ 40 * 2721106 * 2
def baseEnd_2721106 : Nat := 1397235289833335893960867

theorem tailTrace_2721106 : CollatzResearch.WordTrace tailWord_2721106 prefixEnd_2721106 1397235289833335893960867 := by
  unfold tailWord_2721106
  simp only [CollatzResearch.WordTrace]
  refine ⟨24811722319976291187757793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66164592853270109834020781 24811722319976291187757793)
  ·
    refine ⟨18608791739982218390818345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24811722319976291187757793 18608791739982218390818345)
    ·
      refine ⟨13956593804986663793113759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18608791739982218390818345 13956593804986663793113759)
      ·
        refine ⟨20934890707479995689670639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13956593804986663793113759 20934890707479995689670639)
        ·
          refine ⟨31402336061219993534505959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20934890707479995689670639 31402336061219993534505959)
          ·
            refine ⟨47103504091829990301758939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31402336061219993534505959 47103504091829990301758939)
            ·
              refine ⟨70655256137744985452638409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47103504091829990301758939 70655256137744985452638409)
              ·
                refine ⟨52991442103308739089478807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70655256137744985452638409 52991442103308739089478807)
                ·
                  refine ⟨79487163154963108634218211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52991442103308739089478807 79487163154963108634218211)
                  ·
                    refine ⟨119230744732444662951327317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79487163154963108634218211 119230744732444662951327317)
                    ·
                      refine ⟨1397235289833335893960867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 119230744732444662951327317 1397235289833335893960867)
                      ·
                        rfl

theorem cell23_2721106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2721106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721106 prefixEnd_2721106 := by exact prefixLift 2721106
  have htrace : WordTrace (prefixWord ++ tailWord_2721106) baseStart_2721106 baseEnd_2721106 := by
    simpa [prefixWord, tailWord_2721106, baseEnd_2721106] using wordTrace_append hprefix tailTrace_2721106
  have hstable : (prefixWord ++ tailWord_2721106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721106).length < 2 ^ (prefixWord ++ tailWord_2721106).sum := by decide
  have hdescent : baseEnd_2721106 < baseStart_2721106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721124 : List Nat := [2, 3, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_2721124 : Nat := 118140960795 + 2721124 * 2 ^ 59
def prefixEnd_2721124 : Nat := 4983230072969 + 3 ^ 40 * 2721124 * 2
def baseEnd_2721124 : Nat := 465748177495038941178595

theorem tailTrace_2721124 : CollatzResearch.WordTrace tailWord_2721124 prefixEnd_2721124 465748177495038941178595 := by
  unfold tailWord_2721124
  simp only [CollatzResearch.WordTrace]
  refine ⟨49623772896919976912593213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66165030529226635883457617 49623772896919976912593213)
  ·
    refine ⟨18608914836344991342222455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49623772896919976912593213 18608914836344991342222455)
    ·
      refine ⟨27913372254517487013333683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18608914836344991342222455 27913372254517487013333683)
      ·
        refine ⟨41870058381776230520000525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27913372254517487013333683 41870058381776230520000525)
        ·
          refine ⟨15701271893166086445000197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41870058381776230520000525 15701271893166086445000197)
          ·
            refine ⟨2943988479968641208437537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15701271893166086445000197 2943988479968641208437537)
            ·
              refine ⟨2207991359976480906328153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2943988479968641208437537 2207991359976480906328153)
              ·
                refine ⟨1655993519982360679746115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2207991359976480906328153 1655993519982360679746115)
                ·
                  refine ⟨2483990279973541019619173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655993519982360679746115 2483990279973541019619173)
                  ·
                    refine ⟨465748177495038941178595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2483990279973541019619173 465748177495038941178595)
                    ·
                      rfl

theorem cell23_2721124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_2721124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721124 prefixEnd_2721124 := by exact prefixLift 2721124
  have htrace : WordTrace (prefixWord ++ tailWord_2721124) baseStart_2721124 baseEnd_2721124 := by
    simpa [prefixWord, tailWord_2721124, baseEnd_2721124] using wordTrace_append hprefix tailTrace_2721124
  have hstable : (prefixWord ++ tailWord_2721124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721124).length < 2 ^ (prefixWord ++ tailWord_2721124).sum := by decide
  have hdescent : baseEnd_2721124 < baseStart_2721124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721133 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_2721133 : Nat := 118140960795 + 2721133 * 2 ^ 59
def prefixEnd_2721133 : Nat := 4983230072969 + 3 ^ 40 * 2721133 * 2
def baseEnd_2721133 : Nat := 465749717937002429441081

theorem tailTrace_2721133 : CollatzResearch.WordTrace tailWord_2721133 prefixEnd_2721133 465749717937002429441081 := by
  unfold tailWord_2721133
  simp only [CollatzResearch.WordTrace]
  refine ⟨99247874050807348362264053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66165249367204898908176035 99247874050807348362264053)
  ·
    refine ⟨9304488192263188908962255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99247874050807348362264053 9304488192263188908962255)
    ·
      refine ⟨13956732288394783363443383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9304488192263188908962255 13956732288394783363443383)
      ·
        refine ⟨20935098432592175045165075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13956732288394783363443383 20935098432592175045165075)
        ·
          refine ⟨31402647648888262567747613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20935098432592175045165075 31402647648888262567747613)
          ·
            refine ⟨11775992868333098462905355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31402647648888262567747613 11775992868333098462905355)
            ·
              refine ⟨17663989302499647694358033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11775992868333098462905355 17663989302499647694358033)
              ·
                refine ⟨13247991976874735770768525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17663989302499647694358033 13247991976874735770768525)
                ·
                  refine ⟨4967996991328025914038197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13247991976874735770768525 4967996991328025914038197)
                  ·
                    refine ⟨465749717937002429441081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4967996991328025914038197 465749717937002429441081)
                    ·
                      rfl

theorem cell23_2721133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_2721133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721133 prefixEnd_2721133 := by exact prefixLift 2721133
  have htrace : WordTrace (prefixWord ++ tailWord_2721133) baseStart_2721133 baseEnd_2721133 := by
    simpa [prefixWord, tailWord_2721133, baseEnd_2721133] using wordTrace_append hprefix tailTrace_2721133
  have hstable : (prefixWord ++ tailWord_2721133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721133).length < 2 ^ (prefixWord ++ tailWord_2721133).sum := by decide
  have hdescent : baseEnd_2721133 < baseStart_2721133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721146 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_2721146 : Nat := 118140960795 + 2721146 * 2 ^ 59
def prefixEnd_2721146 : Nat := 4983230072969 + 3 ^ 40 * 2721146 * 2
def baseEnd_2721146 : Nat := 465751943019838579153561

theorem tailTrace_2721146 : CollatzResearch.WordTrace tailWord_2721146 prefixEnd_2721146 465751943019838579153561 := by
  unfold tailWord_2721146
  simp only [CollatzResearch.WordTrace]
  refine ⟨24812087049940062895621823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66165565466506834388324861 24812087049940062895621823)
  ·
    refine ⟨37218130574910094343432735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24812087049940062895621823 37218130574910094343432735)
    ·
      refine ⟨55827195862365141515149103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37218130574910094343432735 55827195862365141515149103)
      ·
        refine ⟨83740793793547712272723655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55827195862365141515149103 83740793793547712272723655)
        ·
          refine ⟨125611190690321568409085483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83740793793547712272723655 125611190690321568409085483)
          ·
            refine ⟨188416786035482352613628225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125611190690321568409085483 188416786035482352613628225)
            ·
              refine ⟨141312589526611764460221169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188416786035482352613628225 141312589526611764460221169)
              ·
                refine ⟨105984442144958823345165877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141312589526611764460221169 105984442144958823345165877)
                ·
                  refine ⟨9936041451089889688609301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105984442144958823345165877 9936041451089889688609301)
                  ·
                    refine ⟨465751943019838579153561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9936041451089889688609301 465751943019838579153561)
                    ·
                      rfl

theorem cell23_2721146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_2721146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721146 prefixEnd_2721146 := by exact prefixLift 2721146
  have htrace : WordTrace (prefixWord ++ tailWord_2721146) baseStart_2721146 baseEnd_2721146 := by
    simpa [prefixWord, tailWord_2721146, baseEnd_2721146] using wordTrace_append hprefix tailTrace_2721146
  have hstable : (prefixWord ++ tailWord_2721146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721146).length < 2 ^ (prefixWord ++ tailWord_2721146).sum := by decide
  have hdescent : baseEnd_2721146 < baseStart_2721146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721163 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 4, 4]
def baseStart_2721163 : Nat := 118140960795 + 2721163 * 2 ^ 59
def prefixEnd_2721163 : Nat := 4983230072969 + 3 ^ 40 * 2721163 * 2
def baseEnd_2721163 : Nat := 465754852743547390316035

theorem tailTrace_2721163 : CollatzResearch.WordTrace tailWord_2721163 prefixEnd_2721163 465754852743547390316035 := by
  unfold tailWord_2721163
  simp only [CollatzResearch.WordTrace]
  refine ⟨99248968240698663485856143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66165978827132442323904095 99248968240698663485856143)
  ·
    refine ⟨148873452361047995228784215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99248968240698663485856143 148873452361047995228784215)
    ·
      refine ⟨223310178541571992843176323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148873452361047995228784215 223310178541571992843176323)
      ·
        refine ⟨334965267812357989264764485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223310178541571992843176323 334965267812357989264764485)
        ·
          refine ⟨62805987714817122987143341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 334965267812357989264764485 62805987714817122987143341)
          ·
            refine ⟨23552245393056421120178753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62805987714817122987143341 23552245393056421120178753)
            ·
              refine ⟨17664184044792315840134065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23552245393056421120178753 17664184044792315840134065)
              ·
                refine ⟨13248138033594236880100549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17664184044792315840134065 13248138033594236880100549)
                ·
                  refine ⟨2484025881298919415018853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13248138033594236880100549 2484025881298919415018853)
                  ·
                    refine ⟨465754852743547390316035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2484025881298919415018853 465754852743547390316035)
                    ·
                      rfl

theorem cell23_2721163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 4].length) (baseStart_2721163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721163 prefixEnd_2721163 := by exact prefixLift 2721163
  have htrace : WordTrace (prefixWord ++ tailWord_2721163) baseStart_2721163 baseEnd_2721163 := by
    simpa [prefixWord, tailWord_2721163, baseEnd_2721163] using wordTrace_append hprefix tailTrace_2721163
  have hstable : (prefixWord ++ tailWord_2721163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721163).length < 2 ^ (prefixWord ++ tailWord_2721163).sum := by decide
  have hdescent : baseEnd_2721163 < baseStart_2721163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721187 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 3, 2, 2]
def baseStart_2721187 : Nat := 118140960795 + 2721187 * 2 ^ 59
def prefixEnd_2721187 : Nat := 4983230072969 + 3 ^ 40 * 2721187 * 2
def baseEnd_2721187 : Nat := 1397276881766350077047995

theorem tailTrace_2721187 : CollatzResearch.WordTrace tailWord_2721187 prefixEnd_2721187 1397276881766350077047995 := by
  unfold tailWord_2721187
  simp only [CollatzResearch.WordTrace]
  refine ⟨99249843592611715584729815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66166562395074477056486543 99249843592611715584729815)
  ·
    refine ⟨148874765388917573377094723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99249843592611715584729815 148874765388917573377094723)
    ·
      refine ⟨223312148083376360065642085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148874765388917573377094723 223312148083376360065642085)
      ·
        refine ⟨41871027765633067512307891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223312148083376360065642085 41871027765633067512307891)
        ·
          refine ⟨62806541648449601268461837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41871027765633067512307891 62806541648449601268461837)
          ·
            refine ⟨23552453118168600475673189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62806541648449601268461837 23552453118168600475673189)
            ·
              refine ⟨4416084959656612589188723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23552453118168600475673189 4416084959656612589188723)
              ·
                refine ⟨6624127439484918883783085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416084959656612589188723 6624127439484918883783085)
                ·
                  refine ⟨2484047789806844581418657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6624127439484918883783085 2484047789806844581418657)
                  ·
                    refine ⟨1863035842355133436063993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2484047789806844581418657 1863035842355133436063993)
                    ·
                      refine ⟨1397276881766350077047995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863035842355133436063993 1397276881766350077047995)
                      ·
                        rfl

theorem cell23_2721187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_2721187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721187 prefixEnd_2721187 := by exact prefixLift 2721187
  have htrace : WordTrace (prefixWord ++ tailWord_2721187) baseStart_2721187 baseEnd_2721187 := by
    simpa [prefixWord, tailWord_2721187, baseEnd_2721187] using wordTrace_append hprefix tailTrace_2721187
  have hstable : (prefixWord ++ tailWord_2721187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721187).length < 2 ^ (prefixWord ++ tailWord_2721187).sum := by decide
  have hdescent : baseEnd_2721187 < baseStart_2721187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721197 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_2721197 : Nat := 118140960795 + 2721197 * 2 ^ 59
def prefixEnd_2721197 : Nat := 4983230072969 + 3 ^ 40 * 2721197 * 2
def baseEnd_2721197 : Nat := 465760672190965012640983

theorem tailTrace_2721197 : CollatzResearch.WordTrace tailWord_2721197 prefixEnd_2721197 465760672190965012640983 := by
  unfold tailWord_2721197
  simp only [CollatzResearch.WordTrace]
  refine ⟨99250208322575487292593845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66166805548383658195062563 99250208322575487292593845)
  ·
    refine ⟨9304707030241451933680673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99250208322575487292593845 9304707030241451933680673)
    ·
      refine ⟨6978530272681088950260505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9304707030241451933680673 6978530272681088950260505)
      ·
        refine ⟨5233897704510816712695379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6978530272681088950260505 5233897704510816712695379)
        ·
          refine ⟨7850846556766225069043069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5233897704510816712695379 7850846556766225069043069)
          ·
            refine ⟨2944067458787334400891151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7850846556766225069043069 2944067458787334400891151)
            ·
              refine ⟨4416101188181001601336727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2944067458787334400891151 4416101188181001601336727)
              ·
                refine ⟨6624151782271502402005091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416101188181001601336727 6624151782271502402005091)
                ·
                  refine ⟨9936227673407253603007637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6624151782271502402005091 9936227673407253603007637)
                  ·
                    refine ⟨465760672190965012640983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9936227673407253603007637 465760672190965012640983)
                    ·
                      rfl

theorem cell23_2721197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_2721197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721197 prefixEnd_2721197 := by exact prefixLift 2721197
  have htrace : WordTrace (prefixWord ++ tailWord_2721197) baseStart_2721197 baseEnd_2721197 := by
    simpa [prefixWord, tailWord_2721197, baseEnd_2721197] using wordTrace_append hprefix tailTrace_2721197
  have hstable : (prefixWord ++ tailWord_2721197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721197).length < 2 ^ (prefixWord ++ tailWord_2721197).sum := by decide
  have hdescent : baseEnd_2721197 < baseStart_2721197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721237 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2721237 : Nat := 118140960795 + 2721237 * 2 ^ 59
def prefixEnd_2721237 : Nat := 4983230072969 + 3 ^ 40 * 2721237 * 2
def baseEnd_2721237 : Nat := 1397302555799074881422765

theorem tailTrace_2721237 : CollatzResearch.WordTrace tailWord_2721237 prefixEnd_2721237 1397302555799074881422765 := by
  unfold tailWord_2721237
  simp only [CollatzResearch.WordTrace]
  refine ⟨99251667242430574124049965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66167778161620382749366643 99251667242430574124049965)
  ·
    refine ⟨37219375215911465296518737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99251667242430574124049965 37219375215911465296518737)
    ·
      refine ⟨27914531411933598972389053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37219375215911465296518737 27914531411933598972389053)
      ·
        refine ⟨10467949279475099614645895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27914531411933598972389053 10467949279475099614645895)
        ·
          refine ⟨15701923919212649421968843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10467949279475099614645895 15701923919212649421968843)
          ·
            refine ⟨23552885878818974132953265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15701923919212649421968843 23552885878818974132953265)
            ·
              refine ⟨17664664409114230599714949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23552885878818974132953265 17664664409114230599714949)
              ·
                refine ⟨3312124576708918237446553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17664664409114230599714949 3312124576708918237446553)
                ·
                  refine ⟨2484093432531688678084915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3312124576708918237446553 2484093432531688678084915)
                  ·
                    refine ⟨3726140148797533017127373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2484093432531688678084915 3726140148797533017127373)
                    ·
                      refine ⟨1397302555799074881422765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3726140148797533017127373 1397302555799074881422765)
                      ·
                        rfl

theorem cell23_2721237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2721237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721237 prefixEnd_2721237 := by exact prefixLift 2721237
  have htrace : WordTrace (prefixWord ++ tailWord_2721237) baseStart_2721237 baseEnd_2721237 := by
    simpa [prefixWord, tailWord_2721237, baseEnd_2721237] using wordTrace_append hprefix tailTrace_2721237
  have hstable : (prefixWord ++ tailWord_2721237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721237).length < 2 ^ (prefixWord ++ tailWord_2721237).sum := by decide
  have hdescent : baseEnd_2721237 < baseStart_2721237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721263 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_2721263 : Nat := 118140960795 + 2721263 * 2 ^ 59
def prefixEnd_2721263 : Nat := 4983230072969 + 3 ^ 40 * 2721263 * 2
def baseEnd_2721263 : Nat := 1397315906296091779697645

theorem tailTrace_2721263 : CollatzResearch.WordTrace tailWord_2721263 prefixEnd_2721263 1397315906296091779697645 := by
  unfold tailWord_2721263
  simp only [CollatzResearch.WordTrace]
  refine ⟨99252615540336380564496443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66168410360224253709664295 99252615540336380564496443)
  ·
    refine ⟨148878923310504570846744665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99252615540336380564496443 148878923310504570846744665)
    ·
      refine ⟨111659192482878428135058499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148878923310504570846744665 111659192482878428135058499)
      ·
        refine ⟨167488788724317642202587749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111659192482878428135058499 167488788724317642202587749)
        ·
          refine ⟨31404147885809557912985203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167488788724317642202587749 31404147885809557912985203)
          ·
            refine ⟨47106221828714336869477805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31404147885809557912985203 47106221828714336869477805)
            ·
              refine ⟨17664833185767876326054177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47106221828714336869477805 17664833185767876326054177)
              ·
                refine ⟨13248624889325907244540633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17664833185767876326054177 13248624889325907244540633)
                ·
                  refine ⟨9936468666994430433405475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13248624889325907244540633 9936468666994430433405475)
                  ·
                    refine ⟨14904703000491645650108213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9936468666994430433405475 14904703000491645650108213)
                    ·
                      refine ⟨1397315906296091779697645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14904703000491645650108213 1397315906296091779697645)
                      ·
                        rfl

theorem cell23_2721263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_2721263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721263 prefixEnd_2721263 := by exact prefixLift 2721263
  have htrace : WordTrace (prefixWord ++ tailWord_2721263) baseStart_2721263 baseEnd_2721263 := by
    simpa [prefixWord, tailWord_2721263, baseEnd_2721263] using wordTrace_append hprefix tailTrace_2721263
  have hstable : (prefixWord ++ tailWord_2721263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721263).length < 2 ^ (prefixWord ++ tailWord_2721263).sum := by decide
  have hdescent : baseEnd_2721263 < baseStart_2721263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721264 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 1, 3, 2]
def baseStart_2721264 : Nat := 118140960795 + 2721264 * 2 ^ 59
def prefixEnd_2721264 : Nat := 4983230072969 + 3 ^ 40 * 2721264 * 2
def baseEnd_2721264 : Nat := 1397316419776746275785141

theorem tailTrace_2721264 : CollatzResearch.WordTrace tailWord_2721264 prefixEnd_2721264 1397316419776746275785141 := by
  unfold tailWord_2721264
  simp only [CollatzResearch.WordTrace]
  refine ⟨49626326006666378867641423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66168434675555171823521897 49626326006666378867641423)
  ·
    refine ⟨74439489009999568301462135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49626326006666378867641423 74439489009999568301462135)
    ·
      refine ⟨111659233514999352452193203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74439489009999568301462135 111659233514999352452193203)
      ·
        refine ⟨167488850272499028678289805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111659233514999352452193203 167488850272499028678289805)
        ·
          refine ⟨62808318852187135754358677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167488850272499028678289805 62808318852187135754358677)
          ·
            refine ⟨2944139946196271988485563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62808318852187135754358677 2944139946196271988485563)
            ·
              refine ⟨4416209919294407982728345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2944139946196271988485563 4416209919294407982728345)
              ·
                refine ⟨3312157439470805987046259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4416209919294407982728345 3312157439470805987046259)
                ·
                  refine ⟨4968236159206208980569389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312157439470805987046259 4968236159206208980569389)
                  ·
                    refine ⟨1863088559702328367713521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4968236159206208980569389 1863088559702328367713521)
                    ·
                      refine ⟨1397316419776746275785141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863088559702328367713521 1397316419776746275785141)
                      ·
                        rfl

theorem cell23_2721264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 3, 2].length) (baseStart_2721264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721264 prefixEnd_2721264 := by exact prefixLift 2721264
  have htrace : WordTrace (prefixWord ++ tailWord_2721264) baseStart_2721264 baseEnd_2721264 := by
    simpa [prefixWord, tailWord_2721264, baseEnd_2721264] using wordTrace_append hprefix tailTrace_2721264
  have hstable : (prefixWord ++ tailWord_2721264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721264).length < 2 ^ (prefixWord ++ tailWord_2721264).sum := by decide
  have hdescent : baseEnd_2721264 < baseStart_2721264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721273 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2721273 : Nat := 118140960795 + 2721273 * 2 ^ 59
def prefixEnd_2721273 : Nat := 4983230072969 + 3 ^ 40 * 2721273 * 2
def baseEnd_2721273 : Nat := 1397321041102636740572599

theorem tailTrace_2721273 : CollatzResearch.WordTrace tailWord_2721273 prefixEnd_2721273 1397321041102636740572599 := by
  unfold tailWord_2721273
  simp only [CollatzResearch.WordTrace]
  refine ⟨99252980270300152272360473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66168653513533434848240315 99252980270300152272360473)
  ·
    refine ⟨74439735202725114204270355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99252980270300152272360473 74439735202725114204270355)
    ·
      refine ⟨111659602804087671306405533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74439735202725114204270355 111659602804087671306405533)
      ·
        refine ⟨41872351051532876739902075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111659602804087671306405533 41872351051532876739902075)
        ·
          refine ⟨62808526577299315109853113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41872351051532876739902075 62808526577299315109853113)
          ·
            refine ⟨47106394932974486332389835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62808526577299315109853113 47106394932974486332389835)
            ·
              refine ⟨70659592399461729498584753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47106394932974486332389835 70659592399461729498584753)
              ·
                refine ⟨52994694299596297123938565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70659592399461729498584753 52994694299596297123938565)
                ·
                  refine ⟨9936505181174305710738481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52994694299596297123938565 9936505181174305710738481)
                  ·
                    refine ⟨7452378885880729283053861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9936505181174305710738481 7452378885880729283053861)
                    ·
                      refine ⟨1397321041102636740572599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7452378885880729283053861 1397321041102636740572599)
                      ·
                        rfl

theorem cell23_2721273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2721273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721273 prefixEnd_2721273 := by exact prefixLift 2721273
  have htrace : WordTrace (prefixWord ++ tailWord_2721273) baseStart_2721273 baseEnd_2721273 := by
    simpa [prefixWord, tailWord_2721273, baseEnd_2721273] using wordTrace_append hprefix tailTrace_2721273
  have hstable : (prefixWord ++ tailWord_2721273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721273).length < 2 ^ (prefixWord ++ tailWord_2721273).sum := by decide
  have hdescent : baseEnd_2721273 < baseStart_2721273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721277 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 1, 4, 2]
def baseStart_2721277 : Nat := 118140960795 + 2721277 * 2 ^ 59
def prefixEnd_2721277 : Nat := 4983230072969 + 3 ^ 40 * 2721277 * 2
def baseEnd_2721277 : Nat := 1397323095025254724922581

theorem tailTrace_2721277 : CollatzResearch.WordTrace tailWord_2721277 prefixEnd_2721277 1397323095025254724922581 := by
  unfold tailWord_2721277
  simp only [CollatzResearch.WordTrace]
  refine ⟨99253126162285660955506085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66168750774857107303670723 99253126162285660955506085)
  ·
    refine ⟨18609961155428561429157391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99253126162285660955506085 18609961155428561429157391)
    ·
      refine ⟨27914941733142842143736087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18609961155428561429157391 27914941733142842143736087)
      ·
        refine ⟨41872412599714263215604131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27914941733142842143736087 41872412599714263215604131)
        ·
          refine ⟨62808618899571394823406197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41872412599714263215604131 62808618899571394823406197)
          ·
            refine ⟨5888308021834818264694331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62808618899571394823406197 5888308021834818264694331)
            ·
              refine ⟨8832462032752227397041497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5888308021834818264694331 8832462032752227397041497)
              ·
                refine ⟨6624346524564170547781123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8832462032752227397041497 6624346524564170547781123)
                ·
                  refine ⟨9936519786846255821671685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6624346524564170547781123 9936519786846255821671685)
                  ·
                    refine ⟨1863097460033672966563441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9936519786846255821671685 1863097460033672966563441)
                    ·
                      refine ⟨1397323095025254724922581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863097460033672966563441 1397323095025254724922581)
                      ·
                        rfl

theorem cell23_2721277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_2721277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721277 prefixEnd_2721277 := by exact prefixLift 2721277
  have htrace : WordTrace (prefixWord ++ tailWord_2721277) baseStart_2721277 baseEnd_2721277 := by
    simpa [prefixWord, tailWord_2721277, baseEnd_2721277] using wordTrace_append hprefix tailTrace_2721277
  have hstable : (prefixWord ++ tailWord_2721277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721277).length < 2 ^ (prefixWord ++ tailWord_2721277).sum := by decide
  have hdescent : baseEnd_2721277 < baseStart_2721277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721281 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_2721281 : Nat := 118140960795 + 2721281 * 2 ^ 59
def prefixEnd_2721281 : Nat := 4983230072969 + 3 ^ 40 * 2721281 * 2
def baseEnd_2721281 : Nat := 1397325148947872709272563

theorem tailTrace_2721281 : CollatzResearch.WordTrace tailWord_2721281 prefixEnd_2721281 1397325148947872709272563 := by
  unfold tailWord_2721281
  simp only [CollatzResearch.WordTrace]
  refine ⟨99253272054271169638651697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66168848036180779759101131 99253272054271169638651697)
  ·
    refine ⟨74439954040703377228988773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99253272054271169638651697 74439954040703377228988773)
    ·
      refine ⟨13957491382631883230435395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74439954040703377228988773 13957491382631883230435395)
      ·
        refine ⟨20936237073947824845653093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13957491382631883230435395 20936237073947824845653093)
        ·
          refine ⟨3925544451365217158559955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20936237073947824845653093 3925544451365217158559955)
          ·
            refine ⟨5888316677047825737839933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925544451365217158559955 5888316677047825737839933)
            ·
              refine ⟨2208118753892934651689975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5888316677047825737839933 2208118753892934651689975)
              ·
                refine ⟨3312178130839401977534963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208118753892934651689975 3312178130839401977534963)
                ·
                  refine ⟨4968267196259102966302445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312178130839401977534963 4968267196259102966302445)
                  ·
                    refine ⟨1863100198597163612363417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4968267196259102966302445 1863100198597163612363417)
                    ·
                      refine ⟨1397325148947872709272563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863100198597163612363417 1397325148947872709272563)
                      ·
                        rfl

theorem cell23_2721281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_2721281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721281 prefixEnd_2721281 := by exact prefixLift 2721281
  have htrace : WordTrace (prefixWord ++ tailWord_2721281) baseStart_2721281 baseEnd_2721281 := by
    simpa [prefixWord, tailWord_2721281, baseEnd_2721281] using wordTrace_append hprefix tailTrace_2721281
  have hstable : (prefixWord ++ tailWord_2721281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721281).length < 2 ^ (prefixWord ++ tailWord_2721281).sum := by decide
  have hdescent : baseEnd_2721281 < baseStart_2721281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721353 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_2721353 : Nat := 118140960795 + 2721353 * 2 ^ 59
def prefixEnd_2721353 : Nat := 4983230072969 + 3 ^ 40 * 2721353 * 2
def baseEnd_2721353 : Nat := 1397362119554996427572231

theorem tailTrace_2721353 : CollatzResearch.WordTrace tailWord_2721353 prefixEnd_2721353 1397362119554996427572231 := by
  unfold tailWord_2721353
  simp only [CollatzResearch.WordTrace]
  refine ⟨99255898110010325935272713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66170598740006883956848475 99255898110010325935272713)
  ·
    refine ⟨74441923582507744451454535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99255898110010325935272713 74441923582507744451454535)
    ·
      refine ⟨111662885373761616677181803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74441923582507744451454535 111662885373761616677181803)
      ·
        refine ⟨167494328060642425015772705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111662885373761616677181803 167494328060642425015772705)
        ·
          refine ⟨125620746045481818761829529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167494328060642425015772705 125620746045481818761829529)
          ·
            refine ⟨94215559534111364071372147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125620746045481818761829529 94215559534111364071372147)
            ·
              refine ⟨141323339301167046107058221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94215559534111364071372147 141323339301167046107058221)
              ·
                refine ⟨52996252237937642290146833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141323339301167046107058221 52996252237937642290146833)
                ·
                  refine ⟨39747189178453231717610125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52996252237937642290146833 39747189178453231717610125)
                  ·
                    refine ⟨14905195941919961894103797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39747189178453231717610125 14905195941919961894103797)
                    ·
                      refine ⟨1397362119554996427572231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14905195941919961894103797 1397362119554996427572231)
                      ·
                        rfl

theorem cell23_2721353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_2721353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721353 prefixEnd_2721353 := by exact prefixLift 2721353
  have htrace : WordTrace (prefixWord ++ tailWord_2721353) baseStart_2721353 baseEnd_2721353 := by
    simpa [prefixWord, tailWord_2721353, baseEnd_2721353] using wordTrace_append hprefix tailTrace_2721353
  have hstable : (prefixWord ++ tailWord_2721353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721353).length < 2 ^ (prefixWord ++ tailWord_2721353).sum := by decide
  have hdescent : baseEnd_2721353 < baseStart_2721353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721367 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 2, 4, 2]
def baseStart_2721367 : Nat := 118140960795 + 2721367 * 2 ^ 59
def prefixEnd_2721367 : Nat := 4983230072969 + 3 ^ 40 * 2721367 * 2
def baseEnd_2721367 : Nat := 1397369308284159372797167

theorem tailTrace_2721367 : CollatzResearch.WordTrace tailWord_2721367 prefixEnd_2721367 1397369308284159372797167 := by
  unfold tailWord_2721367
  simp only [CollatzResearch.WordTrace]
  refine ⟨99256408731959606326282355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66170939154639737550854903 99256408731959606326282355)
  ·
    refine ⟨148884613097939409489423533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99256408731959606326282355 148884613097939409489423533)
    ·
      refine ⟨55831729911727278558533825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148884613097939409489423533 55831729911727278558533825)
      ·
        refine ⟨41873797433795458918900369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55831729911727278558533825 41873797433795458918900369)
        ·
          refine ⟨31405348075346594189175277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41873797433795458918900369 31405348075346594189175277)
          ·
            refine ⟨11777005528254972820940729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31405348075346594189175277 11777005528254972820940729)
            ·
              refine ⟨8832754146191229615705547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11777005528254972820940729 8832754146191229615705547)
              ·
                refine ⟨13249131219286844423558321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8832754146191229615705547 13249131219286844423558321)
                ·
                  refine ⟨9936848414465133317668741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13249131219286844423558321 9936848414465133317668741)
                  ·
                    refine ⟨1863159077712212497062889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9936848414465133317668741 1863159077712212497062889)
                    ·
                      refine ⟨1397369308284159372797167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863159077712212497062889 1397369308284159372797167)
                      ·
                        rfl

theorem cell23_2721367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_2721367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721367 prefixEnd_2721367 := by exact prefixLift 2721367
  have htrace : WordTrace (prefixWord ++ tailWord_2721367) baseStart_2721367 baseEnd_2721367 := by
    simpa [prefixWord, tailWord_2721367, baseEnd_2721367] using wordTrace_append hprefix tailTrace_2721367
  have hstable : (prefixWord ++ tailWord_2721367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721367).length < 2 ^ (prefixWord ++ tailWord_2721367).sum := by decide
  have hdescent : baseEnd_2721367 < baseStart_2721367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721420 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_2721420 : Nat := 118140960795 + 2721420 * 2 ^ 59
def prefixEnd_2721420 : Nat := 4983230072969 + 3 ^ 40 * 2721420 * 2
def baseEnd_2721420 : Nat := 465798840919615888478141

theorem tailTrace_2721420 : CollatzResearch.WordTrace tailWord_2721420 prefixEnd_2721420 465798840919615888478141 := by
  unfold tailWord_2721420
  simp only [CollatzResearch.WordTrace]
  refine ⟨49629170900383798188980857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66172227867178397585307809 49629170900383798188980857)
  ·
    refine ⟨37221878175287848641735643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49629170900383798188980857 37221878175287848641735643)
    ·
      refine ⟨55832817262931772962603465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37221878175287848641735643 55832817262931772962603465)
      ·
        refine ⟨41874612947198829721952599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55832817262931772962603465 41874612947198829721952599)
        ·
          refine ⟨62811919420798244582928899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41874612947198829721952599 62811919420798244582928899)
          ·
            refine ⟨94217879131197366874393349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62811919420798244582928899 94217879131197366874393349)
            ·
              refine ⟨17665852337099506288948753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94217879131197366874393349 17665852337099506288948753)
              ·
                refine ⟨13249389252824629716711565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17665852337099506288948753 13249389252824629716711565)
                ·
                  refine ⟨4968520969809236143766837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13249389252824629716711565 4968520969809236143766837)
                  ·
                    refine ⟨465798840919615888478141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4968520969809236143766837 465798840919615888478141)
                    ·
                      rfl

theorem cell23_2721420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_2721420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721420 prefixEnd_2721420 := by exact prefixLift 2721420
  have htrace : WordTrace (prefixWord ++ tailWord_2721420) baseStart_2721420 baseEnd_2721420 := by
    simpa [prefixWord, tailWord_2721420, baseEnd_2721420] using wordTrace_append hprefix tailTrace_2721420
  have hstable : (prefixWord ++ tailWord_2721420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721420).length < 2 ^ (prefixWord ++ tailWord_2721420).sum := by decide
  have hdescent : baseEnd_2721420 < baseStart_2721420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721444 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 2, 3, 2]
def baseStart_2721444 : Nat := 118140960795 + 2721444 * 2 ^ 59
def prefixEnd_2721444 : Nat := 4983230072969 + 3 ^ 40 * 2721444 * 2
def baseEnd_2721444 : Nat := 1397408846294555571534313

theorem tailTrace_2721444 : CollatzResearch.WordTrace tailWord_2721444 prefixEnd_2721444 1397408846294555571534313 := by
  unfold tailWord_2721444
  simp only [CollatzResearch.WordTrace]
  refine ⟨49629608576340324238417693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66172811435120432317890257 49629608576340324238417693)
  ·
    refine ⟨18611103216127621589406635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49629608576340324238417693 18611103216127621589406635)
    ·
      refine ⟨27916654824191432384109953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18611103216127621589406635 27916654824191432384109953)
      ·
        refine ⟨20937491118143574288082465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27916654824191432384109953 20937491118143574288082465)
        ·
          refine ⟨15703118338607680716061849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20937491118143574288082465 15703118338607680716061849)
          ·
            refine ⟨11777338753955760537046387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15703118338607680716061849 11777338753955760537046387)
            ·
              refine ⟨17666008130933640805569581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11777338753955760537046387 17666008130933640805569581)
              ·
                refine ⟨6624753049100115302088593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17666008130933640805569581 6624753049100115302088593)
                ·
                  refine ⟨4968564786825086476566445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6624753049100115302088593 4968564786825086476566445)
                  ·
                    refine ⟨1863211795059407428712417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4968564786825086476566445 1863211795059407428712417)
                    ·
                      refine ⟨1397408846294555571534313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863211795059407428712417 1397408846294555571534313)
                      ·
                        rfl

theorem cell23_2721444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_2721444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721444 prefixEnd_2721444 := by exact prefixLift 2721444
  have htrace : WordTrace (prefixWord ++ tailWord_2721444) baseStart_2721444 baseEnd_2721444 := by
    simpa [prefixWord, tailWord_2721444, baseEnd_2721444] using wordTrace_append hprefix tailTrace_2721444
  have hstable : (prefixWord ++ tailWord_2721444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721444).length < 2 ^ (prefixWord ++ tailWord_2721444).sum := by decide
  have hdescent : baseEnd_2721444 < baseStart_2721444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721468 : List Nat := [2, 2, 2, 3, 1, 2, 4, 2, 1, 1, 3]
def baseStart_2721468 : Nat := 118140960795 + 2721468 * 2 ^ 59
def prefixEnd_2721468 : Nat := 4983230072969 + 3 ^ 40 * 2721468 * 2
def baseEnd_2721468 : Nat := 1397421169830263477634203

theorem tailTrace_2721468 : CollatzResearch.WordTrace tailWord_2721468 prefixEnd_2721468 1397421169830263477634203 := by
  unfold tailWord_2721468
  simp only [CollatzResearch.WordTrace]
  refine ⟨49630046252296850287854529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66173395003062467050472705 49630046252296850287854529)
  ·
    refine ⟨37222534689222637715890897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49630046252296850287854529 37222534689222637715890897)
    ·
      refine ⟨27916901016916978286918173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37222534689222637715890897 27916901016916978286918173)
      ·
        refine ⟨10468837881343866857594315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27916901016916978286918173 10468837881343866857594315)
        ·
          refine ⟨15703256822015800286391473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10468837881343866857594315 15703256822015800286391473)
          ·
            refine ⟨11777442616511850214793605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15703256822015800286391473 11777442616511850214793605)
            ·
              refine ⟨2208270490595971915273801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11777442616511850214793605 2208270490595971915273801)
              ·
                refine ⟨1656202867946978936455351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2208270490595971915273801 1656202867946978936455351)
                ·
                  refine ⟨2484304301920468404683027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656202867946978936455351 2484304301920468404683027)
                  ·
                    refine ⟨3726456452880702607024541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2484304301920468404683027 3726456452880702607024541)
                    ·
                      refine ⟨1397421169830263477634203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3726456452880702607024541 1397421169830263477634203)
                      ·
                        rfl

theorem cell23_2721468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_2721468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721468 prefixEnd_2721468 := by exact prefixLift 2721468
  have htrace : WordTrace (prefixWord ++ tailWord_2721468) baseStart_2721468 baseEnd_2721468 := by
    simpa [prefixWord, tailWord_2721468, baseEnd_2721468] using wordTrace_append hprefix tailTrace_2721468
  have hstable : (prefixWord ++ tailWord_2721468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721468).length < 2 ^ (prefixWord ++ tailWord_2721468).sum := by decide
  have hdescent : baseEnd_2721468 < baseStart_2721468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
