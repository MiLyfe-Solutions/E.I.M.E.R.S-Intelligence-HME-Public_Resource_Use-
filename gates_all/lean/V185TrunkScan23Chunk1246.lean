import V185TrunkScan23Chunk1245

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7380575 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_7380575 : Nat := 118140960795 + 7380575 * 2 ^ 59
def prefixEnd_7380575 : Nat := 4983230072969 + 3 ^ 40 * 7380575 * 2
def baseEnd_7380575 : Nat := 3789782481557566200069859

theorem tailTrace_7380575 : CollatzResearch.WordTrace tailWord_7380575 prefixEnd_7380575 3789782481557566200069859 := by
  unfold tailWord_7380575
  simp only [CollatzResearch.WordTrace]
  refine ⟨269191685236444751701431179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179461123490963167800954119 269191685236444751701431179)
  ·
    refine ⟨403787527854667127552146769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269191685236444751701431179 403787527854667127552146769)
    ·
      refine ⟨302840645891000345664110077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403787527854667127552146769 302840645891000345664110077)
      ·
        refine ⟨113565242209125129624041279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302840645891000345664110077 113565242209125129624041279)
        ·
          refine ⟨170347863313687694436061919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113565242209125129624041279 170347863313687694436061919)
          ·
            refine ⟨255521794970531541654092879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170347863313687694436061919 255521794970531541654092879)
            ·
              refine ⟨383282692455797312481139319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255521794970531541654092879 383282692455797312481139319)
              ·
                refine ⟨574924038683695968721708979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383282692455797312481139319 574924038683695968721708979)
                ·
                  refine ⟨862386058025543953082563469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574924038683695968721708979 862386058025543953082563469)
                  ·
                    refine ⟨323394771759578982405961301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 862386058025543953082563469 323394771759578982405961301)
                    ·
                      refine ⟨3789782481557566200069859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 323394771759578982405961301 3789782481557566200069859)
                      ·
                        rfl

theorem cell23_7380575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_7380575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380575 prefixEnd_7380575 := by exact prefixLift 7380575
  have htrace : WordTrace (prefixWord ++ tailWord_7380575) baseStart_7380575 baseEnd_7380575 := by
    simpa [prefixWord, tailWord_7380575, baseEnd_7380575] using wordTrace_append hprefix tailTrace_7380575
  have hstable : (prefixWord ++ tailWord_7380575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380575).length < 2 ^ (prefixWord ++ tailWord_7380575).sum := by decide
  have hdescent : baseEnd_7380575 < baseStart_7380575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380589 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 7]
def baseStart_7380589 : Nat := 118140960795 + 7380589 * 2 ^ 59
def prefixEnd_7380589 : Nat := 4983230072969 + 3 ^ 40 * 7380589 * 2
def baseEnd_7380589 : Nat := 421087741142969905032755

theorem tailTrace_7380589 : CollatzResearch.WordTrace tailWord_7380589 prefixEnd_7380589 421087741142969905032755 := by
  unfold tailWord_7380589
  simp only [CollatzResearch.WordTrace]
  refine ⟨269192195858394032092440821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179461463905596021394960547 269192195858394032092440821)
  ·
    refine ⟨25236768361724440508666327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269192195858394032092440821 25236768361724440508666327)
    ·
      refine ⟨37855152542586660762999491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25236768361724440508666327 37855152542586660762999491)
      ·
        refine ⟨56782728813879991144499237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37855152542586660762999491 56782728813879991144499237)
        ·
          refine ⟨10646761652602498339593607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56782728813879991144499237 10646761652602498339593607)
          ·
            refine ⟨15970142478903747509390411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10646761652602498339593607 15970142478903747509390411)
            ·
              refine ⟨23955213718355621264085617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15970142478903747509390411 23955213718355621264085617)
              ·
                refine ⟨17966410288766715948064213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23955213718355621264085617 17966410288766715948064213)
                ·
                  refine ⟨421087741142969905032755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17966410288766715948064213 421087741142969905032755)
                  ·
                    rfl

theorem cell23_7380589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_7380589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380589 prefixEnd_7380589 := by exact prefixLift 7380589
  have htrace : WordTrace (prefixWord ++ tailWord_7380589) baseStart_7380589 baseEnd_7380589 := by
    simpa [prefixWord, tailWord_7380589, baseEnd_7380589] using wordTrace_append hprefix tailTrace_7380589
  have hstable : (prefixWord ++ tailWord_7380589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380589).length < 2 ^ (prefixWord ++ tailWord_7380589).sum := by decide
  have hdescent : baseEnd_7380589 < baseStart_7380589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380602 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_7380602 : Nat := 118140960795 + 7380602 * 2 ^ 59
def prefixEnd_7380602 : Nat := 4983230072969 + 3 ^ 40 * 7380602 * 2
def baseEnd_7380602 : Nat := 1263265448511745864810745

theorem tailTrace_7380602 : CollatzResearch.WordTrace tailWord_7380602 prefixEnd_7380602 1263265448511745864810745 := by
  unfold tailWord_7380602
  simp only [CollatzResearch.WordTrace]
  refine ⟨67298167501836733828166015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179461780004897956875109373 67298167501836733828166015)
  ·
    refine ⟨100947251252755100742249023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67298167501836733828166015 100947251252755100742249023)
    ·
      refine ⟨151420876879132651113373535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100947251252755100742249023 151420876879132651113373535)
      ·
        refine ⟨227131315318698976670060303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151420876879132651113373535 227131315318698976670060303)
        ·
          refine ⟨340696972978048465005090455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227131315318698976670060303 340696972978048465005090455)
          ·
            refine ⟨511045459467072697507635683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340696972978048465005090455 511045459467072697507635683)
            ·
              refine ⟨766568189200609046261453525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511045459467072697507635683 766568189200609046261453525)
              ·
                refine ⟨17966441934389274521752817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 766568189200609046261453525 17966441934389274521752817)
                ·
                  refine ⟨13474831450791955891314613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17966441934389274521752817 13474831450791955891314613)
                  ·
                    refine ⟨1263265448511745864810745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13474831450791955891314613 1263265448511745864810745)
                    ·
                      rfl

theorem cell23_7380602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_7380602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380602 prefixEnd_7380602 := by exact prefixLift 7380602
  have htrace : WordTrace (prefixWord ++ tailWord_7380602) baseStart_7380602 baseEnd_7380602 := by
    simpa [prefixWord, tailWord_7380602, baseEnd_7380602] using wordTrace_append hprefix tailTrace_7380602
  have hstable : (prefixWord ++ tailWord_7380602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380602).length < 2 ^ (prefixWord ++ tailWord_7380602).sum := by decide
  have hdescent : baseEnd_7380602 < baseStart_7380602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380659 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 3]
def baseStart_7380659 : Nat := 118140960795 + 7380659 * 2 ^ 59
def prefixEnd_7380659 : Nat := 4983230072969 + 3 ^ 40 * 7380659 * 2
def baseEnd_7380659 : Nat := 3789825613932543871419473

theorem tailTrace_7380659 : CollatzResearch.WordTrace tailWord_7380659 prefixEnd_7380659 3789825613932543871419473 := by
  unfold tailWord_7380659
  simp only [CollatzResearch.WordTrace]
  refine ⟨269194748968140434047489031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179463165978760289364992687 269194748968140434047489031)
  ·
    refine ⟨403792123452210651071233547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269194748968140434047489031 403792123452210651071233547)
    ·
      refine ⟨605688185178315976606850321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403792123452210651071233547 605688185178315976606850321)
      ·
        refine ⟨454266138883736982455137741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605688185178315976606850321 454266138883736982455137741)
        ·
          refine ⟨170349802081401368420676653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454266138883736982455137741 170349802081401368420676653)
          ·
            refine ⟨63881175780525513157753745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170349802081401368420676653 63881175780525513157753745)
            ·
              refine ⟨47910881835394134868315309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63881175780525513157753745 47910881835394134868315309)
              ·
                refine ⟨17966580688272800575618241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47910881835394134868315309 17966580688272800575618241)
                ·
                  refine ⟨13474935516204600431713681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17966580688272800575618241 13474935516204600431713681)
                  ·
                    refine ⟨10106201637153450323785261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13474935516204600431713681 10106201637153450323785261)
                    ·
                      refine ⟨3789825613932543871419473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10106201637153450323785261 3789825613932543871419473)
                      ·
                        rfl

theorem cell23_7380659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 3].length) (baseStart_7380659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380659 prefixEnd_7380659 := by exact prefixLift 7380659
  have htrace : WordTrace (prefixWord ++ tailWord_7380659) baseStart_7380659 baseEnd_7380659 := by
    simpa [prefixWord, tailWord_7380659, baseEnd_7380659] using wordTrace_append hprefix tailTrace_7380659
  have hstable : (prefixWord ++ tailWord_7380659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380659).length < 2 ^ (prefixWord ++ tailWord_7380659).sum := by decide
  have hdescent : baseEnd_7380659 < baseStart_7380659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380676 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_7380676 : Nat := 118140960795 + 7380676 * 2 ^ 59
def prefixEnd_7380676 : Nat := 4983230072969 + 3 ^ 40 * 7380676 * 2
def baseEnd_7380676 : Nat := 3789834343103670304906895

theorem tailTrace_7380676 : CollatzResearch.WordTrace tailWord_7380676 prefixEnd_7380676 3789834343103670304906895 := by
  unfold tailWord_7380676
  simp only [CollatzResearch.WordTrace]
  refine ⟨134597684504539422975428941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179463579339385897300571921 134597684504539422975428941)
  ·
    refine ⟨50474131689202283615785853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134597684504539422975428941 50474131689202283615785853)
    ·
      refine ⟨18927799383450856355919695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50474131689202283615785853 18927799383450856355919695)
      ·
        refine ⟨28391699075176284533879543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18927799383450856355919695 28391699075176284533879543)
        ·
          refine ⟨42587548612764426800819315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28391699075176284533879543 42587548612764426800819315)
          ·
            refine ⟨63881322919146640201228973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42587548612764426800819315 63881322919146640201228973)
            ·
              refine ⟨23955496094679990075460865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63881322919146640201228973 23955496094679990075460865)
              ·
                refine ⟨17966622071009992556595649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23955496094679990075460865 17966622071009992556595649)
                ·
                  refine ⟨13474966553257494417446737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17966622071009992556595649 13474966553257494417446737)
                  ·
                    refine ⟨10106224914943120813085053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13474966553257494417446737 10106224914943120813085053)
                    ·
                      refine ⟨3789834343103670304906895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10106224914943120813085053 3789834343103670304906895)
                      ·
                        rfl

theorem cell23_7380676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_7380676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380676 prefixEnd_7380676 := by exact prefixLift 7380676
  have htrace : WordTrace (prefixWord ++ tailWord_7380676) baseStart_7380676 baseEnd_7380676 := by
    simpa [prefixWord, tailWord_7380676, baseEnd_7380676] using wordTrace_append hprefix tailTrace_7380676
  have hstable : (prefixWord ++ tailWord_7380676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380676).length < 2 ^ (prefixWord ++ tailWord_7380676).sum := by decide
  have hdescent : baseEnd_7380676 < baseStart_7380676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380709 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_7380709 : Nat := 118140960795 + 7380709 * 2 ^ 59
def prefixEnd_7380709 : Nat := 4983230072969 + 3 ^ 40 * 7380709 * 2
def baseEnd_7380709 : Nat := 1263283762655089558598081

theorem tailTrace_7380709 : CollatzResearch.WordTrace tailWord_7380709 prefixEnd_7380709 1263283762655089558598081 := by
  unfold tailWord_7380709
  simp only [CollatzResearch.WordTrace]
  refine ⟨269196572617959292586809181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179464381745306195057872787 269196572617959292586809181)
  ·
    refine ⟨100948714731734734720053443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269196572617959292586809181 100948714731734734720053443)
    ·
      refine ⟨151423072097602102080080165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100948714731734734720053443 151423072097602102080080165)
      ·
        refine ⟨28391826018300394140015031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151423072097602102080080165 28391826018300394140015031)
        ·
          refine ⟨42587739027450591210022547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28391826018300394140015031 42587739027450591210022547)
          ·
            refine ⟨63881608541175886815033821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42587739027450591210022547 63881608541175886815033821)
            ·
              refine ⟨23955603202940957555637683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63881608541175886815033821 23955603202940957555637683)
              ·
                refine ⟨35933404804411436333456525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23955603202940957555637683 35933404804411436333456525)
                ·
                  refine ⟨13475026801654288625046197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35933404804411436333456525 13475026801654288625046197)
                  ·
                    refine ⟨1263283762655089558598081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13475026801654288625046197 1263283762655089558598081)
                    ·
                      rfl

theorem cell23_7380709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_7380709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380709 prefixEnd_7380709 := by exact prefixLift 7380709
  have htrace : WordTrace (prefixWord ++ tailWord_7380709) baseStart_7380709 baseEnd_7380709 := by
    simpa [prefixWord, tailWord_7380709, baseEnd_7380709] using wordTrace_append hprefix tailTrace_7380709
  have hstable : (prefixWord ++ tailWord_7380709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380709).length < 2 ^ (prefixWord ++ tailWord_7380709).sum := by decide
  have hdescent : baseEnd_7380709 < baseStart_7380709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380716 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 2, 3, 2]
def baseStart_7380716 : Nat := 118140960795 + 7380716 * 2 ^ 59
def prefixEnd_7380716 : Nat := 4983230072969 + 3 ^ 40 * 7380716 * 2
def baseEnd_7380716 : Nat := 3789854882329850148406711

theorem tailTrace_7380716 : CollatzResearch.WordTrace tailWord_7380716 prefixEnd_7380716 3789854882329850148406711 := by
  unfold tailWord_7380716
  simp only [CollatzResearch.WordTrace]
  refine ⟨134598413964466966391157001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179464551952622621854876001 134598413964466966391157001)
  ·
    refine ⟨100948810473350224793367751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134598413964466966391157001 100948810473350224793367751)
    ·
      refine ⟨151423215710025337190051627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100948810473350224793367751 151423215710025337190051627)
      ·
        refine ⟨227134823565038005785077441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151423215710025337190051627 227134823565038005785077441)
        ·
          refine ⟨170351117673778504338808081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227134823565038005785077441 170351117673778504338808081)
          ·
            refine ⟨127763338255333878254106061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170351117673778504338808081 127763338255333878254106061)
            ·
              refine ⟨47911251845750204345289773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127763338255333878254106061 47911251845750204345289773)
              ·
                refine ⟨17966719442156326629483665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47911251845750204345289773 17966719442156326629483665)
                ·
                  refine ⟨13475039581617244972112749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17966719442156326629483665 13475039581617244972112749)
                  ·
                    refine ⟨5053139843106466864542281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13475039581617244972112749 5053139843106466864542281)
                    ·
                      refine ⟨3789854882329850148406711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053139843106466864542281 3789854882329850148406711)
                      ·
                        rfl

theorem cell23_7380716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_7380716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380716 prefixEnd_7380716 := by exact prefixLift 7380716
  have htrace : WordTrace (prefixWord ++ tailWord_7380716) baseStart_7380716 baseEnd_7380716 := by
    simpa [prefixWord, tailWord_7380716, baseEnd_7380716] using wordTrace_append hprefix tailTrace_7380716
  have hstable : (prefixWord ++ tailWord_7380716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380716).length < 2 ^ (prefixWord ++ tailWord_7380716).sum := by decide
  have hdescent : baseEnd_7380716 < baseStart_7380716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380734 : List Nat := [4, 2, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_7380734 : Nat := 118140960795 + 7380734 * 2 ^ 59
def prefixEnd_7380734 : Nat := 4983230072969 + 3 ^ 40 * 7380734 * 2
def baseEnd_7380734 : Nat := 1263288041660543692660543

theorem tailTrace_7380734 : CollatzResearch.WordTrace tailWord_7380734 prefixEnd_7380734 1263288041660543692660543 := by
  unfold tailWord_7380734
  simp only [CollatzResearch.WordTrace]
  refine ⟨33649685555358590232058657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179464989628579147904312837 33649685555358590232058657)
  ·
    refine ⟨25237264166518942674043993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33649685555358590232058657 25237264166518942674043993)
    ·
      refine ⟨18927948124889207005532995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25237264166518942674043993 18927948124889207005532995)
      ·
        refine ⟨28391922187333810508299493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18927948124889207005532995 28391922187333810508299493)
        ·
          refine ⟨5323485410125089470306155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28391922187333810508299493 5323485410125089470306155)
          ·
            refine ⟨7985228115187634205459233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323485410125089470306155 7985228115187634205459233)
            ·
              refine ⟨5988921086390725654094425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7985228115187634205459233 5988921086390725654094425)
              ·
                refine ⟨4491690814793044240570819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988921086390725654094425 4491690814793044240570819)
                ·
                  refine ⟨6737536222189566360856229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491690814793044240570819 6737536222189566360856229)
                  ·
                    refine ⟨1263288041660543692660543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6737536222189566360856229 1263288041660543692660543)
                    ·
                      rfl

theorem cell23_7380734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_7380734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380734 prefixEnd_7380734 := by exact prefixLift 7380734
  have htrace : WordTrace (prefixWord ++ tailWord_7380734) baseStart_7380734 baseEnd_7380734 := by
    simpa [prefixWord, tailWord_7380734, baseEnd_7380734] using wordTrace_append hprefix tailTrace_7380734
  have hstable : (prefixWord ++ tailWord_7380734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380734).length < 2 ^ (prefixWord ++ tailWord_7380734).sum := by decide
  have hdescent : baseEnd_7380734 < baseStart_7380734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380739 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 4, 4]
def baseStart_7380739 : Nat := 118140960795 + 7380739 * 2 ^ 59
def prefixEnd_7380739 : Nat := 4983230072969 + 3 ^ 40 * 7380739 * 2
def baseEnd_7380739 : Nat := 1263288897461634519473035

theorem tailTrace_7380739 : CollatzResearch.WordTrace tailWord_7380739 prefixEnd_7380739 1263288897461634519473035 := by
  unfold tailWord_7380739
  simp only [CollatzResearch.WordTrace]
  refine ⟨269197666807850607710401271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179465111205233738473600847 269197666807850607710401271)
  ·
    refine ⟨403796500211775911565601907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269197666807850607710401271 403796500211775911565601907)
    ·
      refine ⟨605694750317663867348402861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403796500211775911565601907 605694750317663867348402861)
      ·
        refine ⟨227135531369123950255651073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605694750317663867348402861 227135531369123950255651073)
        ·
          refine ⟨170351648526842962691738305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227135531369123950255651073 170351648526842962691738305)
          ·
            refine ⟨127763736395132222018803729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170351648526842962691738305 127763736395132222018803729)
            ·
              refine ⟨95822802296349166514102797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127763736395132222018803729 95822802296349166514102797)
              ·
                refine ⟨35933550861130937442788549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95822802296349166514102797 35933550861130937442788549)
                ·
                  refine ⟨6737540786462050770522853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35933550861130937442788549 6737540786462050770522853)
                  ·
                    refine ⟨1263288897461634519473035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6737540786462050770522853 1263288897461634519473035)
                    ·
                      rfl

theorem cell23_7380739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 4].length) (baseStart_7380739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380739 prefixEnd_7380739 := by exact prefixLift 7380739
  have htrace : WordTrace (prefixWord ++ tailWord_7380739) baseStart_7380739 baseEnd_7380739 := by
    simpa [prefixWord, tailWord_7380739, baseEnd_7380739] using wordTrace_append hprefix tailTrace_7380739
  have hstable : (prefixWord ++ tailWord_7380739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380739).length < 2 ^ (prefixWord ++ tailWord_7380739).sum := by decide
  have hdescent : baseEnd_7380739 < baseStart_7380739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380740 : List Nat := [2, 3, 2, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_7380740 : Nat := 118140960795 + 7380740 * 2 ^ 59
def prefixEnd_7380740 : Nat := 4983230072969 + 3 ^ 40 * 7380740 * 2
def baseEnd_7380740 : Nat := 3789867205865558054506601

theorem tailTrace_7380740 : CollatzResearch.WordTrace tailWord_7380740 prefixEnd_7380740 3789867205865558054506601 := by
  unfold tailWord_7380740
  simp only [CollatzResearch.WordTrace]
  refine ⟨134598851640423492440593837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179465135520564656587458449 134598851640423492440593837)
  ·
    refine ⟨50474569365158809665222689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134598851640423492440593837 50474569365158809665222689)
    ·
      refine ⟨37855927023869107248917017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50474569365158809665222689 37855927023869107248917017)
      ·
        refine ⟨28391945267901830436687763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37855927023869107248917017 28391945267901830436687763)
        ·
          refine ⟨42587917901852745655031645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28391945267901830436687763 42587917901852745655031645)
          ·
            refine ⟨15970469213194779620636867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42587917901852745655031645 15970469213194779620636867)
            ·
              refine ⟨23955703819792169430955301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15970469213194779620636867 23955703819792169430955301)
              ·
                refine ⟨4491694466211031768304119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23955703819792169430955301 4491694466211031768304119)
                ·
                  refine ⟨6737541699316547652456179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491694466211031768304119 6737541699316547652456179)
                  ·
                    refine ⟨10106312548974821478684269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6737541699316547652456179 10106312548974821478684269)
                    ·
                      refine ⟨3789867205865558054506601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10106312548974821478684269 3789867205865558054506601)
                      ·
                        rfl

theorem cell23_7380740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_7380740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380740 prefixEnd_7380740 := by exact prefixLift 7380740
  have htrace : WordTrace (prefixWord ++ tailWord_7380740) baseStart_7380740 baseEnd_7380740 := by
    simpa [prefixWord, tailWord_7380740, baseEnd_7380740] using wordTrace_append hprefix tailTrace_7380740
  have hstable : (prefixWord ++ tailWord_7380740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380740).length < 2 ^ (prefixWord ++ tailWord_7380740).sum := by decide
  have hdescent : baseEnd_7380740 < baseStart_7380740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380776 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_7380776 : Nat := 118140960795 + 7380776 * 2 ^ 59
def prefixEnd_7380776 : Nat := 4983230072969 + 3 ^ 40 * 7380776 * 2
def baseEnd_7380776 : Nat := 3789885691169119913656435

theorem tailTrace_7380776 : CollatzResearch.WordTrace tailWord_7380776 prefixEnd_7380776 3789885691169119913656435 := by
  unfold tailWord_7380776
  simp only [CollatzResearch.WordTrace]
  refine ⟨134599508154358281514749091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179466010872477708686332121 134599508154358281514749091)
  ·
    refine ⟨201899262231537422272123637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134599508154358281514749091 201899262231537422272123637)
    ·
      refine ⟨18928055834206633338011591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201899262231537422272123637 18928055834206633338011591)
      ·
        refine ⟨28392083751309950007017387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18928055834206633338011591 28392083751309950007017387)
        ·
          refine ⟨42588125626964925010526081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28392083751309950007017387 42588125626964925010526081)
          ·
            refine ⟨31941094220223693757894561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42588125626964925010526081 31941094220223693757894561)
            ·
              refine ⟨23955820665167770318420921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31941094220223693757894561 23955820665167770318420921)
              ·
                refine ⟨17966865498875827738815691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23955820665167770318420921 17966865498875827738815691)
                ·
                  refine ⟨26950298248313741608223537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17966865498875827738815691 26950298248313741608223537)
                  ·
                    refine ⟨20212723686235306206167653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26950298248313741608223537 20212723686235306206167653)
                    ·
                      refine ⟨3789885691169119913656435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20212723686235306206167653 3789885691169119913656435)
                      ·
                        rfl

theorem cell23_7380776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_7380776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380776 prefixEnd_7380776 := by exact prefixLift 7380776
  have htrace : WordTrace (prefixWord ++ tailWord_7380776) baseStart_7380776 baseEnd_7380776 := by
    simpa [prefixWord, tailWord_7380776, baseEnd_7380776] using wordTrace_append hprefix tailTrace_7380776
  have hstable : (prefixWord ++ tailWord_7380776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380776).length < 2 ^ (prefixWord ++ tailWord_7380776).sum := by decide
  have hdescent : baseEnd_7380776 < baseStart_7380776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380780 : List Nat := [2, 2, 1, 1, 1, 5, 1, 5, 1, 2, 2]
def baseStart_7380780 : Nat := 118140960795 + 7380780 * 2 ^ 59
def prefixEnd_7380780 : Nat := 4983230072969 + 3 ^ 40 * 7380780 * 2
def baseEnd_7380780 : Nat := 3789887745091737898006417

theorem tailTrace_7380780 : CollatzResearch.WordTrace tailWord_7380780 prefixEnd_7380780 3789887745091737898006417 := by
  unfold tailWord_7380780
  simp only [CollatzResearch.WordTrace]
  refine ⟨134599581100351035856321897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179466108133801381141762529 134599581100351035856321897)
  ·
    refine ⟨100949685825263276892241423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134599581100351035856321897 100949685825263276892241423)
    ·
      refine ⟨151424528737894915338362135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100949685825263276892241423 151424528737894915338362135)
      ·
        refine ⟨227136793106842373007543203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151424528737894915338362135 227136793106842373007543203)
        ·
          refine ⟨340705189660263559511314805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227136793106842373007543203 340705189660263559511314805)
          ·
            refine ⟨31941111530649708704185763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 340705189660263559511314805 31941111530649708704185763)
            ·
              refine ⟨47911667295974563056278645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31941111530649708704185763 47911667295974563056278645)
              ·
                refine ⟨4491718808997615286526123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47911667295974563056278645 4491718808997615286526123)
                ·
                  refine ⟨6737578213496422929789185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491718808997615286526123 6737578213496422929789185)
                  ·
                    refine ⟨5053183660122317197341889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6737578213496422929789185 5053183660122317197341889)
                    ·
                      refine ⟨3789887745091737898006417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053183660122317197341889 3789887745091737898006417)
                      ·
                        rfl

theorem cell23_7380780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 1, 2, 2].length) (baseStart_7380780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380780 prefixEnd_7380780 := by exact prefixLift 7380780
  have htrace : WordTrace (prefixWord ++ tailWord_7380780) baseStart_7380780 baseEnd_7380780 := by
    simpa [prefixWord, tailWord_7380780, baseEnd_7380780] using wordTrace_append hprefix tailTrace_7380780
  have hstable : (prefixWord ++ tailWord_7380780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380780).length < 2 ^ (prefixWord ++ tailWord_7380780).sum := by decide
  have hdescent : baseEnd_7380780 < baseStart_7380780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380790 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_7380790 : Nat := 118140960795 + 7380790 * 2 ^ 59
def prefixEnd_7380790 : Nat := 4983230072969 + 3 ^ 40 * 7380790 * 2
def baseEnd_7380790 : Nat := 1263297626632760952960457

theorem tailTrace_7380790 : CollatzResearch.WordTrace tailWord_7380790 prefixEnd_7380790 1263297626632760952960457 := by
  unfold tailWord_7380790
  simp only [CollatzResearch.WordTrace]
  refine ⟨16824970433166615213781739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179466351287110562280338549 16824970433166615213781739)
  ·
    refine ⟨25237455649749922820672609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16824970433166615213781739 25237455649749922820672609)
    ·
      refine ⟨18928091737312442115504457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25237455649749922820672609 18928091737312442115504457)
      ·
        refine ⟨14196068802984331586628343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18928091737312442115504457 14196068802984331586628343)
        ·
          refine ⟨21294103204476497379942515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14196068802984331586628343 21294103204476497379942515)
          ·
            refine ⟨31941154806714746069913773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21294103204476497379942515 31941154806714746069913773)
            ·
              refine ⟨11977933052518029776217665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31941154806714746069913773 11977933052518029776217665)
              ·
                refine ⟨8983449789388522332163249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11977933052518029776217665 8983449789388522332163249)
                ·
                  refine ⟨6737587342041391749122437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8983449789388522332163249 6737587342041391749122437)
                  ·
                    refine ⟨1263297626632760952960457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6737587342041391749122437 1263297626632760952960457)
                    ·
                      rfl

theorem cell23_7380790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_7380790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380790 prefixEnd_7380790 := by exact prefixLift 7380790
  have htrace : WordTrace (prefixWord ++ tailWord_7380790) baseStart_7380790 baseEnd_7380790 := by
    simpa [prefixWord, tailWord_7380790, baseEnd_7380790] using wordTrace_append hprefix tailTrace_7380790
  have hstable : (prefixWord ++ tailWord_7380790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380790).length < 2 ^ (prefixWord ++ tailWord_7380790).sum := by decide
  have hdescent : baseEnd_7380790 < baseStart_7380790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380797 : List Nat := [1, 4, 1, 4, 1, 1, 2, 4, 1, 2, 2]
def baseStart_7380797 : Nat := 118140960795 + 7380797 * 2 ^ 59
def prefixEnd_7380797 : Nat := 4983230072969 + 3 ^ 40 * 7380797 * 2
def baseEnd_7380797 : Nat := 3789896474262864331493839

theorem tailTrace_7380797 : CollatzResearch.WordTrace tailWord_7380797 prefixEnd_7380797 3789896474262864331493839 := by
  unfold tailWord_7380797
  simp only [CollatzResearch.WordTrace]
  refine ⟨269199782241640483616012645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179466521494426989077341763 269199782241640483616012645)
  ·
    refine ⟨50474959170307590678002371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269199782241640483616012645 50474959170307590678002371)
    ·
      refine ⟨75712438755461386017003557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50474959170307590678002371 75712438755461386017003557)
      ·
        refine ⟨14196082266649009878188167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75712438755461386017003557 14196082266649009878188167)
        ·
          refine ⟨21294123399973514817282251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14196082266649009878188167 21294123399973514817282251)
          ·
            refine ⟨31941185099960272225923377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21294123399973514817282251 31941185099960272225923377)
            ·
              refine ⟨23955888824970204169442533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31941185099960272225923377 23955888824970204169442533)
              ·
                refine ⟨4491729154681913281770475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23955888824970204169442533 4491729154681913281770475)
                ·
                  refine ⟨6737593732022869922655713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491729154681913281770475 6737593732022869922655713)
                  ·
                    refine ⟨5053195299017152441991785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6737593732022869922655713 5053195299017152441991785)
                    ·
                      refine ⟨3789896474262864331493839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053195299017152441991785 3789896474262864331493839)
                      ·
                        rfl

theorem cell23_7380797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_7380797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380797 prefixEnd_7380797 := by exact prefixLift 7380797
  have htrace : WordTrace (prefixWord ++ tailWord_7380797) baseStart_7380797 baseEnd_7380797 := by
    simpa [prefixWord, tailWord_7380797, baseEnd_7380797] using wordTrace_append hprefix tailTrace_7380797
  have hstable : (prefixWord ++ tailWord_7380797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380797).length < 2 ^ (prefixWord ++ tailWord_7380797).sum := by decide
  have hdescent : baseEnd_7380797 < baseStart_7380797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380874 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2]
def baseStart_7380874 : Nat := 118140960795 + 7380874 * 2 ^ 59
def prefixEnd_7380874 : Nat := 4983230072969 + 3 ^ 40 * 7380874 * 2
def baseEnd_7380874 : Nat := 3789936012273260530230985

theorem tailTrace_7380874 : CollatzResearch.WordTrace tailWord_7380874 prefixEnd_7380874 3789936012273260530230985 := by
  unfold tailWord_7380874
  simp only [CollatzResearch.WordTrace]
  refine ⟨67300647665590381441641419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179468393774907683844377117 67300647665590381441641419)
  ·
    refine ⟨100950971498385572162462129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67300647665590381441641419 100950971498385572162462129)
    ·
      refine ⟨75713228623789179121846597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100950971498385572162462129 75713228623789179121846597)
      ·
        refine ⟨14196230366960471085346237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75713228623789179121846597 14196230366960471085346237)
        ·
          refine ⟨5323586387610176657004839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14196230366960471085346237 5323586387610176657004839)
          ·
            refine ⟨7985379581415264985507259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323586387610176657004839 7985379581415264985507259)
            ·
              refine ⟨11978069372122897478260889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7985379581415264985507259 11978069372122897478260889)
              ·
                refine ⟨8983552029092173108695667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11978069372122897478260889 8983552029092173108695667)
                ·
                  refine ⟨13475328043638259663043501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8983552029092173108695667 13475328043638259663043501)
                  ·
                    refine ⟨5053248016364347373641313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13475328043638259663043501 5053248016364347373641313)
                    ·
                      refine ⟨3789936012273260530230985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053248016364347373641313 3789936012273260530230985)
                      ·
                        rfl

theorem cell23_7380874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_7380874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380874 prefixEnd_7380874 := by exact prefixLift 7380874
  have htrace : WordTrace (prefixWord ++ tailWord_7380874) baseStart_7380874 baseEnd_7380874 := by
    simpa [prefixWord, tailWord_7380874, baseEnd_7380874] using wordTrace_append hprefix tailTrace_7380874
  have hstable : (prefixWord ++ tailWord_7380874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380874).length < 2 ^ (prefixWord ++ tailWord_7380874).sum := by decide
  have hdescent : baseEnd_7380874 < baseStart_7380874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380889 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 1, 7]
def baseStart_7380889 : Nat := 118140960795 + 7380889 * 2 ^ 59
def prefixEnd_7380889 : Nat := 4983230072969 + 3 ^ 40 * 7380889 * 2
def baseEnd_7380889 : Nat := 1263314571494359323847805

theorem tailTrace_7380889 : CollatzResearch.WordTrace tailWord_7380889 prefixEnd_7380889 1263314571494359323847805 := by
  unfold tailWord_7380889
  simp only [CollatzResearch.WordTrace]
  refine ⟨269203137757307183328361721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179468758504871455552241147 269203137757307183328361721)
  ·
    refine ⟨201902353317980387496271291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269203137757307183328361721 201902353317980387496271291)
    ·
      refine ⟨302853529976970581244406937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201902353317980387496271291 302853529976970581244406937)
      ·
        refine ⟨227140147482727935933305203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302853529976970581244406937 227140147482727935933305203)
        ·
          refine ⟨340710221224091903899957805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227140147482727935933305203 340710221224091903899957805)
          ·
            refine ⟨127766332959034463962484177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340710221224091903899957805 127766332959034463962484177)
            ·
              refine ⟨95824749719275847971863133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127766332959034463962484177 95824749719275847971863133)
              ·
                refine ⟨35934281144728442989448675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95824749719275847971863133 35934281144728442989448675)
                ·
                  refine ⟨53901421717092664484173013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35934281144728442989448675 53901421717092664484173013)
                  ·
                    refine ⟨1263314571494359323847805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53901421717092664484173013 1263314571494359323847805)
                    ·
                      rfl

theorem cell23_7380889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_7380889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380889 prefixEnd_7380889 := by exact prefixLift 7380889
  have htrace : WordTrace (prefixWord ++ tailWord_7380889) baseStart_7380889 baseEnd_7380889 := by
    simpa [prefixWord, tailWord_7380889, baseEnd_7380889] using wordTrace_append hprefix tailTrace_7380889
  have hstable : (prefixWord ++ tailWord_7380889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380889).length < 2 ^ (prefixWord ++ tailWord_7380889).sum := by decide
  have hdescent : baseEnd_7380889 < baseStart_7380889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380913 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 2, 5, 2]
def baseStart_7380913 : Nat := 118140960795 + 7380913 * 2 ^ 59
def prefixEnd_7380913 : Nat := 4983230072969 + 3 ^ 40 * 7380913 * 2
def baseEnd_7380913 : Nat := 3789956038018785877643305

theorem tailTrace_7380913 : CollatzResearch.WordTrace tailWord_7380913 prefixEnd_7380913 3789956038018785877643305 := by
  unfold tailWord_7380913
  simp only [CollatzResearch.WordTrace]
  refine ⟨269204013109220235427235393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179469342072813490284823595 269204013109220235427235393)
  ·
    refine ⟨201903009831915176570426545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269204013109220235427235393 201903009831915176570426545)
    ·
      refine ⟨151427257373936382427819909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201903009831915176570426545 151427257373936382427819909)
      ·
        refine ⟨28392610757613071705216233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151427257373936382427819909 28392610757613071705216233)
        ·
          refine ⟨21294458068209803778912175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28392610757613071705216233 21294458068209803778912175)
          ·
            refine ⟨31941687102314705668368263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21294458068209803778912175 31941687102314705668368263)
            ·
              refine ⟨47912530653472058502552395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31941687102314705668368263 47912530653472058502552395)
              ·
                refine ⟨71868795980208087753828593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47912530653472058502552395 71868795980208087753828593)
                ·
                  refine ⟨53901596985156065815371445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71868795980208087753828593 53901596985156065815371445)
                  ·
                    refine ⟨5053274717358381170191073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53901596985156065815371445 5053274717358381170191073)
                    ·
                      refine ⟨3789956038018785877643305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053274717358381170191073 3789956038018785877643305)
                      ·
                        rfl

theorem cell23_7380913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_7380913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380913 prefixEnd_7380913 := by exact prefixLift 7380913
  have htrace : WordTrace (prefixWord ++ tailWord_7380913) baseStart_7380913 baseEnd_7380913 := by
    simpa [prefixWord, tailWord_7380913, baseEnd_7380913] using wordTrace_append hprefix tailTrace_7380913
  have hstable : (prefixWord ++ tailWord_7380913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380913).length < 2 ^ (prefixWord ++ tailWord_7380913).sum := by decide
  have hdescent : baseEnd_7380913 < baseStart_7380913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380919 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 2, 8]
def baseStart_7380919 : Nat := 118140960795 + 7380919 * 2 ^ 59
def prefixEnd_7380919 : Nat := 4983230072969 + 3 ^ 40 * 7380919 * 2
def baseEnd_7380919 : Nat := 1263319706300904284722759

theorem tailTrace_7380919 : CollatzResearch.WordTrace tailWord_7380919 prefixEnd_7380919 1263319706300904284722759 := by
  unfold tailWord_7380919
  simp only [CollatzResearch.WordTrace]
  refine ⟨269204231947198498451953811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179469487964798998967969207 269204231947198498451953811)
  ·
    refine ⟨403806347920797747677930717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269204231947198498451953811 403806347920797747677930717)
    ·
      refine ⟨151427380470299155379224019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403806347920797747677930717 151427380470299155379224019)
      ·
        refine ⟨227141070705448733068836029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151427380470299155379224019 227141070705448733068836029)
        ·
          refine ⟨85177901514543274900813511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227141070705448733068836029 85177901514543274900813511)
          ·
            refine ⟨127766852271814912351220267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85177901514543274900813511 127766852271814912351220267)
            ·
              refine ⟨191650278407722368526830401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127766852271814912351220267 191650278407722368526830401)
              ·
                refine ⟨143737708805791776395122801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191650278407722368526830401 143737708805791776395122801)
                ·
                  refine ⟨107803281604343832296342101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143737708805791776395122801 107803281604343832296342101)
                  ·
                    refine ⟨1263319706300904284722759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107803281604343832296342101 1263319706300904284722759)
                    ·
                      rfl

theorem cell23_7380919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_7380919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380919 prefixEnd_7380919 := by exact prefixLift 7380919
  have htrace : WordTrace (prefixWord ++ tailWord_7380919) baseStart_7380919 baseEnd_7380919 := by
    simpa [prefixWord, tailWord_7380919, baseEnd_7380919] using wordTrace_append hprefix tailTrace_7380919
  have hstable : (prefixWord ++ tailWord_7380919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380919).length < 2 ^ (prefixWord ++ tailWord_7380919).sum := by decide
  have hdescent : baseEnd_7380919 < baseStart_7380919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7380970 : List Nat := [3, 1, 3, 1, 2, 1, 1, 6, 1, 4]
def baseStart_7380970 : Nat := 118140960795 + 7380970 * 2 ^ 59
def prefixEnd_7380970 : Nat := 4983230072969 + 3 ^ 40 * 7380970 * 2
def baseEnd_7380970 : Nat := 1263328435472030718210181

theorem tailTrace_7380970 : CollatzResearch.WordTrace tailWord_7380970 prefixEnd_7380970 1263328435472030718210181 := by
  unfold tailWord_7380970
  simp only [CollatzResearch.WordTrace]
  refine ⟨67301523017503433540515091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179470728046675822774706909 67301523017503433540515091)
  ·
    refine ⟨100952284526255150310772637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67301523017503433540515091 100952284526255150310772637)
    ·
      refine ⟨37857106697345681366539739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100952284526255150310772637 37857106697345681366539739)
      ·
        refine ⟨56785660046018522049809609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37857106697345681366539739 56785660046018522049809609)
        ·
          refine ⟨42589245034513891537357207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56785660046018522049809609 42589245034513891537357207)
          ·
            refine ⟨63883867551770837306035811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42589245034513891537357207 63883867551770837306035811)
            ·
              refine ⟨95825801327656255959053717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63883867551770837306035811 95825801327656255959053717)
              ·
                refine ⟨4491834437233886998080643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95825801327656255959053717 4491834437233886998080643)
                ·
                  refine ⟨6737751655850830497120965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491834437233886998080643 6737751655850830497120965)
                  ·
                    refine ⟨1263328435472030718210181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6737751655850830497120965 1263328435472030718210181)
                    ·
                      rfl

theorem cell23_7380970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_7380970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7380970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7380970 prefixEnd_7380970 := by exact prefixLift 7380970
  have htrace : WordTrace (prefixWord ++ tailWord_7380970) baseStart_7380970 baseEnd_7380970 := by
    simpa [prefixWord, tailWord_7380970, baseEnd_7380970] using wordTrace_append hprefix tailTrace_7380970
  have hstable : (prefixWord ++ tailWord_7380970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7380970).length < 2 ^ (prefixWord ++ tailWord_7380970).sum := by decide
  have hdescent : baseEnd_7380970 < baseStart_7380970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7380970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381003 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 1, 5, 2]
def baseStart_7381003 : Nat := 118140960795 + 7381003 * 2 ^ 59
def prefixEnd_7381003 : Nat := 4983230072969 + 3 ^ 40 * 7381003 * 2
def baseEnd_7381003 : Nat := 3790002251277690525517891

theorem tailTrace_7381003 : CollatzResearch.WordTrace tailWord_7381003 prefixEnd_7381003 3790002251277690525517891 := by
  unfold tailWord_7381003
  simp only [CollatzResearch.WordTrace]
  refine ⟨269207295678894180798011663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179471530452596120532007775 269207295678894180798011663)
  ·
    refine ⟨403810943518341271197017495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269207295678894180798011663 403810943518341271197017495)
    ·
      refine ⟨605716415277511906795526243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403810943518341271197017495 605716415277511906795526243)
      ·
        refine ⟨908574622916267860193289365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605716415277511906795526243 908574622916267860193289365)
        ·
          refine ⟨42589435449200055946560439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 908574622916267860193289365 42589435449200055946560439)
          ·
            refine ⟨63884153173800083919840659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42589435449200055946560439 63884153173800083919840659)
            ·
              refine ⟨95826229760700125879760989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63884153173800083919840659 95826229760700125879760989)
              ·
                refine ⟨35934836160262547204910371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95826229760700125879760989 35934836160262547204910371)
                ·
                  refine ⟨53902254240393820807365557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35934836160262547204910371 53902254240393820807365557)
                  ·
                    refine ⟨5053336335036920700690521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53902254240393820807365557 5053336335036920700690521)
                    ·
                      refine ⟨3790002251277690525517891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053336335036920700690521 3790002251277690525517891)
                      ·
                        rfl

theorem cell23_7381003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 5, 2].length) (baseStart_7381003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381003 prefixEnd_7381003 := by exact prefixLift 7381003
  have htrace : WordTrace (prefixWord ++ tailWord_7381003) baseStart_7381003 baseEnd_7381003 := by
    simpa [prefixWord, tailWord_7381003, baseEnd_7381003] using wordTrace_append hprefix tailTrace_7381003
  have hstable : (prefixWord ++ tailWord_7381003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381003).length < 2 ^ (prefixWord ++ tailWord_7381003).sum := by decide
  have hdescent : baseEnd_7381003 < baseStart_7381003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381020 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_7381020 : Nat := 118140960795 + 7381020 * 2 ^ 59
def prefixEnd_7381020 : Nat := 4983230072969 + 3 ^ 40 * 7381020 * 2
def baseEnd_7381020 : Nat := 3790010980448816959005313

theorem tailTrace_7381020 : CollatzResearch.WordTrace tailWord_7381020 prefixEnd_7381020 3790010980448816959005313 := by
  unfold tailWord_7381020
  simp only [CollatzResearch.WordTrace]
  refine ⟨134603957859916296350690257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179471943813221728467587009 134603957859916296350690257)
  ·
    refine ⟨100952968394937222263017693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134603957859916296350690257 100952968394937222263017693)
    ·
      refine ⟨37857363148101458348631635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100952968394937222263017693 37857363148101458348631635)
      ·
        refine ⟨56786044722152187522947453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37857363148101458348631635 56786044722152187522947453)
        ·
          refine ⟨21294766770807070321105295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56786044722152187522947453 21294766770807070321105295)
          ·
            refine ⟨31942150156210605481657943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21294766770807070321105295 31942150156210605481657943)
            ·
              refine ⟨47913225234315908222486915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31942150156210605481657943 47913225234315908222486915)
              ·
                refine ⟨71869837851473862333730373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47913225234315908222486915 71869837851473862333730373)
                ·
                  refine ⟨13475594597151349187574445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71869837851473862333730373 13475594597151349187574445)
                  ·
                    refine ⟨5053347973931755945340417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13475594597151349187574445 5053347973931755945340417)
                    ·
                      refine ⟨3790010980448816959005313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053347973931755945340417 3790010980448816959005313)
                      ·
                        rfl

theorem cell23_7381020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_7381020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381020 prefixEnd_7381020 := by exact prefixLift 7381020
  have htrace : WordTrace (prefixWord ++ tailWord_7381020) baseStart_7381020 baseEnd_7381020 := by
    simpa [prefixWord, tailWord_7381020, baseEnd_7381020] using wordTrace_append hprefix tailTrace_7381020
  have hstable : (prefixWord ++ tailWord_7381020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381020).length < 2 ^ (prefixWord ++ tailWord_7381020).sum := by decide
  have hdescent : baseEnd_7381020 < baseStart_7381020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381036 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_7381036 : Nat := 118140960795 + 7381036 * 2 ^ 59
def prefixEnd_7381036 : Nat := 4983230072969 + 3 ^ 40 * 7381036 * 2
def baseEnd_7381036 : Nat := 3790019196139288896405239

theorem tailTrace_7381036 : CollatzResearch.WordTrace tailWord_7381036 prefixEnd_7381036 3790019196139288896405239 := by
  unfold tailWord_7381036
  simp only [CollatzResearch.WordTrace]
  refine ⟨134604249643887313716981481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179472332858516418289308641 134604249643887313716981481)
  ·
    refine ⟨100953187232915485287736111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134604249643887313716981481 100953187232915485287736111)
    ·
      refine ⟨151429780849373227931604167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100953187232915485287736111 151429780849373227931604167)
      ·
        refine ⟨227144671274059841897406251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151429780849373227931604167 227144671274059841897406251)
        ·
          refine ⟨340717006911089762846109377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227144671274059841897406251 340717006911089762846109377)
          ·
            refine ⟨255537755183317322134582033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340717006911089762846109377 255537755183317322134582033)
            ·
              refine ⟨191653316387487991600936525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255537755183317322134582033 191653316387487991600936525)
              ·
                refine ⟨71869993645307996850351197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191653316387487991600936525 71869993645307996850351197)
                ·
                  refine ⟨26951247616990498818881699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71869993645307996850351197 26951247616990498818881699)
                  ·
                    refine ⟨40426871425485748228322549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26951247616990498818881699 40426871425485748228322549)
                    ·
                      refine ⟨3790019196139288896405239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40426871425485748228322549 3790019196139288896405239)
                      ·
                        rfl

theorem cell23_7381036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_7381036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381036 prefixEnd_7381036 := by exact prefixLift 7381036
  have htrace : WordTrace (prefixWord ++ tailWord_7381036) baseStart_7381036 baseEnd_7381036 := by
    simpa [prefixWord, tailWord_7381036, baseEnd_7381036] using wordTrace_append hprefix tailTrace_7381036
  have hstable : (prefixWord ++ tailWord_7381036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381036).length < 2 ^ (prefixWord ++ tailWord_7381036).sum := by decide
  have hdescent : baseEnd_7381036 < baseStart_7381036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381050 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2]
def baseStart_7381050 : Nat := 118140960795 + 7381050 * 2 ^ 59
def prefixEnd_7381050 : Nat := 4983230072969 + 3 ^ 40 * 7381050 * 2
def baseEnd_7381050 : Nat := 3790026384868451841630175

theorem tailTrace_7381050 : CollatzResearch.WordTrace tailWord_7381050 prefixEnd_7381050 3790026384868451841630175 := by
  unfold tailWord_7381050
  simp only [CollatzResearch.WordTrace]
  refine ⟨67302252477430976956243151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179472673273149271883315069 67302252477430976956243151)
  ·
    refine ⟨100953378716146465434364727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67302252477430976956243151 100953378716146465434364727)
    ·
      refine ⟨151430068074219698151547091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100953378716146465434364727 151430068074219698151547091)
      ·
        refine ⟨227145102111329547227320637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151430068074219698151547091 227145102111329547227320637)
        ·
          refine ⟨85179413291748580210245239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227145102111329547227320637 85179413291748580210245239)
          ·
            refine ⟨127769119937622870315367859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85179413291748580210245239 127769119937622870315367859)
            ·
              refine ⟨191653679906434305473051789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127769119937622870315367859 191653679906434305473051789)
              ·
                refine ⟨71870129964912864552394421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191653679906434305473051789 71870129964912864552394421)
                ·
                  refine ⟨6737824684210581051786977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71870129964912864552394421 6737824684210581051786977)
                  ·
                    refine ⟨5053368513157935788840233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6737824684210581051786977 5053368513157935788840233)
                    ·
                      refine ⟨3790026384868451841630175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053368513157935788840233 3790026384868451841630175)
                      ·
                        rfl

theorem cell23_7381050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_7381050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381050 prefixEnd_7381050 := by exact prefixLift 7381050
  have htrace : WordTrace (prefixWord ++ tailWord_7381050) baseStart_7381050 baseEnd_7381050 := by
    simpa [prefixWord, tailWord_7381050, baseEnd_7381050] using wordTrace_append hprefix tailTrace_7381050
  have hstable : (prefixWord ++ tailWord_7381050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381050).length < 2 ^ (prefixWord ++ tailWord_7381050).sum := by decide
  have hdescent : baseEnd_7381050 < baseStart_7381050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381054 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_7381054 : Nat := 118140960795 + 7381054 * 2 ^ 59
def prefixEnd_7381054 : Nat := 4983230072969 + 3 ^ 40 * 7381054 * 2
def baseEnd_7381054 : Nat := 3790028438791069825980157

theorem tailTrace_7381054 : CollatzResearch.WordTrace tailWord_7381054 prefixEnd_7381054 3790028438791069825980157 := by
  unfold tailWord_7381054
  simp only [CollatzResearch.WordTrace]
  refine ⟨33651144475213677063514777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179472770534472944338745477 33651144475213677063514777)
  ·
    refine ⟨25238358356410257797636083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33651144475213677063514777 25238358356410257797636083)
    ·
      refine ⟨37857537534615386696454125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25238358356410257797636083 37857537534615386696454125)
      ·
        refine ⟨14196576575480770011170297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37857537534615386696454125 14196576575480770011170297)
        ·
          refine ⟨10647432431610577508377723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14196576575480770011170297 10647432431610577508377723)
          ·
            refine ⟨15971148647415866262566585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10647432431610577508377723 15971148647415866262566585)
            ·
              refine ⟨11978361485561899696924939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15971148647415866262566585 11978361485561899696924939)
              ·
                refine ⟨17967542228342849545387409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11978361485561899696924939 17967542228342849545387409)
                ·
                  refine ⟨13475656671257137159040557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17967542228342849545387409 13475656671257137159040557)
                  ·
                    refine ⟨5053371251721426434640209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13475656671257137159040557 5053371251721426434640209)
                    ·
                      refine ⟨3790028438791069825980157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053371251721426434640209 3790028438791069825980157)
                      ·
                        rfl

theorem cell23_7381054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_7381054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381054 prefixEnd_7381054 := by exact prefixLift 7381054
  have htrace : WordTrace (prefixWord ++ tailWord_7381054) baseStart_7381054 baseEnd_7381054 := by
    simpa [prefixWord, tailWord_7381054, baseEnd_7381054] using wordTrace_append hprefix tailTrace_7381054
  have hstable : (prefixWord ++ tailWord_7381054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381054).length < 2 ^ (prefixWord ++ tailWord_7381054).sum := by decide
  have hdescent : baseEnd_7381054 < baseStart_7381054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381056 : List Nat := [2, 1, 1, 2, 2, 4, 2, 9]
def baseStart_7381056 : Nat := 118140960795 + 7381056 * 2 ^ 59
def prefixEnd_7381056 : Nat := 4983230072969 + 3 ^ 40 * 7381056 * 2
def baseEnd_7381056 : Nat := 140371461694532548820561

theorem tailTrace_7381056 : CollatzResearch.WordTrace tailWord_7381056 prefixEnd_7381056 140371461694532548820561 := by
  unfold tailWord_7381056
  simp only [CollatzResearch.WordTrace]
  refine ⟨134604614373851085424845511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179472819165134780566460681 134604614373851085424845511)
  ·
    refine ⟨201906921560776628137268267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134604614373851085424845511 201906921560776628137268267)
    ·
      refine ⟨302860382341164942205902401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201906921560776628137268267 302860382341164942205902401)
      ·
        refine ⟨227145286755873706654426801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302860382341164942205902401 227145286755873706654426801)
        ·
          refine ⟨170358965066905279990820101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227145286755873706654426801 170358965066905279990820101)
          ·
            refine ⟨31942305950044739998278769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170358965066905279990820101 31942305950044739998278769)
            ·
              refine ⟨23956729462533554998709077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31942305950044739998278769 23956729462533554998709077)
              ·
                refine ⟨140371461694532548820561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23956729462533554998709077 140371461694532548820561)
                ·
                  rfl

theorem cell23_7381056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 9].length) (baseStart_7381056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381056 prefixEnd_7381056 := by exact prefixLift 7381056
  have htrace : WordTrace (prefixWord ++ tailWord_7381056) baseStart_7381056 baseEnd_7381056 := by
    simpa [prefixWord, tailWord_7381056, baseEnd_7381056] using wordTrace_append hprefix tailTrace_7381056
  have hstable : (prefixWord ++ tailWord_7381056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381056).length < 2 ^ (prefixWord ++ tailWord_7381056).sum := by decide
  have hdescent : baseEnd_7381056 < baseStart_7381056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381063 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_7381063 : Nat := 118140960795 + 7381063 * 2 ^ 59
def prefixEnd_7381063 : Nat := 4983230072969 + 3 ^ 40 * 7381063 * 2
def baseEnd_7381063 : Nat := 3790033060116960290767615

theorem tailTrace_7381063 : CollatzResearch.WordTrace tailWord_7381063 prefixEnd_7381063 3790033060116960290767615 := by
  unfold tailWord_7381063
  simp only [CollatzResearch.WordTrace]
  refine ⟨269209484058676811045195843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179472989372451207363463895 269209484058676811045195843)
  ·
    refine ⟨403814226088015216567793765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269209484058676811045195843 403814226088015216567793765)
    ·
      refine ⟨75715167391502853106461331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403814226088015216567793765 75715167391502853106461331)
      ·
        refine ⟨113572751087254279659691997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75715167391502853106461331 113572751087254279659691997)
        ·
          refine ⟨42589781657720354872384499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113572751087254279659691997 42589781657720354872384499)
          ·
            refine ⟨63884672486580532308576749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42589781657720354872384499 63884672486580532308576749)
            ·
              refine ⟨23956752182467699615716281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63884672486580532308576749 23956752182467699615716281)
              ·
                refine ⟨17967564136850774711787211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23956752182467699615716281 17967564136850774711787211)
                ·
                  refine ⟨26951346205276162067680817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17967564136850774711787211 26951346205276162067680817)
                  ·
                    refine ⟨20213509653957121550760613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26951346205276162067680817 20213509653957121550760613)
                    ·
                      refine ⟨3790033060116960290767615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20213509653957121550760613 3790033060116960290767615)
                      ·
                        rfl

theorem cell23_7381063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_7381063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381063 prefixEnd_7381063 := by exact prefixLift 7381063
  have htrace : WordTrace (prefixWord ++ tailWord_7381063) baseStart_7381063 baseEnd_7381063 := by
    simpa [prefixWord, tailWord_7381063, baseEnd_7381063] using wordTrace_append hprefix tailTrace_7381063
  have hstable : (prefixWord ++ tailWord_7381063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381063).length < 2 ^ (prefixWord ++ tailWord_7381063).sum := by decide
  have hdescent : baseEnd_7381063 < baseStart_7381063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381070 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_7381070 : Nat := 118140960795 + 7381070 * 2 ^ 59
def prefixEnd_7381070 : Nat := 4983230072969 + 3 ^ 40 * 7381070 * 2
def baseEnd_7381070 : Nat := 3790036654481541763380083

theorem tailTrace_7381070 : CollatzResearch.WordTrace tailWord_7381070 prefixEnd_7381070 3790036654481541763380083 := by
  unfold tailWord_7381070
  simp only [CollatzResearch.WordTrace]
  refine ⟨33651217421206431405087583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179473159579767634160467109 33651217421206431405087583)
  ·
    refine ⟨50476826131809647107631375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33651217421206431405087583 50476826131809647107631375)
    ·
      refine ⟨75715239197714470661447063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50476826131809647107631375 75715239197714470661447063)
      ·
        refine ⟨113572858796571705992170595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75715239197714470661447063 113572858796571705992170595)
        ·
          refine ⟨170359288194857558988255893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113572858796571705992170595 170359288194857558988255893)
          ·
            refine ⟨7985591634133948077574495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170359288194857558988255893 7985591634133948077574495)
            ·
              refine ⟨11978387451200922116361743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7985591634133948077574495 11978387451200922116361743)
              ·
                refine ⟨17967581176801383174542615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11978387451200922116361743 17967581176801383174542615)
                ·
                  refine ⟨26951371765202074761813923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17967581176801383174542615 26951371765202074761813923)
                  ·
                    refine ⟨40427057647803112142720885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26951371765202074761813923 40427057647803112142720885)
                    ·
                      refine ⟨3790036654481541763380083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40427057647803112142720885 3790036654481541763380083)
                      ·
                        rfl

theorem cell23_7381070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_7381070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381070 prefixEnd_7381070 := by exact prefixLift 7381070
  have htrace : WordTrace (prefixWord ++ tailWord_7381070) baseStart_7381070 baseEnd_7381070 := by
    simpa [prefixWord, tailWord_7381070, baseEnd_7381070] using wordTrace_append hprefix tailTrace_7381070
  have hstable : (prefixWord ++ tailWord_7381070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381070).length < 2 ^ (prefixWord ++ tailWord_7381070).sum := by decide
  have hdescent : baseEnd_7381070 < baseStart_7381070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381078 : List Nat := [5, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_7381078 : Nat := 118140960795 + 7381078 * 2 ^ 59
def prefixEnd_7381078 : Nat := 4983230072969 + 3 ^ 40 * 7381078 * 2
def baseEnd_7381078 : Nat := 3790040762326777732080047

theorem tailTrace_7381078 : CollatzResearch.WordTrace tailWord_7381078 prefixEnd_7381078 3790040762326777732080047 := by
  unfold tailWord_7381078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16825626947101404287936993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179473354102414979071327925 16825626947101404287936993)
  ·
    refine ⟨12619220210326053215952745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16825626947101404287936993 12619220210326053215952745)
    ·
      refine ⟨9464415157744539911964559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12619220210326053215952745 9464415157744539911964559)
      ·
        refine ⟨14196622736616809867946839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9464415157744539911964559 14196622736616809867946839)
        ·
          refine ⟨21294934104925214801920259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14196622736616809867946839 21294934104925214801920259)
          ·
            refine ⟨31942401157387822202880389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21294934104925214801920259 31942401157387822202880389)
            ·
              refine ⟨5989200217010216663040073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31942401157387822202880389 5989200217010216663040073)
              ·
                refine ⟨4491900162757662497280055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5989200217010216663040073 4491900162757662497280055)
                ·
                  refine ⟨6737850244136493745920083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491900162757662497280055 6737850244136493745920083)
                  ·
                    refine ⟨10106775366204740618880125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6737850244136493745920083 10106775366204740618880125)
                    ·
                      refine ⟨3790040762326777732080047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10106775366204740618880125 3790040762326777732080047)
                      ·
                        rfl

theorem cell23_7381078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_7381078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381078 prefixEnd_7381078 := by exact prefixLift 7381078
  have htrace : WordTrace (prefixWord ++ tailWord_7381078) baseStart_7381078 baseEnd_7381078 := by
    simpa [prefixWord, tailWord_7381078, baseEnd_7381078] using wordTrace_append hprefix tailTrace_7381078
  have hstable : (prefixWord ++ tailWord_7381078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381078).length < 2 ^ (prefixWord ++ tailWord_7381078).sum := by decide
  have hdescent : baseEnd_7381078 < baseStart_7381078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381100 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 3]
def baseStart_7381100 : Nat := 118140960795 + 7381100 * 2 ^ 59
def prefixEnd_7381100 : Nat := 4983230072969 + 3 ^ 40 * 7381100 * 2
def baseEnd_7381100 : Nat := 3790052058901176646004945

theorem tailTrace_7381100 : CollatzResearch.WordTrace tailWord_7381100 prefixEnd_7381100 3790052058901176646004945 := by
  unfold tailWord_7381100
  simp only [CollatzResearch.WordTrace]
  refine ⟨134605416779771383182146377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179473889039695177576195169 134605416779771383182146377)
  ·
    refine ⟨100954062584828537386609783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134605416779771383182146377 100954062584828537386609783)
    ·
      refine ⟨151431093877242806079914675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100954062584828537386609783 151431093877242806079914675)
      ·
        refine ⟨227146640815864209119872013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151431093877242806079914675 227146640815864209119872013)
        ·
          refine ⟨85179990305949078419952005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227146640815864209119872013 85179990305949078419952005)
          ·
            refine ⟨15971248182365452203741001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85179990305949078419952005 15971248182365452203741001)
            ·
              refine ⟨11978436136774089152805751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15971248182365452203741001 11978436136774089152805751)
              ·
                refine ⟨17967654205161133729208627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11978436136774089152805751 17967654205161133729208627)
                ·
                  refine ⟨26951481307741700593812941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17967654205161133729208627 26951481307741700593812941)
                  ·
                    refine ⟨10106805490403137722679853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26951481307741700593812941 10106805490403137722679853)
                    ·
                      refine ⟨3790052058901176646004945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10106805490403137722679853 3790052058901176646004945)
                      ·
                        rfl

theorem cell23_7381100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_7381100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381100 prefixEnd_7381100 := by exact prefixLift 7381100
  have htrace : WordTrace (prefixWord ++ tailWord_7381100) baseStart_7381100 baseEnd_7381100 := by
    simpa [prefixWord, tailWord_7381100, baseEnd_7381100] using wordTrace_append hprefix tailTrace_7381100
  have hstable : (prefixWord ++ tailWord_7381100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381100).length < 2 ^ (prefixWord ++ tailWord_7381100).sum := by decide
  have hdescent : baseEnd_7381100 < baseStart_7381100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381121 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_7381121 : Nat := 118140960795 + 7381121 * 2 ^ 59
def prefixEnd_7381121 : Nat := 4983230072969 + 3 ^ 40 * 7381121 * 2
def baseEnd_7381121 : Nat := 3790062841994921063842349

theorem tailTrace_7381121 : CollatzResearch.WordTrace tailWord_7381121 prefixEnd_7381121 3790062841994921063842349 := by
  unfold tailWord_7381121
  simp only [CollatzResearch.WordTrace]
  refine ⟨269211599492466686950807217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179474399661644457967204811 269211599492466686950807217)
  ·
    refine ⟨201908699619350015213105413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269211599492466686950807217 201908699619350015213105413)
    ·
      refine ⟨37857881178628127852457265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201908699619350015213105413 37857881178628127852457265)
      ·
        refine ⟨28393410883971095889342949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37857881178628127852457265 28393410883971095889342949)
        ·
          refine ⟨5323764540744580479251803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28393410883971095889342949 5323764540744580479251803)
          ·
            refine ⟨7985646811116870718877705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323764540744580479251803 7985646811116870718877705)
            ·
              refine ⟨5989235108337653039158279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7985646811116870718877705 5989235108337653039158279)
              ·
                refine ⟨8983852662506479558737419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5989235108337653039158279 8983852662506479558737419)
                ·
                  refine ⟨13475778993759719338106129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8983852662506479558737419 13475778993759719338106129)
                  ·
                    refine ⟨10106834245319789503579597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13475778993759719338106129 10106834245319789503579597)
                    ·
                      refine ⟨3790062841994921063842349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10106834245319789503579597 3790062841994921063842349)
                      ·
                        rfl

theorem cell23_7381121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_7381121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381121 prefixEnd_7381121 := by exact prefixLift 7381121
  have htrace : WordTrace (prefixWord ++ tailWord_7381121) baseStart_7381121 baseEnd_7381121 := by
    simpa [prefixWord, tailWord_7381121, baseEnd_7381121] using wordTrace_append hprefix tailTrace_7381121
  have hstable : (prefixWord ++ tailWord_7381121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381121).length < 2 ^ (prefixWord ++ tailWord_7381121).sum := by decide
  have hdescent : baseEnd_7381121 < baseStart_7381121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381284 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_7381284 : Nat := 118140960795 + 7381284 * 2 ^ 59
def prefixEnd_7381284 : Nat := 4983230072969 + 3 ^ 40 * 7381284 * 2
def baseEnd_7381284 : Nat := 3790146539341603926104099

theorem tailTrace_7381284 : CollatzResearch.WordTrace tailWord_7381284 prefixEnd_7381284 3790146539341603926104099 := by
  unfold tailWord_7381284
  simp only [CollatzResearch.WordTrace]
  refine ⟨134608772295438082894495453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179478363060584110525993937 134608772295438082894495453)
  ·
    refine ⟨50478289610789281085435795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134608772295438082894495453 50478289610789281085435795)
    ·
      refine ⟨75717434416183921628153693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50478289610789281085435795 75717434416183921628153693)
      ·
        refine ⟨28394037906068970610557635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75717434416183921628153693 28394037906068970610557635)
        ·
          refine ⟨42591056859103455915836453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28394037906068970610557635 42591056859103455915836453)
          ·
            refine ⟨7985823161081897984219335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42591056859103455915836453 7985823161081897984219335)
            ·
              refine ⟨11978734741622846976329003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7985823161081897984219335 11978734741622846976329003)
              ·
                refine ⟨17968102112434270464493505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11978734741622846976329003 17968102112434270464493505)
                ·
                  refine ⟨13476076584325702848370129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17968102112434270464493505 13476076584325702848370129)
                  ·
                    refine ⟨10107057438244277136277597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13476076584325702848370129 10107057438244277136277597)
                    ·
                      refine ⟨3790146539341603926104099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10107057438244277136277597 3790146539341603926104099)
                      ·
                        rfl

theorem cell23_7381284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_7381284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381284 prefixEnd_7381284 := by exact prefixLift 7381284
  have htrace : WordTrace (prefixWord ++ tailWord_7381284) baseStart_7381284 baseEnd_7381284 := by
    simpa [prefixWord, tailWord_7381284, baseEnd_7381284] using wordTrace_append hprefix tailTrace_7381284
  have hstable : (prefixWord ++ tailWord_7381284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381284).length < 2 ^ (prefixWord ++ tailWord_7381284).sum := by decide
  have hdescent : baseEnd_7381284 < baseStart_7381284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381320 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_7381320 : Nat := 118140960795 + 7381320 * 2 ^ 59
def prefixEnd_7381320 : Nat := 4983230072969 + 3 ^ 40 * 7381320 * 2
def baseEnd_7381320 : Nat := 3790165024645165785253933

theorem tailTrace_7381320 : CollatzResearch.WordTrace tailWord_7381320 prefixEnd_7381320 3790165024645165785253933 := by
  unfold tailWord_7381320
  simp only [CollatzResearch.WordTrace]
  refine ⟨134609428809372871968650707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179479238412497162624867609 134609428809372871968650707)
  ·
    refine ⟨201914143214059307952976061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134609428809372871968650707 201914143214059307952976061)
    ·
      refine ⟨75717803705272240482366023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201914143214059307952976061 75717803705272240482366023)
      ·
        refine ⟨113576705557908360723549035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75717803705272240482366023 113576705557908360723549035)
        ·
          refine ⟨170365058336862541085323553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113576705557908360723549035 170365058336862541085323553)
          ·
            refine ⟨127773793752646905813992665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170365058336862541085323553 127773793752646905813992665)
            ·
              refine ⟨95830345314485179360494499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127773793752646905813992665 95830345314485179360494499)
              ·
                refine ⟨143745517971727769040741749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95830345314485179360494499 143745517971727769040741749)
                ·
                  refine ⟨13476142309849478347569539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143745517971727769040741749 13476142309849478347569539)
                  ·
                    refine ⟨20214213464774217521354309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13476142309849478347569539 20214213464774217521354309)
                    ·
                      refine ⟨3790165024645165785253933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20214213464774217521354309 3790165024645165785253933)
                      ·
                        rfl

theorem cell23_7381320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_7381320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381320 prefixEnd_7381320 := by exact prefixLift 7381320
  have htrace : WordTrace (prefixWord ++ tailWord_7381320) baseStart_7381320 baseEnd_7381320 := by
    simpa [prefixWord, tailWord_7381320, baseEnd_7381320] using wordTrace_append hprefix tailTrace_7381320
  have hstable : (prefixWord ++ tailWord_7381320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381320).length < 2 ^ (prefixWord ++ tailWord_7381320).sum := by decide
  have hdescent : baseEnd_7381320 < baseStart_7381320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381354 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_7381354 : Nat := 118140960795 + 7381354 * 2 ^ 59
def prefixEnd_7381354 : Nat := 4983230072969 + 3 ^ 40 * 7381354 * 2
def baseEnd_7381354 : Nat := 3790182482987418652228777

theorem tailTrace_7381354 : CollatzResearch.WordTrace tailWord_7381354 prefixEnd_7381354 3790182482987418652228777 := by
  unfold tailWord_7381354
  simp only [CollatzResearch.WordTrace]
  refine ⟨67305024425155641936009779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179480065133748378496026077 67305024425155641936009779)
  ·
    refine ⟨100957536637733462904014669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67305024425155641936009779 100957536637733462904014669)
    ·
      refine ⟨37859076239150048589005501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100957536637733462904014669 37859076239150048589005501)
      ·
        refine ⟨14197153589681268220877063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37859076239150048589005501 14197153589681268220877063)
        ·
          refine ⟨21295730384521902331315595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14197153589681268220877063 21295730384521902331315595)
          ·
            refine ⟨31943595576782853496973393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21295730384521902331315595 31943595576782853496973393)
            ·
              refine ⟨23957696682587140122730045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31943595576782853496973393 23957696682587140122730045)
              ·
                refine ⟨8984136255970177546023767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23957696682587140122730045 8984136255970177546023767)
                ·
                  refine ⟨13476204383955266319035651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8984136255970177546023767 13476204383955266319035651)
                  ·
                    refine ⟨20214306575932899478553477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13476204383955266319035651 20214306575932899478553477)
                    ·
                      refine ⟨3790182482987418652228777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20214306575932899478553477 3790182482987418652228777)
                      ·
                        rfl

theorem cell23_7381354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_7381354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381354 prefixEnd_7381354 := by exact prefixLift 7381354
  have htrace : WordTrace (prefixWord ++ tailWord_7381354) baseStart_7381354 baseEnd_7381354 := by
    simpa [prefixWord, tailWord_7381354, baseEnd_7381354] using wordTrace_append hprefix tailTrace_7381354
  have hstable : (prefixWord ++ tailWord_7381354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381354).length < 2 ^ (prefixWord ++ tailWord_7381354).sum := by decide
  have hdescent : baseEnd_7381354 < baseStart_7381354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381357 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_7381357 : Nat := 118140960795 + 7381357 * 2 ^ 59
def prefixEnd_7381357 : Nat := 4983230072969 + 3 ^ 40 * 7381357 * 2
def baseEnd_7381357 : Nat := 3790184023429382140491263

theorem tailTrace_7381357 : CollatzResearch.WordTrace tailWord_7381357 prefixEnd_7381357 3790184023429382140491263 := by
  unfold tailWord_7381357
  simp only [CollatzResearch.WordTrace]
  refine ⟨269220207119611699256398325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179480138079741132837598883 269220207119611699256398325)
  ·
    refine ⟨25239394417463596805287343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269220207119611699256398325 25239394417463596805287343)
    ·
      refine ⟨37859091626195395207931015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25239394417463596805287343 37859091626195395207931015)
      ·
        refine ⟨56788637439293092811896523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37859091626195395207931015 56788637439293092811896523)
        ·
          refine ⟨85182956158939639217844785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56788637439293092811896523 85182956158939639217844785)
          ·
            refine ⟨63887217119204729413383589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85182956158939639217844785 63887217119204729413383589)
            ·
              refine ⟨11978853209850886765009423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63887217119204729413383589 11978853209850886765009423)
              ·
                refine ⟨17968279814776330147514135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11978853209850886765009423 17968279814776330147514135)
                ·
                  refine ⟨26952419722164495221271203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17968279814776330147514135 26952419722164495221271203)
                  ·
                    refine ⟨40428629583246742831906805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26952419722164495221271203 40428629583246742831906805)
                    ·
                      refine ⟨3790184023429382140491263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40428629583246742831906805 3790184023429382140491263)
                      ·
                        rfl

theorem cell23_7381357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_7381357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381357 prefixEnd_7381357 := by exact prefixLift 7381357
  have htrace : WordTrace (prefixWord ++ tailWord_7381357) baseStart_7381357 baseEnd_7381357 := by
    simpa [prefixWord, tailWord_7381357, baseEnd_7381357] using wordTrace_append hprefix tailTrace_7381357
  have hstable : (prefixWord ++ tailWord_7381357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381357).length < 2 ^ (prefixWord ++ tailWord_7381357).sum := by decide
  have hdescent : baseEnd_7381357 < baseStart_7381357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381360 : List Nat := [2, 1, 1, 1, 4, 5, 9]
def baseStart_7381360 : Nat := 118140960795 + 7381360 * 2 ^ 59
def prefixEnd_7381360 : Nat := 4983230072969 + 3 ^ 40 * 7381360 * 2
def baseEnd_7381360 : Nat := 46792414368782044799429

theorem tailTrace_7381360 : CollatzResearch.WordTrace tailWord_7381360 prefixEnd_7381360 46792414368782044799429 := by
  unfold tailWord_7381360
  simp only [CollatzResearch.WordTrace]
  refine ⟨134610158269300415384378767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179480211025733887179171689 134610158269300415384378767)
  ·
    refine ⟨201915237403950623076568151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134610158269300415384378767 201915237403950623076568151)
    ·
      refine ⟨302872856105925934614852227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201915237403950623076568151 302872856105925934614852227)
      ·
        refine ⟨454309284158888901922278341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302872856105925934614852227 454309284158888901922278341)
        ·
          refine ⟨85182990779791669110427189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454309284158888901922278341 85182990779791669110427189)
          ·
            refine ⟨7985905385605468979102549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85182990779791669110427189 7985905385605468979102549)
            ·
              refine ⟨46792414368782044799429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7985905385605468979102549 46792414368782044799429)
              ·
                rfl

theorem cell23_7381360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 9].length) (baseStart_7381360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381360 prefixEnd_7381360 := by exact prefixLift 7381360
  have htrace : WordTrace (prefixWord ++ tailWord_7381360) baseStart_7381360 baseEnd_7381360 := by
    simpa [prefixWord, tailWord_7381360, baseEnd_7381360] using wordTrace_append hprefix tailTrace_7381360
  have hstable : (prefixWord ++ tailWord_7381360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381360).length < 2 ^ (prefixWord ++ tailWord_7381360).sum := by decide
  have hdescent : baseEnd_7381360 < baseStart_7381360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381370 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3]
def baseStart_7381370 : Nat := 118140960795 + 7381370 * 2 ^ 59
def prefixEnd_7381370 : Nat := 4983230072969 + 3 ^ 40 * 7381370 * 2
def baseEnd_7381370 : Nat := 3790190698677890589628703

theorem tailTrace_7381370 : CollatzResearch.WordTrace tailWord_7381370 prefixEnd_7381370 3790190698677890589628703 := by
  unfold tailWord_7381370
  simp only [CollatzResearch.WordTrace]
  refine ⟨67305170317141150619155391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179480454179043068317747709 67305170317141150619155391)
  ·
    refine ⟨100957755475711725928733087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67305170317141150619155391 100957755475711725928733087)
    ·
      refine ⟨151436633213567588893099631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100957755475711725928733087 151436633213567588893099631)
      ·
        refine ⟨227154949820351383339649447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151436633213567588893099631 227154949820351383339649447)
        ·
          refine ⟨340732424730527075009474171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227154949820351383339649447 340732424730527075009474171)
          ·
            refine ⟨511098637095790612514211257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340732424730527075009474171 511098637095790612514211257)
            ·
              refine ⟨383323977821842959385658443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511098637095790612514211257 383323977821842959385658443)
              ·
                refine ⟨574985966732764439078487665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383323977821842959385658443 574985966732764439078487665)
                ·
                  refine ⟨431239475049573329308865749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574985966732764439078487665 431239475049573329308865749)
                  ·
                    refine ⟨10107175196474374905676541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 431239475049573329308865749 10107175196474374905676541)
                    ·
                      refine ⟨3790190698677890589628703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10107175196474374905676541 3790190698677890589628703)
                      ·
                        rfl

theorem cell23_7381370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_7381370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381370 prefixEnd_7381370 := by exact prefixLift 7381370
  have htrace : WordTrace (prefixWord ++ tailWord_7381370) baseStart_7381370 baseEnd_7381370 := by
    simpa [prefixWord, tailWord_7381370, baseEnd_7381370] using wordTrace_append hprefix tailTrace_7381370
  have hstable : (prefixWord ++ tailWord_7381370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381370).length < 2 ^ (prefixWord ++ tailWord_7381370).sum := by decide
  have hdescent : baseEnd_7381370 < baseStart_7381370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381371 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 3, 2, 2]
def baseStart_7381371 : Nat := 118140960795 + 7381371 * 2 ^ 59
def prefixEnd_7381371 : Nat := 4983230072969 + 3 ^ 40 * 7381371 * 2
def baseEnd_7381371 : Nat := 3790191212158545085716199

theorem tailTrace_7381371 : CollatzResearch.WordTrace tailWord_7381371 prefixEnd_7381371 3790191212158545085716199 := by
  unfold tailWord_7381371
  simp only [CollatzResearch.WordTrace]
  refine ⟨269220717741560979647407967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179480478494373986431605311 269220717741560979647407967)
  ·
    refine ⟨403831076612341469471111951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269220717741560979647407967 403831076612341469471111951)
    ·
      refine ⟨605746614918512204206667927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403831076612341469471111951 605746614918512204206667927)
      ·
        refine ⟨908619922377768306310001891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605746614918512204206667927 908619922377768306310001891)
        ·
          refine ⟨1362929883566652459465002837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908619922377768306310001891 1362929883566652459465002837)
          ·
            refine ⟨7985917286523354254677751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1362929883566652459465002837 7985917286523354254677751)
            ·
              refine ⟨11978875929785031382016627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7985917286523354254677751 11978875929785031382016627)
              ·
                refine ⟨17968313894677547073024941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11978875929785031382016627 17968313894677547073024941)
                ·
                  refine ⟨6738117710504080152384353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17968313894677547073024941 6738117710504080152384353)
                  ·
                    refine ⟨5053588282878060114288265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6738117710504080152384353 5053588282878060114288265)
                    ·
                      refine ⟨3790191212158545085716199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053588282878060114288265 3790191212158545085716199)
                      ·
                        rfl

theorem cell23_7381371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 2, 2].length) (baseStart_7381371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381371 prefixEnd_7381371 := by exact prefixLift 7381371
  have htrace : WordTrace (prefixWord ++ tailWord_7381371) baseStart_7381371 baseEnd_7381371 := by
    simpa [prefixWord, tailWord_7381371, baseEnd_7381371] using wordTrace_append hprefix tailTrace_7381371
  have hstable : (prefixWord ++ tailWord_7381371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381371).length < 2 ^ (prefixWord ++ tailWord_7381371).sum := by decide
  have hdescent : baseEnd_7381371 < baseStart_7381371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381377 : List Nat := [1, 2, 4, 3, 1, 2, 2, 8]
def baseStart_7381377 : Nat := 118140960795 + 7381377 * 2 ^ 59
def prefixEnd_7381377 : Nat := 4983230072969 + 3 ^ 40 * 7381377 * 2
def baseEnd_7381377 : Nat := 140377566408980446749673

theorem tailTrace_7381377 : CollatzResearch.WordTrace tailWord_7381377 prefixEnd_7381377 140377566408980446749673 := by
  unfold tailWord_7381377
  simp only [CollatzResearch.WordTrace]
  refine ⟨269220936579539242672126385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179480624386359495114750923 269220936579539242672126385)
  ·
    refine ⟨201915702434654432004094789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269220936579539242672126385 201915702434654432004094789)
    ·
      refine ⟨37859194206497706000767773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201915702434654432004094789 37859194206497706000767773)
      ·
        refine ⟨14197197827436639750287915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37859194206497706000767773 14197197827436639750287915)
        ·
          refine ⟨21295796741154959625431873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14197197827436639750287915 21295796741154959625431873)
          ·
            refine ⟨15971847555866219719073905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21295796741154959625431873 15971847555866219719073905)
            ·
              refine ⟨11978885666899664789305429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15971847555866219719073905 11978885666899664789305429)
              ·
                refine ⟨140377566408980446749673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11978885666899664789305429 140377566408980446749673)
                ·
                  rfl

theorem cell23_7381377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 8].length) (baseStart_7381377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381377 prefixEnd_7381377 := by exact prefixLift 7381377
  have htrace : WordTrace (prefixWord ++ tailWord_7381377) baseStart_7381377 baseEnd_7381377 := by
    simpa [prefixWord, tailWord_7381377, baseEnd_7381377] using wordTrace_append hprefix tailTrace_7381377
  have hstable : (prefixWord ++ tailWord_7381377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381377).length < 2 ^ (prefixWord ++ tailWord_7381377).sum := by decide
  have hdescent : baseEnd_7381377 < baseStart_7381377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381380 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_7381380 : Nat := 118140960795 + 7381380 * 2 ^ 59
def prefixEnd_7381380 : Nat := 4983230072969 + 3 ^ 40 * 7381380 * 2
def baseEnd_7381380 : Nat := 3790195833484435550503657

theorem tailTrace_7381380 : CollatzResearch.WordTrace tailWord_7381380 prefixEnd_7381380 3790195833484435550503657 := by
  unfold tailWord_7381380
  simp only [CollatzResearch.WordTrace]
  refine ⟨134610522999264187092242797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179480697332352249456323729 134610522999264187092242797)
  ·
    refine ⟨50478946124724070159591049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134610522999264187092242797 50478946124724070159591049)
    ·
      refine ⟨37859209593543052619693287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50478946124724070159591049 37859209593543052619693287)
      ·
        refine ⟨56788814390314578929539931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37859209593543052619693287 56788814390314578929539931)
        ·
          refine ⟨85183221585471868394309897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56788814390314578929539931 85183221585471868394309897)
          ·
            refine ⟨63887416189103901295732423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85183221585471868394309897 63887416189103901295732423)
            ·
              refine ⟨95831124283655851943598635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63887416189103901295732423 95831124283655851943598635)
              ·
                refine ⟨143746686425483777915397953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95831124283655851943598635 143746686425483777915397953)
                ·
                  refine ⟨107810014819112833436548465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143746686425483777915397953 107810014819112833436548465)
                  ·
                    refine ⟨80857511114334625077411349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107810014819112833436548465 80857511114334625077411349)
                    ·
                      refine ⟨3790195833484435550503657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80857511114334625077411349 3790195833484435550503657)
                      ·
                        rfl

theorem cell23_7381380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_7381380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381380 prefixEnd_7381380 := by exact prefixLift 7381380
  have htrace : WordTrace (prefixWord ++ tailWord_7381380) baseStart_7381380 baseEnd_7381380 := by
    simpa [prefixWord, tailWord_7381380, baseEnd_7381380] using wordTrace_append hprefix tailTrace_7381380
  have hstable : (prefixWord ++ tailWord_7381380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381380).length < 2 ^ (prefixWord ++ tailWord_7381380).sum := by decide
  have hdescent : baseEnd_7381380 < baseStart_7381380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381398 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7381398 : Nat := 118140960795 + 7381398 * 2 ^ 59
def prefixEnd_7381398 : Nat := 4983230072969 + 3 ^ 40 * 7381398 * 2
def baseEnd_7381398 : Nat := 1263401692045405493359525

theorem tailTrace_7381398 : CollatzResearch.WordTrace tailWord_7381398 prefixEnd_7381398 1263401692045405493359525 := by
  unfold tailWord_7381398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16826356407028947703665053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179481135008308775505760565 16826356407028947703665053)
  ·
    refine ⟨6309883652635855388874395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16826356407028947703665053 6309883652635855388874395)
    ·
      refine ⟨9464825478953783083311593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6309883652635855388874395 9464825478953783083311593)
      ·
        refine ⟨7098619109215337312483695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9464825478953783083311593 7098619109215337312483695)
        ·
          refine ⟨10647928663823005968725543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098619109215337312483695 10647928663823005968725543)
          ·
            refine ⟨15971892995734508953088315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10647928663823005968725543 15971892995734508953088315)
            ·
              refine ⟨23957839493601763429632473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15971892995734508953088315 23957839493601763429632473)
              ·
                refine ⟨17968379620201322572224355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23957839493601763429632473 17968379620201322572224355)
                ·
                  refine ⟨26952569430301983858336533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17968379620201322572224355 26952569430301983858336533)
                  ·
                    refine ⟨1263401692045405493359525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26952569430301983858336533 1263401692045405493359525)
                    ·
                      rfl

theorem cell23_7381398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7381398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381398 prefixEnd_7381398 := by exact prefixLift 7381398
  have htrace : WordTrace (prefixWord ++ tailWord_7381398) baseStart_7381398 baseEnd_7381398 := by
    simpa [prefixWord, tailWord_7381398, baseEnd_7381398] using wordTrace_append hprefix tailTrace_7381398
  have hstable : (prefixWord ++ tailWord_7381398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381398).length < 2 ^ (prefixWord ++ tailWord_7381398).sum := by decide
  have hdescent : baseEnd_7381398 < baseStart_7381398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381420 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_7381420 : Nat := 118140960795 + 7381420 * 2 ^ 59
def prefixEnd_7381420 : Nat := 4983230072969 + 3 ^ 40 * 7381420 * 2
def baseEnd_7381420 : Nat := 1263405457570205131334491

theorem tailTrace_7381420 : CollatzResearch.WordTrace tailWord_7381420 prefixEnd_7381420 1263405457570205131334491 := by
  unfold tailWord_7381420
  simp only [CollatzResearch.WordTrace]
  refine ⟨134611252459191730507970857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179481669945588974010627809 134611252459191730507970857)
  ·
    refine ⟨100958439344393797880978143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134611252459191730507970857 100958439344393797880978143)
    ·
      refine ⟨151437659016590696821467215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100958439344393797880978143 151437659016590696821467215)
      ·
        refine ⟨227156488524886045232200823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151437659016590696821467215 227156488524886045232200823)
        ·
          refine ⟨340734732787329067848301235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227156488524886045232200823 340734732787329067848301235)
          ·
            refine ⟨511102099180993601772451853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340734732787329067848301235 511102099180993601772451853)
            ·
              refine ⟨191663287192872600664669445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511102099180993601772451853 191663287192872600664669445)
              ·
                refine ⟨35936866348663612624625521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191663287192872600664669445 35936866348663612624625521)
                ·
                  refine ⟨26952649761497709468469141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35936866348663612624625521 26952649761497709468469141)
                  ·
                    refine ⟨1263405457570205131334491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26952649761497709468469141 1263405457570205131334491)
                    ·
                      rfl

theorem cell23_7381420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_7381420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381420 prefixEnd_7381420 := by exact prefixLift 7381420
  have htrace : WordTrace (prefixWord ++ tailWord_7381420) baseStart_7381420 baseEnd_7381420 := by
    simpa [prefixWord, tailWord_7381420, baseEnd_7381420] using wordTrace_append hprefix tailTrace_7381420
  have hstable : (prefixWord ++ tailWord_7381420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381420).length < 2 ^ (prefixWord ++ tailWord_7381420).sum := by decide
  have hdescent : baseEnd_7381420 < baseStart_7381420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381428 : List Nat := [2, 5, 2, 2, 2, 1, 1, 8]
def baseStart_7381428 : Nat := 118140960795 + 7381428 * 2 ^ 59
def prefixEnd_7381428 : Nat := 4983230072969 + 3 ^ 40 * 7381428 * 2
def baseEnd_7381428 : Nat := 140378536316883383803831

theorem tailTrace_7381428 : CollatzResearch.WordTrace tailWord_7381428 prefixEnd_7381428 140378536316883383803831 := by
  unfold tailWord_7381428
  simp only [CollatzResearch.WordTrace]
  refine ⟨134611398351177239191116469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179481864468236318921488625 134611398351177239191116469)
  ·
    refine ⟨12619818595422866174167169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134611398351177239191116469 12619818595422866174167169)
    ·
      refine ⟨9464863946567149630625377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12619818595422866174167169 9464863946567149630625377)
      ·
        refine ⟨7098647959925362222969033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9464863946567149630625377 7098647959925362222969033)
        ·
          refine ⟨5323985969944021667226775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7098647959925362222969033 5323985969944021667226775)
          ·
            refine ⟨7985978954916032500840163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323985969944021667226775 7985978954916032500840163)
            ·
              refine ⟨11978968432374048751260245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7985978954916032500840163 11978968432374048751260245)
              ·
                refine ⟨140378536316883383803831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11978968432374048751260245 140378536316883383803831)
                ·
                  rfl

theorem cell23_7381428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 8].length) (baseStart_7381428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381428 prefixEnd_7381428 := by exact prefixLift 7381428
  have htrace : WordTrace (prefixWord ++ tailWord_7381428) baseStart_7381428 baseEnd_7381428 := by
    simpa [prefixWord, tailWord_7381428, baseEnd_7381428] using wordTrace_append hprefix tailTrace_7381428
  have hstable : (prefixWord ++ tailWord_7381428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381428).length < 2 ^ (prefixWord ++ tailWord_7381428).sum := by decide
  have hdescent : baseEnd_7381428 < baseStart_7381428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381437 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_7381437 : Nat := 118140960795 + 7381437 * 2 ^ 59
def prefixEnd_7381437 : Nat := 4983230072969 + 3 ^ 40 * 7381437 * 2
def baseEnd_7381437 : Nat := 1263408367293913942496965

theorem tailTrace_7381437 : CollatzResearch.WordTrace tailWord_7381437 prefixEnd_7381437 1263408367293913942496965 := by
  unfold tailWord_7381437
  simp only [CollatzResearch.WordTrace]
  refine ⟨269223124959321872919310565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179482083306214581946207043 269223124959321872919310565)
  ·
    refine ⟨50479335929872851172370731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269223124959321872919310565 50479335929872851172370731)
    ·
      refine ⟨75719003894809276758556097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50479335929872851172370731 75719003894809276758556097)
      ·
        refine ⟨56789252921106957568917073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75719003894809276758556097 56789252921106957568917073)
        ·
          refine ⟨42591939690830218176687805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56789252921106957568917073 42591939690830218176687805)
          ·
            refine ⟨15971977384061331816257927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42591939690830218176687805 15971977384061331816257927)
            ·
              refine ⟨23957966076091997724386891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15971977384061331816257927 23957966076091997724386891)
              ·
                refine ⟨35936949114137996586580337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23957966076091997724386891 35936949114137996586580337)
                ·
                  refine ⟨26952711835603497439935253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35936949114137996586580337 26952711835603497439935253)
                  ·
                    refine ⟨1263408367293913942496965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26952711835603497439935253 1263408367293913942496965)
                    ·
                      rfl

theorem cell23_7381437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_7381437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381437 prefixEnd_7381437 := by exact prefixLift 7381437
  have htrace : WordTrace (prefixWord ++ tailWord_7381437) baseStart_7381437 baseEnd_7381437 := by
    simpa [prefixWord, tailWord_7381437, baseEnd_7381437] using wordTrace_append hprefix tailTrace_7381437
  have hstable : (prefixWord ++ tailWord_7381437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381437).length < 2 ^ (prefixWord ++ tailWord_7381437).sum := by decide
  have hdescent : baseEnd_7381437 < baseStart_7381437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381494 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_7381494 : Nat := 118140960795 + 7381494 * 2 ^ 59
def prefixEnd_7381494 : Nat := 4983230072969 + 3 ^ 40 * 7381494 * 2
def baseEnd_7381494 : Nat := 3790254370279048104478133

theorem tailTrace_7381494 : CollatzResearch.WordTrace tailWord_7381494 prefixEnd_7381494 3790254370279048104478133 := by
  unfold tailWord_7381494
  simp only [CollatzResearch.WordTrace]
  refine ⟨16826575245007210728383471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179483469280076914436090357 16826575245007210728383471)
  ·
    refine ⟨25239862867510816092575207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16826575245007210728383471 25239862867510816092575207)
    ·
      refine ⟨37859794301266224138862811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25239862867510816092575207 37859794301266224138862811)
      ·
        refine ⟨56789691451899336208294217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37859794301266224138862811 56789691451899336208294217)
        ·
          refine ⟨42592268588924502156220663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56789691451899336208294217 42592268588924502156220663)
          ·
            refine ⟨63888402883386753234330995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42592268588924502156220663 63888402883386753234330995)
            ·
              refine ⟨95832604325080129851496493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63888402883386753234330995 95832604325080129851496493)
              ·
                refine ⟨35937226621905048694311185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95832604325080129851496493 35937226621905048694311185)
                ·
                  refine ⟨26952919966428786520733389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35937226621905048694311185 26952919966428786520733389)
                  ·
                    refine ⟨10107344987410794945275021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26952919966428786520733389 10107344987410794945275021)
                    ·
                      refine ⟨3790254370279048104478133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10107344987410794945275021 3790254370279048104478133)
                      ·
                        rfl

theorem cell23_7381494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_7381494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381494 prefixEnd_7381494 := by exact prefixLift 7381494
  have htrace : WordTrace (prefixWord ++ tailWord_7381494) baseStart_7381494 baseEnd_7381494 := by
    simpa [prefixWord, tailWord_7381494, baseEnd_7381494] using wordTrace_append hprefix tailTrace_7381494
  have hstable : (prefixWord ++ tailWord_7381494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381494).length < 2 ^ (prefixWord ++ tailWord_7381494).sum := by decide
  have hdescent : baseEnd_7381494 < baseStart_7381494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381584 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 7, 1, 3]
def baseStart_7381584 : Nat := 118140960795 + 7381584 * 2 ^ 59
def prefixEnd_7381584 : Nat := 4983230072969 + 3 ^ 40 * 7381584 * 2
def baseEnd_7381584 : Nat := 3790300583537952752352719

theorem tailTrace_7381584 : CollatzResearch.WordTrace tailWord_7381584 prefixEnd_7381584 3790300583537952752352719 := by
  unfold tailWord_7381584
  simp only [CollatzResearch.WordTrace]
  refine ⟨134614243244894658512455903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179485657659859544683274537 134614243244894658512455903)
  ·
    refine ⟨201921364867341987768683855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134614243244894658512455903 201921364867341987768683855)
    ·
      refine ⟨302882047301012981653025783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201921364867341987768683855 302882047301012981653025783)
      ·
        refine ⟨454323070951519472479538675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302882047301012981653025783 454323070951519472479538675)
        ·
          refine ⟨681484606427279208719308013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454323070951519472479538675 681484606427279208719308013)
          ·
            refine ⟨255556727410229703269740505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 681484606427279208719308013 255556727410229703269740505)
            ·
              refine ⟨191667545557672277452305379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255556727410229703269740505 191667545557672277452305379)
              ·
                refine ⟨287501318336508416178458069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191667545557672277452305379 287501318336508416178458069)
                ·
                  refine ⟨6738312148511916004182611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 287501318336508416178458069 6738312148511916004182611)
                  ·
                    refine ⟨10107468222767874006273917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6738312148511916004182611 10107468222767874006273917)
                    ·
                      refine ⟨3790300583537952752352719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10107468222767874006273917 3790300583537952752352719)
                      ·
                        rfl

theorem cell23_7381584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7, 1, 3].length) (baseStart_7381584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381584 prefixEnd_7381584 := by exact prefixLift 7381584
  have htrace : WordTrace (prefixWord ++ tailWord_7381584) baseStart_7381584 baseEnd_7381584 := by
    simpa [prefixWord, tailWord_7381584, baseEnd_7381584] using wordTrace_append hprefix tailTrace_7381584
  have hstable : (prefixWord ++ tailWord_7381584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381584).length < 2 ^ (prefixWord ++ tailWord_7381584).sum := by decide
  have hdescent : baseEnd_7381584 < baseStart_7381584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381594 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2]
def baseStart_7381594 : Nat := 118140960795 + 7381594 * 2 ^ 59
def prefixEnd_7381594 : Nat := 4983230072969 + 3 ^ 40 * 7381594 * 2
def baseEnd_7381594 : Nat := 3790305718344497713227673

theorem tailTrace_7381594 : CollatzResearch.WordTrace tailWord_7381594 prefixEnd_7381594 3790305718344497713227673 := by
  unfold tailWord_7381594
  simp only [CollatzResearch.WordTrace]
  refine ⟨67307212804938272183193959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179485900813168725821850557 67307212804938272183193959)
  ·
    refine ⟨100960819207407408274790939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67307212804938272183193959 100960819207407408274790939)
    ·
      refine ⟨151441228811111112412186409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100960819207407408274790939 151441228811111112412186409)
      ·
        refine ⟨113580921608333334309139807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151441228811111112412186409 113580921608333334309139807)
        ·
          refine ⟨170371382412500001463709711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113580921608333334309139807 170371382412500001463709711)
          ·
            refine ⟨255557073618750002195564567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170371382412500001463709711 255557073618750002195564567)
            ·
              refine ⟨383335610428125003293346851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255557073618750002195564567 383335610428125003293346851)
              ·
                refine ⟨575003415642187504940020277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383335610428125003293346851 575003415642187504940020277)
                ·
                  refine ⟨53906570216455078588126901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 575003415642187504940020277 53906570216455078588126901)
                  ·
                    refine ⟨5053740957792663617636897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53906570216455078588126901 5053740957792663617636897)
                    ·
                      refine ⟨3790305718344497713227673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053740957792663617636897 3790305718344497713227673)
                      ·
                        rfl

theorem cell23_7381594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_7381594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381594 prefixEnd_7381594 := by exact prefixLift 7381594
  have htrace : WordTrace (prefixWord ++ tailWord_7381594) baseStart_7381594 baseEnd_7381594 := by
    simpa [prefixWord, tailWord_7381594, baseEnd_7381594] using wordTrace_append hprefix tailTrace_7381594
  have hstable : (prefixWord ++ tailWord_7381594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381594).length < 2 ^ (prefixWord ++ tailWord_7381594).sum := by decide
  have hdescent : baseEnd_7381594 < baseStart_7381594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381618 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_7381618 : Nat := 118140960795 + 7381618 * 2 ^ 59
def prefixEnd_7381618 : Nat := 4983230072969 + 3 ^ 40 * 7381618 * 2
def baseEnd_7381618 : Nat := 3790318041880205619327563

theorem tailTrace_7381618 : CollatzResearch.WordTrace tailWord_7381618 prefixEnd_7381618 3790318041880205619327563 := by
  unfold tailWord_7381618
  simp only [CollatzResearch.WordTrace]
  refine ⟨67307431642916535207912377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179486484381110760554433005 67307431642916535207912377)
  ·
    refine ⟨50480573732187401405934283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67307431642916535207912377 50480573732187401405934283)
    ·
      refine ⟨75720860598281102108901425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50480573732187401405934283 75720860598281102108901425)
      ·
        refine ⟨56790645448710826581676069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75720860598281102108901425 56790645448710826581676069)
        ·
          refine ⟨10648246021633279984064263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56790645448710826581676069 10648246021633279984064263)
          ·
            refine ⟨15972369032449919976096395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10648246021633279984064263 15972369032449919976096395)
            ·
              refine ⟨23958553548674879964144593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15972369032449919976096395 23958553548674879964144593)
              ·
                refine ⟨17968915161506159973108445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23958553548674879964144593 17968915161506159973108445)
                ·
                  refine ⟨6738343185564809989915667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17968915161506159973108445 6738343185564809989915667)
                  ·
                    refine ⟨10107514778347214984873501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6738343185564809989915667 10107514778347214984873501)
                    ·
                      refine ⟨3790318041880205619327563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10107514778347214984873501 3790318041880205619327563)
                      ·
                        rfl

theorem cell23_7381618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_7381618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381618 prefixEnd_7381618 := by exact prefixLift 7381618
  have htrace : WordTrace (prefixWord ++ tailWord_7381618) baseStart_7381618 baseEnd_7381618 := by
    simpa [prefixWord, tailWord_7381618, baseEnd_7381618] using wordTrace_append hprefix tailTrace_7381618
  have hstable : (prefixWord ++ tailWord_7381618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381618).length < 2 ^ (prefixWord ++ tailWord_7381618).sum := by decide
  have hdescent : baseEnd_7381618 < baseStart_7381618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381624 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 2, 6, 2]
def baseStart_7381624 : Nat := 118140960795 + 7381624 * 2 ^ 59
def prefixEnd_7381624 : Nat := 4983230072969 + 3 ^ 40 * 7381624 * 2
def baseEnd_7381624 : Nat := 3790321122764132595852535

theorem tailTrace_7381624 : CollatzResearch.WordTrace tailWord_7381624 prefixEnd_7381624 3790321122764132595852535 := by
  unfold tailWord_7381624
  simp only [CollatzResearch.WordTrace]
  refine ⟨134614972704822201928183963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179486630273096269237578617 134614972704822201928183963)
  ·
    refine ⟨201922459057233302892275945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134614972704822201928183963 201922459057233302892275945)
    ·
      refine ⟨151441844292924977169206959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201922459057233302892275945 151441844292924977169206959)
      ·
        refine ⟨227162766439387465753810439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151441844292924977169206959 227162766439387465753810439)
        ·
          refine ⟨340744149659081198630715659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227162766439387465753810439 340744149659081198630715659)
          ·
            refine ⟨511116224488621797946073489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340744149659081198630715659 511116224488621797946073489)
            ·
              refine ⟨383337168366466348459555117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511116224488621797946073489 383337168366466348459555117)
              ·
                refine ⟨143751438137424880672333169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383337168366466348459555117 143751438137424880672333169)
                ·
                  refine ⟨107813578603068660504249877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143751438137424880672333169 107813578603068660504249877)
                  ·
                    refine ⟨5053761497018843461136713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107813578603068660504249877 5053761497018843461136713)
                    ·
                      refine ⟨3790321122764132595852535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053761497018843461136713 3790321122764132595852535)
                      ·
                        rfl

theorem cell23_7381624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_7381624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381624 prefixEnd_7381624 := by exact prefixLift 7381624
  have htrace : WordTrace (prefixWord ++ tailWord_7381624) baseStart_7381624 baseEnd_7381624 := by
    simpa [prefixWord, tailWord_7381624, baseEnd_7381624] using wordTrace_append hprefix tailTrace_7381624
  have hstable : (prefixWord ++ tailWord_7381624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381624).length < 2 ^ (prefixWord ++ tailWord_7381624).sum := by decide
  have hdescent : baseEnd_7381624 < baseStart_7381624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381627 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 5]
def baseStart_7381627 : Nat := 118140960795 + 7381627 * 2 ^ 59
def prefixEnd_7381627 : Nat := 4983230072969 + 3 ^ 40 * 7381627 * 2
def baseEnd_7381627 : Nat := 3790322663206096084115021

theorem tailTrace_7381627 : CollatzResearch.WordTrace tailWord_7381627 prefixEnd_7381627 3790322663206096084115021 := by
  unfold tailWord_7381627
  simp only [CollatzResearch.WordTrace]
  refine ⟨269230054828633535368727135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179486703219089023579151423 269230054828633535368727135)
  ·
    refine ⟨403845082242950303053090703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269230054828633535368727135 403845082242950303053090703)
    ·
      refine ⟨605767623364425454579636055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403845082242950303053090703 605767623364425454579636055)
      ·
        refine ⟨908651435046638181869454083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605767623364425454579636055 908651435046638181869454083)
        ·
          refine ⟨1362977152569957272804181125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908651435046638181869454083 1362977152569957272804181125)
          ·
            refine ⟨255558216106866988650783961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1362977152569957272804181125 255558216106866988650783961)
            ·
              refine ⟨191668662080150241488087971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255558216106866988650783961 191668662080150241488087971)
              ·
                refine ⟨287502993120225362232131957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191668662080150241488087971 287502993120225362232131957)
                ·
                  refine ⟨26953405605021127709262371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287502993120225362232131957 26953405605021127709262371)
                  ·
                    refine ⟨40430108407531691563893557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26953405605021127709262371 40430108407531691563893557)
                    ·
                      refine ⟨3790322663206096084115021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40430108407531691563893557 3790322663206096084115021)
                      ·
                        rfl

theorem cell23_7381627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 5].length) (baseStart_7381627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381627 prefixEnd_7381627 := by exact prefixLift 7381627
  have htrace : WordTrace (prefixWord ++ tailWord_7381627) baseStart_7381627 baseEnd_7381627 := by
    simpa [prefixWord, tailWord_7381627, baseEnd_7381627] using wordTrace_append hprefix tailTrace_7381627
  have hstable : (prefixWord ++ tailWord_7381627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381627).length < 2 ^ (prefixWord ++ tailWord_7381627).sum := by decide
  have hdescent : baseEnd_7381627 < baseStart_7381627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381641 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 7, 2, 2]
def baseStart_7381641 : Nat := 118140960795 + 7381641 * 2 ^ 59
def prefixEnd_7381641 : Nat := 4983230072969 + 3 ^ 40 * 7381641 * 2
def baseEnd_7381641 : Nat := 3790329851935259029339957

theorem tailTrace_7381641 : CollatzResearch.WordTrace tailWord_7381641 prefixEnd_7381641 3790329851935259029339957 := by
  unfold tailWord_7381641
  simp only [CollatzResearch.WordTrace]
  refine ⟨269230565450582815759736777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179487043633721877173157851 269230565450582815759736777)
  ·
    refine ⟨201922924087937111819802583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269230565450582815759736777 201922924087937111819802583)
    ·
      refine ⟨302884386131905667729703875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201922924087937111819802583 302884386131905667729703875)
      ·
        refine ⟨454326579197858501594555813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302884386131905667729703875 454326579197858501594555813)
        ·
          refine ⟨85186233599598469048979215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454326579197858501594555813 85186233599598469048979215)
          ·
            refine ⟨127779350399397703573468823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85186233599598469048979215 127779350399397703573468823)
            ·
              refine ⟨191669025599096555360203235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127779350399397703573468823 191669025599096555360203235)
              ·
                refine ⟨287503538398644833040304853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191669025599096555360203235 287503538398644833040304853)
                ·
                  refine ⟨6738364181218238274382145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 287503538398644833040304853 6738364181218238274382145)
                  ·
                    refine ⟨5053773135913678705786609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6738364181218238274382145 5053773135913678705786609)
                    ·
                      refine ⟨3790329851935259029339957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053773135913678705786609 3790329851935259029339957)
                      ·
                        rfl

theorem cell23_7381641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 2, 2].length) (baseStart_7381641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381641 prefixEnd_7381641 := by exact prefixLift 7381641
  have htrace : WordTrace (prefixWord ++ tailWord_7381641) baseStart_7381641 baseEnd_7381641 := by
    simpa [prefixWord, tailWord_7381641, baseEnd_7381641] using wordTrace_append hprefix tailTrace_7381641
  have hstable : (prefixWord ++ tailWord_7381641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381641).length < 2 ^ (prefixWord ++ tailWord_7381641).sum := by decide
  have hdescent : baseEnd_7381641 < baseStart_7381641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381644 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 5, 2, 3]
def baseStart_7381644 : Nat := 118140960795 + 7381644 * 2 ^ 59
def prefixEnd_7381644 : Nat := 4983230072969 + 3 ^ 40 * 7381644 * 2
def baseEnd_7381644 : Nat := 3790331392377222517602443

theorem tailTrace_7381644 : CollatzResearch.WordTrace tailWord_7381644 prefixEnd_7381644 3790331392377222517602443 := by
  unfold tailWord_7381644
  simp only [CollatzResearch.WordTrace]
  refine ⟨134615337434785973636047993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179487116579714631514730657 134615337434785973636047993)
  ·
    refine ⟨100961503076089480227035995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134615337434785973636047993 100961503076089480227035995)
    ·
      refine ⟨151442254614134220340553993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100961503076089480227035995 151442254614134220340553993)
      ·
        refine ⟨113581690960600665255415495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151442254614134220340553993 113581690960600665255415495)
        ·
          refine ⟨170372536440900997883123243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113581690960600665255415495 170372536440900997883123243)
          ·
            refine ⟨255558804661351496824684865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170372536440900997883123243 255558804661351496824684865)
            ·
              refine ⟨191669103496013622618513649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255558804661351496824684865 191669103496013622618513649)
              ·
                refine ⟨143751827622010216963885237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191669103496013622618513649 143751827622010216963885237)
                ·
                  refine ⟨13476733839563457840364241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143751827622010216963885237 13476733839563457840364241)
                  ·
                    refine ⟨10107550379672593380273181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13476733839563457840364241 10107550379672593380273181)
                    ·
                      refine ⟨3790331392377222517602443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10107550379672593380273181 3790331392377222517602443)
                      ·
                        rfl

theorem cell23_7381644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_7381644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381644 prefixEnd_7381644 := by exact prefixLift 7381644
  have htrace : WordTrace (prefixWord ++ tailWord_7381644) baseStart_7381644 baseEnd_7381644 := by
    simpa [prefixWord, tailWord_7381644, baseEnd_7381644] using wordTrace_append hprefix tailTrace_7381644
  have hstable : (prefixWord ++ tailWord_7381644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381644).length < 2 ^ (prefixWord ++ tailWord_7381644).sum := by decide
  have hdescent : baseEnd_7381644 < baseStart_7381644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381667 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 6]
def baseStart_7381667 : Nat := 118140960795 + 7381667 * 2 ^ 59
def prefixEnd_7381667 : Nat := 4983230072969 + 3 ^ 40 * 7381667 * 2
def baseEnd_7381667 : Nat := 3790343202432275927614837

theorem tailTrace_7381667 : CollatzResearch.WordTrace tailWord_7381667 prefixEnd_7381667 3790343202432275927614837 := by
  unfold tailWord_7381667
  simp only [CollatzResearch.WordTrace]
  refine ⟨269231513748488622200183255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179487675832325748133455503 269231513748488622200183255)
  ·
    refine ⟨403847270622732933300274883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269231513748488622200183255 403847270622732933300274883)
    ·
      refine ⟨605770905934099399950412325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403847270622732933300274883 605770905934099399950412325)
      ·
        refine ⟨113582044862643637490702311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 605770905934099399950412325 113582044862643637490702311)
        ·
          refine ⟨170373067293965456236053467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113582044862643637490702311 170373067293965456236053467)
          ·
            refine ⟨255559600940948184354080201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170373067293965456236053467 255559600940948184354080201)
            ·
              refine ⟨191669700705711138265560151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255559600940948184354080201 191669700705711138265560151)
              ·
                refine ⟨287504551058566707398340227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191669700705711138265560151 287504551058566707398340227)
                ·
                  refine ⟨431256826587850061097510341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287504551058566707398340227 431256826587850061097510341)
                  ·
                    refine ⟨80860654985221886455783189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 431256826587850061097510341 80860654985221886455783189)
                    ·
                      refine ⟨3790343202432275927614837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80860654985221886455783189 3790343202432275927614837)
                      ·
                        rfl

theorem cell23_7381667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_7381667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381667 prefixEnd_7381667 := by exact prefixLift 7381667
  have htrace : WordTrace (prefixWord ++ tailWord_7381667) baseStart_7381667 baseEnd_7381667 := by
    simpa [prefixWord, tailWord_7381667, baseEnd_7381667] using wordTrace_append hprefix tailTrace_7381667
  have hstable : (prefixWord ++ tailWord_7381667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381667).length < 2 ^ (prefixWord ++ tailWord_7381667).sum := by decide
  have hdescent : baseEnd_7381667 < baseStart_7381667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381668 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_7381668 : Nat := 118140960795 + 7381668 * 2 ^ 59
def prefixEnd_7381668 : Nat := 4983230072969 + 3 ^ 40 * 7381668 * 2
def baseEnd_7381668 : Nat := 1263447905304310141234111

theorem tailTrace_7381668 : CollatzResearch.WordTrace tailWord_7381668 prefixEnd_7381668 1263447905304310141234111 := by
  unfold tailWord_7381668
  simp only [CollatzResearch.WordTrace]
  refine ⟨134615775110742499685484829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179487700147656666247313105 134615775110742499685484829)
  ·
    refine ⟨50480915666528437382056811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134615775110742499685484829 50480915666528437382056811)
    ·
      refine ⟨75721373499792656073085217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50480915666528437382056811 75721373499792656073085217)
      ·
        refine ⟨56791030124844492054813913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75721373499792656073085217 56791030124844492054813913)
        ·
          refine ⟨42593272593633369041110435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56791030124844492054813913 42593272593633369041110435)
          ·
            refine ⟨63889908890450053561665653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42593272593633369041110435 63889908890450053561665653)
            ·
              refine ⟨5989678958479692521406155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63889908890450053561665653 5989678958479692521406155)
              ·
                refine ⟨8984518437719538782109233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5989678958479692521406155 8984518437719538782109233)
                ·
                  refine ⟨6738388828289654086581925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8984518437719538782109233 6738388828289654086581925)
                  ·
                    refine ⟨1263447905304310141234111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6738388828289654086581925 1263447905304310141234111)
                    ·
                      rfl

theorem cell23_7381668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_7381668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381668 prefixEnd_7381668 := by exact prefixLift 7381668
  have htrace : WordTrace (prefixWord ++ tailWord_7381668) baseStart_7381668 baseEnd_7381668 := by
    simpa [prefixWord, tailWord_7381668, baseEnd_7381668] using wordTrace_append hprefix tailTrace_7381668
  have hstable : (prefixWord ++ tailWord_7381668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381668).length < 2 ^ (prefixWord ++ tailWord_7381668).sum := by decide
  have hdescent : baseEnd_7381668 < baseStart_7381668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381681 : List Nat := [1, 2, 2, 6, 1, 1, 1, 9]
def baseStart_7381681 : Nat := 118140960795 + 7381681 * 2 ^ 59
def prefixEnd_7381681 : Nat := 4983230072969 + 3 ^ 40 * 7381681 * 2
def baseEnd_7381681 : Nat := 140383347820794032327399

theorem tailTrace_7381681 : CollatzResearch.WordTrace tailWord_7381681 prefixEnd_7381681 140383347820794032327399 := by
  unfold tailWord_7381681
  simp only [CollatzResearch.WordTrace]
  refine ⟨269232024370437902591192897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179488016246958601727461931 269232024370437902591192897)
  ·
    refine ⟨201924018277828426943394673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269232024370437902591192897 201924018277828426943394673)
    ·
      refine ⟨151443013708371320207546005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201924018277828426943394673 151443013708371320207546005)
      ·
        refine ⟨7098891267579905634728719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151443013708371320207546005 7098891267579905634728719)
        ·
          refine ⟨10648336901369858452093079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098891267579905634728719 10648336901369858452093079)
          ·
            refine ⟨15972505352054787678139619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10648336901369858452093079 15972505352054787678139619)
            ·
              refine ⟨23958758028082181517209429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15972505352054787678139619 23958758028082181517209429)
              ·
                refine ⟨140383347820794032327399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23958758028082181517209429 140383347820794032327399)
                ·
                  rfl

theorem cell23_7381681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 9].length) (baseStart_7381681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381681 prefixEnd_7381681 := by exact prefixLift 7381681
  have htrace : WordTrace (prefixWord ++ tailWord_7381681) baseStart_7381681 baseEnd_7381681 := by
    simpa [prefixWord, tailWord_7381681, baseEnd_7381681] using wordTrace_append hprefix tailTrace_7381681
  have hstable : (prefixWord ++ tailWord_7381681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381681).length < 2 ^ (prefixWord ++ tailWord_7381681).sum := by decide
  have hdescent : baseEnd_7381681 < baseStart_7381681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381686 : List Nat := [5, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_7381686 : Nat := 118140960795 + 7381686 * 2 ^ 59
def prefixEnd_7381686 : Nat := 4983230072969 + 3 ^ 40 * 7381686 * 2
def baseEnd_7381686 : Nat := 3790352958564711353277251

theorem tailTrace_7381686 : CollatzResearch.WordTrace tailWord_7381686 prefixEnd_7381686 3790352958564711353277251 := by
  unfold tailWord_7381686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16827012920963736777820307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179488137823613192296749941 16827012920963736777820307)
  ·
    refine ⟨25240519381445605166730461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16827012920963736777820307 25240519381445605166730461)
    ·
      refine ⟨9465194768042101937523923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25240519381445605166730461 9465194768042101937523923)
      ·
        refine ⟨14197792152063152906285885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9465194768042101937523923 14197792152063152906285885)
        ·
          refine ⟨5324172057023682339857207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14197792152063152906285885 5324172057023682339857207)
          ·
            refine ⟨7986258085535523509785811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5324172057023682339857207 7986258085535523509785811)
            ·
              refine ⟨11979387128303285264678717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7986258085535523509785811 11979387128303285264678717)
              ·
                refine ⟨4492270173113731974254519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11979387128303285264678717 4492270173113731974254519)
                ·
                  refine ⟨6738405259670597961381779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4492270173113731974254519 6738405259670597961381779)
                  ·
                    refine ⟨10107607889505896942072669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6738405259670597961381779 10107607889505896942072669)
                    ·
                      refine ⟨3790352958564711353277251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10107607889505896942072669 3790352958564711353277251)
                      ·
                        rfl

theorem cell23_7381686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_7381686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381686 prefixEnd_7381686 := by exact prefixLift 7381686
  have htrace : WordTrace (prefixWord ++ tailWord_7381686) baseStart_7381686 baseEnd_7381686 := by
    simpa [prefixWord, tailWord_7381686, baseEnd_7381686] using wordTrace_append hprefix tailTrace_7381686
  have hstable : (prefixWord ++ tailWord_7381686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381686).length < 2 ^ (prefixWord ++ tailWord_7381686).sum := by decide
  have hdescent : baseEnd_7381686 < baseStart_7381686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381708 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7381708 : Nat := 118140960795 + 7381708 * 2 ^ 59
def prefixEnd_7381708 : Nat := 4983230072969 + 3 ^ 40 * 7381708 * 2
def baseEnd_7381708 : Nat := 3790364255139110267202149

theorem tailTrace_7381708 : CollatzResearch.WordTrace tailWord_7381708 prefixEnd_7381708 3790364255139110267202149 := by
  unfold tailWord_7381708
  simp only [CollatzResearch.WordTrace]
  refine ⟨134616504570670043101212889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179488672760893390801617185 134616504570670043101212889)
  ·
    refine ⟨100962378428002532325909667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134616504570670043101212889 100962378428002532325909667)
    ·
      refine ⟨151443567642003798488864501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100962378428002532325909667 151443567642003798488864501)
      ·
        refine ⟨14197834466437856108331047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151443567642003798488864501 14197834466437856108331047)
        ·
          refine ⟨21296751699656784162496571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14197834466437856108331047 21296751699656784162496571)
          ·
            refine ⟨31945127549485176243744857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21296751699656784162496571 31945127549485176243744857)
            ·
              refine ⟨23958845662113882182808643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31945127549485176243744857 23958845662113882182808643)
              ·
                refine ⟨35938268493170823274212965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23958845662113882182808643 35938268493170823274212965)
                ·
                  refine ⟨6738425342469529363914931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35938268493170823274212965 6738425342469529363914931)
                  ·
                    refine ⟨10107638013704294045872397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6738425342469529363914931 10107638013704294045872397)
                    ·
                      refine ⟨3790364255139110267202149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10107638013704294045872397 3790364255139110267202149)
                      ·
                        rfl

theorem cell23_7381708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7381708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381708 prefixEnd_7381708 := by exact prefixLift 7381708
  have htrace : WordTrace (prefixWord ++ tailWord_7381708) baseStart_7381708 baseEnd_7381708 := by
    simpa [prefixWord, tailWord_7381708, baseEnd_7381708] using wordTrace_append hprefix tailTrace_7381708
  have hstable : (prefixWord ++ tailWord_7381708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381708).length < 2 ^ (prefixWord ++ tailWord_7381708).sum := by decide
  have hdescent : baseEnd_7381708 < baseStart_7381708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381709 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_7381709 : Nat := 118140960795 + 7381709 * 2 ^ 59
def prefixEnd_7381709 : Nat := 4983230072969 + 3 ^ 40 * 7381709 * 2
def baseEnd_7381709 : Nat := 3790364768619764763289645

theorem tailTrace_7381709 : CollatzResearch.WordTrace tailWord_7381709 prefixEnd_7381709 3790364768619764763289645 := by
  unfold tailWord_7381709
  simp only [CollatzResearch.WordTrace]
  refine ⟨269233045614336463373212181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179488697076224308915474787 269233045614336463373212181)
  ·
    refine ⟨12620299013172021720619321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 269233045614336463373212181 12620299013172021720619321)
    ·
      refine ⟨9465224259879016290464491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12620299013172021720619321 9465224259879016290464491)
      ·
        refine ⟨14197836389818524435696737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9465224259879016290464491 14197836389818524435696737)
        ·
          refine ⟨10648377292363893326772553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14197836389818524435696737 10648377292363893326772553)
          ·
            refine ⟨7986282969272919995079415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10648377292363893326772553 7986282969272919995079415)
            ·
              refine ⟨11979424453909379992619123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7986282969272919995079415 11979424453909379992619123)
              ·
                refine ⟨17969136680864069988928685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11979424453909379992619123 17969136680864069988928685)
                ·
                  refine ⟨6738426255324026245848257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17969136680864069988928685 6738426255324026245848257)
                  ·
                    refine ⟨5053819691493019684386193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6738426255324026245848257 5053819691493019684386193)
                    ·
                      refine ⟨3790364768619764763289645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5053819691493019684386193 3790364768619764763289645)
                      ·
                        rfl

theorem cell23_7381709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_7381709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381709 prefixEnd_7381709 := by exact prefixLift 7381709
  have htrace : WordTrace (prefixWord ++ tailWord_7381709) baseStart_7381709 baseEnd_7381709 := by
    simpa [prefixWord, tailWord_7381709, baseEnd_7381709] using wordTrace_append hprefix tailTrace_7381709
  have hstable : (prefixWord ++ tailWord_7381709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381709).length < 2 ^ (prefixWord ++ tailWord_7381709).sum := by decide
  have hdescent : baseEnd_7381709 < baseStart_7381709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381774 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7381774 : Nat := 118140960795 + 7381774 * 2 ^ 59
def prefixEnd_7381774 : Nat := 4983230072969 + 3 ^ 40 * 7381774 * 2
def baseEnd_7381774 : Nat := 3790398144862307008976845

theorem tailTrace_7381774 : CollatzResearch.WordTrace tailWord_7381774 prefixEnd_7381774 3790398144862307008976845 := by
  unfold tailWord_7381774
  simp only [CollatzResearch.WordTrace]
  refine ⟨33654427044887622434291047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179490277572733986316218917 33654427044887622434291047)
  ·
    refine ⟨50481640567331433651436571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33654427044887622434291047 50481640567331433651436571)
    ·
      refine ⟨75722460850997150477154857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50481640567331433651436571 75722460850997150477154857)
      ·
        refine ⟨56791845638247862857866143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75722460850997150477154857 56791845638247862857866143)
        ·
          refine ⟨85187768457371794286799215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56791845638247862857866143 85187768457371794286799215)
          ·
            refine ⟨127781652686057691430198823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85187768457371794286799215 127781652686057691430198823)
            ·
              refine ⟨191672479029086537145298235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127781652686057691430198823 191672479029086537145298235)
              ·
                refine ⟨287508718543629805717947353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191672479029086537145298235 287508718543629805717947353)
                ·
                  refine ⟨215631538907722354288460515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287508718543629805717947353 215631538907722354288460515)
                  ·
                    refine ⟨323447308361583531432690773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 215631538907722354288460515 323447308361583531432690773)
                    ·
                      refine ⟨3790398144862307008976845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 323447308361583531432690773 3790398144862307008976845)
                      ·
                        rfl

theorem cell23_7381774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7381774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381774 prefixEnd_7381774 := by exact prefixLift 7381774
  have htrace : WordTrace (prefixWord ++ tailWord_7381774) baseStart_7381774 baseEnd_7381774 := by
    simpa [prefixWord, tailWord_7381774, baseEnd_7381774] using wordTrace_append hprefix tailTrace_7381774
  have hstable : (prefixWord ++ tailWord_7381774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381774).length < 2 ^ (prefixWord ++ tailWord_7381774).sum := by decide
  have hdescent : baseEnd_7381774 < baseStart_7381774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381781 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_7381781 : Nat := 118140960795 + 7381781 * 2 ^ 59
def prefixEnd_7381781 : Nat := 4983230072969 + 3 ^ 40 * 7381781 * 2
def baseEnd_7381781 : Nat := 3790401739226888481589313

theorem tailTrace_7381781 : CollatzResearch.WordTrace tailWord_7381781 prefixEnd_7381781 3790401739226888481589313 := by
  unfold tailWord_7381781
  simp only [CollatzResearch.WordTrace]
  refine ⟨269235671670075619669833197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179490447780050413113222131 269235671670075619669833197)
  ·
    refine ⟨100963376876278357376187449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269235671670075619669833197 100963376876278357376187449)
    ·
      refine ⟨75722532657208768032140587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100963376876278357376187449 75722532657208768032140587)
      ·
        refine ⟨113583798985813152048210881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75722532657208768032140587 113583798985813152048210881)
        ·
          refine ⟨85187849239359864036158161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113583798985813152048210881 85187849239359864036158161)
          ·
            refine ⟨63890886929519898027118621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85187849239359864036158161 63890886929519898027118621)
            ·
              refine ⟨23959082598569961760169483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63890886929519898027118621 23959082598569961760169483)
              ·
                refine ⟨35938623897854942640254225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23959082598569961760169483 35938623897854942640254225)
                ·
                  refine ⟨26953967923391206980190669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35938623897854942640254225 26953967923391206980190669)
                  ·
                    refine ⟨10107737971271702617571501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26953967923391206980190669 10107737971271702617571501)
                    ·
                      refine ⟨3790401739226888481589313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10107737971271702617571501 3790401739226888481589313)
                      ·
                        rfl

theorem cell23_7381781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_7381781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381781 prefixEnd_7381781 := by exact prefixLift 7381781
  have htrace : WordTrace (prefixWord ++ tailWord_7381781) baseStart_7381781 baseEnd_7381781 := by
    simpa [prefixWord, tailWord_7381781, baseEnd_7381781] using wordTrace_append hprefix tailTrace_7381781
  have hstable : (prefixWord ++ tailWord_7381781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381781).length < 2 ^ (prefixWord ++ tailWord_7381781).sum := by decide
  have hdescent : baseEnd_7381781 < baseStart_7381781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381784 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 1, 7]
def baseStart_7381784 : Nat := 118140960795 + 7381784 * 2 ^ 59
def prefixEnd_7381784 : Nat := 4983230072969 + 3 ^ 40 * 7381784 * 2
def baseEnd_7381784 : Nat := 1263467759889617323283933

theorem tailTrace_7381784 : CollatzResearch.WordTrace tailWord_7381784 prefixEnd_7381784 1263467759889617323283933 := by
  unfold tailWord_7381784
  simp only [CollatzResearch.WordTrace]
  refine ⟨134617890544532375591096203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179490520726043167454794937 134617890544532375591096203)
  ·
    refine ⟨201926835816798563386644305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134617890544532375591096203 201926835816798563386644305)
    ·
      refine ⟨151445126862598922539983229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201926835816798563386644305 151445126862598922539983229)
      ·
        refine ⟨56791922573474595952493711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151445126862598922539983229 56791922573474595952493711)
        ·
          refine ⟨85187883860211893928740567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56791922573474595952493711 85187883860211893928740567)
          ·
            refine ⟨127781825790317840893110851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85187883860211893928740567 127781825790317840893110851)
            ·
              refine ⟨191672738685476761339666277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127781825790317840893110851 191672738685476761339666277)
              ·
                refine ⟨35938638503526892751187427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191672738685476761339666277 35938638503526892751187427)
                ·
                  refine ⟨53907957755290339126781141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35938638503526892751187427 53907957755290339126781141)
                  ·
                    refine ⟨1263467759889617323283933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53907957755290339126781141 1263467759889617323283933)
                    ·
                      rfl

theorem cell23_7381784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_7381784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381784 prefixEnd_7381784 := by exact prefixLift 7381784
  have htrace : WordTrace (prefixWord ++ tailWord_7381784) baseStart_7381784 baseEnd_7381784 := by
    simpa [prefixWord, tailWord_7381784, baseEnd_7381784] using wordTrace_append hprefix tailTrace_7381784
  have hstable : (prefixWord ++ tailWord_7381784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381784).length < 2 ^ (prefixWord ++ tailWord_7381784).sum := by decide
  have hdescent : baseEnd_7381784 < baseStart_7381784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381824 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_7381824 : Nat := 118140960795 + 7381824 * 2 ^ 59
def prefixEnd_7381824 : Nat := 4983230072969 + 3 ^ 40 * 7381824 * 2
def baseEnd_7381824 : Nat := 3790423818895031813351615

theorem tailTrace_7381824 : CollatzResearch.WordTrace tailWord_7381824 prefixEnd_7381824 3790423818895031813351615 := by
  unfold tailWord_7381824
  simp only [CollatzResearch.WordTrace]
  refine ⟨134618620004459919006824263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179491493339279892009099017 134618620004459919006824263)
  ·
    refine ⟨201927930006689878510236395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134618620004459919006824263 201927930006689878510236395)
    ·
      refine ⟨302891895010034817765354593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201927930006689878510236395 302891895010034817765354593)
      ·
        refine ⟨227168921257526113324015945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302891895010034817765354593 227168921257526113324015945)
        ·
          refine ⟨170376690943144584993011959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227168921257526113324015945 170376690943144584993011959)
          ·
            refine ⟨255565036414716877489517939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170376690943144584993011959 255565036414716877489517939)
            ·
              refine ⟨383347554622075316234276909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255565036414716877489517939 383347554622075316234276909)
              ·
                refine ⟨143755332983278243587853841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383347554622075316234276909 143755332983278243587853841)
                ·
                  refine ⟨107816499737458682690890381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143755332983278243587853841 107816499737458682690890381)
                  ·
                    refine ⟨40431187401547006009083893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107816499737458682690890381 40431187401547006009083893)
                    ·
                      refine ⟨3790423818895031813351615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40431187401547006009083893 3790423818895031813351615)
                      ·
                        rfl

theorem cell23_7381824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_7381824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381824 prefixEnd_7381824 := by exact prefixLift 7381824
  have htrace : WordTrace (prefixWord ++ tailWord_7381824) baseStart_7381824 baseEnd_7381824 := by
    simpa [prefixWord, tailWord_7381824, baseEnd_7381824] using wordTrace_append hprefix tailTrace_7381824
  have hstable : (prefixWord ++ tailWord_7381824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381824).length < 2 ^ (prefixWord ++ tailWord_7381824).sum := by decide
  have hdescent : baseEnd_7381824 < baseStart_7381824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381878 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_7381878 : Nat := 118140960795 + 7381878 * 2 ^ 59
def prefixEnd_7381878 : Nat := 4983230072969 + 3 ^ 40 * 7381878 * 2
def baseEnd_7381878 : Nat := 421161282983374955786263

theorem tailTrace_7381878 : CollatzResearch.WordTrace tailWord_7381878 prefixEnd_7381878 421161282983374955786263 := by
  unfold tailWord_7381878
  simp only [CollatzResearch.WordTrace]
  refine ⟨16827450596920262827257143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179492806367149470157409525 16827450596920262827257143)
  ·
    refine ⟨25241175895380394240885715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16827450596920262827257143 25241175895380394240885715)
    ·
      refine ⟨37861763843070591361328573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25241175895380394240885715 37861763843070591361328573)
      ·
        refine ⟨14198161441151471760498215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37861763843070591361328573 14198161441151471760498215)
        ·
          refine ⟨21297242161727207640747323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14198161441151471760498215 21297242161727207640747323)
          ·
            refine ⟨31945863242590811461120985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21297242161727207640747323 31945863242590811461120985)
            ·
              refine ⟨23959397431943108595840739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31945863242590811461120985 23959397431943108595840739)
              ·
                refine ⟨35939096147914662893761109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23959397431943108595840739 35939096147914662893761109)
                ·
                  refine ⟨421161282983374955786263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35939096147914662893761109 421161282983374955786263)
                  ·
                    rfl

theorem cell23_7381878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_7381878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381878 prefixEnd_7381878 := by exact prefixLift 7381878
  have htrace : WordTrace (prefixWord ++ tailWord_7381878) baseStart_7381878 baseEnd_7381878 := by
    simpa [prefixWord, tailWord_7381878, baseEnd_7381878] using wordTrace_append hprefix tailTrace_7381878
  have hstable : (prefixWord ++ tailWord_7381878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381878).length < 2 ^ (prefixWord ++ tailWord_7381878).sum := by decide
  have hdescent : baseEnd_7381878 < baseStart_7381878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381888 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 3, 1, 3]
def baseStart_7381888 : Nat := 118140960795 + 7381888 * 2 ^ 59
def prefixEnd_7381888 : Nat := 4983230072969 + 3 ^ 40 * 7381888 * 2
def baseEnd_7381888 : Nat := 3790456681656919562951321

theorem tailTrace_7381888 : CollatzResearch.WordTrace tailWord_7381888 prefixEnd_7381888 3790456681656919562951321 := by
  unfold tailWord_7381888
  simp only [CollatzResearch.WordTrace]
  refine ⟨134619787140343988471989159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179493049520458651295985545 134619787140343988471989159)
  ·
    refine ⟨201929680710515982707983739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134619787140343988471989159 201929680710515982707983739)
    ·
      refine ⟨302894521065773974061975609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201929680710515982707983739 302894521065773974061975609)
      ·
        refine ⟨227170890799330480546481707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302894521065773974061975609 227170890799330480546481707)
        ·
          refine ⟨340756336198995720819722561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227170890799330480546481707 340756336198995720819722561)
          ·
            refine ⟨255567252149246790614791921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340756336198995720819722561 255567252149246790614791921)
            ·
              refine ⟨191675439111935092961093941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255567252149246790614791921 191675439111935092961093941)
              ·
                refine ⟨17969572416743914965102557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191675439111935092961093941 17969572416743914965102557)
                ·
                  refine ⟨6738589656278968111913459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17969572416743914965102557 6738589656278968111913459)
                  ·
                    refine ⟨10107884484418452167870189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6738589656278968111913459 10107884484418452167870189)
                    ·
                      refine ⟨3790456681656919562951321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10107884484418452167870189 3790456681656919562951321)
                      ·
                        rfl

theorem cell23_7381888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_7381888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381888 prefixEnd_7381888 := by exact prefixLift 7381888
  have htrace : WordTrace (prefixWord ++ tailWord_7381888) baseStart_7381888 baseEnd_7381888 := by
    simpa [prefixWord, tailWord_7381888, baseEnd_7381888] using wordTrace_append hprefix tailTrace_7381888
  have hstable : (prefixWord ++ tailWord_7381888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381888).length < 2 ^ (prefixWord ++ tailWord_7381888).sum := by decide
  have hdescent : baseEnd_7381888 < baseStart_7381888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381891 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 3, 5]
def baseStart_7381891 : Nat := 118140960795 + 7381891 * 2 ^ 59
def prefixEnd_7381891 : Nat := 4983230072969 + 3 ^ 40 * 7381891 * 2
def baseEnd_7381891 : Nat := 1263486074032961017071269

theorem tailTrace_7381891 : CollatzResearch.WordTrace tailWord_7381891 prefixEnd_7381891 1263486074032961017071269 := by
  unfold tailWord_7381891
  simp only [CollatzResearch.WordTrace]
  refine ⟨269239683699677108456337527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179493122466451405637558351 269239683699677108456337527)
  ·
    refine ⟨403859525549515662684506291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269239683699677108456337527 403859525549515662684506291)
    ·
      refine ⟨605789288324273494026759437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403859525549515662684506291 605789288324273494026759437)
      ·
        refine ⟨227170983121602560260034789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605789288324273494026759437 227170983121602560260034789)
        ·
          refine ⟨42594559335300480048756523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227170983121602560260034789 42594559335300480048756523)
          ·
            refine ⟨63891839002950720073134785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42594559335300480048756523 63891839002950720073134785)
            ·
              refine ⟨47918879252213040054851089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63891839002950720073134785 47918879252213040054851089)
              ·
                refine ⟨35939159439159780041138317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47918879252213040054851089 35939159439159780041138317)
                ·
                  refine ⟨13477184789684917515426869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35939159439159780041138317 13477184789684917515426869)
                  ·
                    refine ⟨1263486074032961017071269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13477184789684917515426869 1263486074032961017071269)
                    ·
                      rfl

theorem cell23_7381891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 5].length) (baseStart_7381891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381891 prefixEnd_7381891 := by exact prefixLift 7381891
  have htrace : WordTrace (prefixWord ++ tailWord_7381891) baseStart_7381891 baseEnd_7381891 := by
    simpa [prefixWord, tailWord_7381891, baseEnd_7381891] using wordTrace_append hprefix tailTrace_7381891
  have hstable : (prefixWord ++ tailWord_7381891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381891).length < 2 ^ (prefixWord ++ tailWord_7381891).sum := by decide
  have hdescent : baseEnd_7381891 < baseStart_7381891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381895 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 6]
def baseStart_7381895 : Nat := 118140960795 + 7381895 * 2 ^ 59
def prefixEnd_7381895 : Nat := 4983230072969 + 3 ^ 40 * 7381895 * 2
def baseEnd_7381895 : Nat := 421162252891277892840421

theorem tailTrace_7381895 : CollatzResearch.WordTrace tailWord_7381895 prefixEnd_7381895 421162252891277892840421 := by
  unfold tailWord_7381895
  simp only [CollatzResearch.WordTrace]
  refine ⟨269239829591662617139483139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179493219727775078092988759 269239829591662617139483139)
  ·
    refine ⟨403859744387493925709224709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269239829591662617139483139 403859744387493925709224709)
    ·
      refine ⟨75723702072655111070479633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403859744387493925709224709 75723702072655111070479633)
      ·
        refine ⟨56792776554491333302859725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75723702072655111070479633 56792776554491333302859725)
        ·
          refine ⟨21297291207934249988572397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56792776554491333302859725 21297291207934249988572397)
          ·
            refine ⟨7986484202975343745714649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21297291207934249988572397 7986484202975343745714649)
            ·
              refine ⟨5989863152231507809285987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7986484202975343745714649 5989863152231507809285987)
              ·
                refine ⟨8984794728347261713928981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5989863152231507809285987 8984794728347261713928981)
                ·
                  refine ⟨421162252891277892840421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8984794728347261713928981 421162252891277892840421)
                  ·
                    rfl

theorem cell23_7381895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 6].length) (baseStart_7381895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381895 prefixEnd_7381895 := by exact prefixLift 7381895
  have htrace : WordTrace (prefixWord ++ tailWord_7381895) baseStart_7381895 baseEnd_7381895 := by
    simpa [prefixWord, tailWord_7381895, baseEnd_7381895] using wordTrace_append hprefix tailTrace_7381895
  have hstable : (prefixWord ++ tailWord_7381895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381895).length < 2 ^ (prefixWord ++ tailWord_7381895).sum := by decide
  have hdescent : baseEnd_7381895 < baseStart_7381895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381908 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_7381908 : Nat := 118140960795 + 7381908 * 2 ^ 59
def prefixEnd_7381908 : Nat := 4983230072969 + 3 ^ 40 * 7381908 * 2
def baseEnd_7381908 : Nat := 1263488983756669828233743

theorem tailTrace_7381908 : CollatzResearch.WordTrace tailWord_7381908 prefixEnd_7381908 1263488983756669828233743 := by
  unfold tailWord_7381908
  simp only [CollatzResearch.WordTrace]
  refine ⟨134620151870307760179853189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179493535827077013573137585 134620151870307760179853189)
  ·
    refine ⟨25241278475682705033722473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134620151870307760179853189 25241278475682705033722473)
    ·
      refine ⟨18930958856762028775291855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25241278475682705033722473 18930958856762028775291855)
      ·
        refine ⟨28396438285143043162937783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18930958856762028775291855 28396438285143043162937783)
        ·
          refine ⟨42594657427714564744406675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28396438285143043162937783 42594657427714564744406675)
          ·
            refine ⟨63891986141571847116610013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42594657427714564744406675 63891986141571847116610013)
            ·
              refine ⟨23959494803089442668728755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63891986141571847116610013 23959494803089442668728755)
              ·
                refine ⟨35939242204634164003093133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23959494803089442668728755 35939242204634164003093133)
                ·
                  refine ⟨13477215826737811501159925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35939242204634164003093133 13477215826737811501159925)
                  ·
                    refine ⟨1263488983756669828233743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13477215826737811501159925 1263488983756669828233743)
                    ·
                      rfl

theorem cell23_7381908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_7381908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381908 prefixEnd_7381908 := by exact prefixLift 7381908
  have htrace : WordTrace (prefixWord ++ tailWord_7381908) baseStart_7381908 baseEnd_7381908 := by
    simpa [prefixWord, tailWord_7381908, baseEnd_7381908] using wordTrace_append hprefix tailTrace_7381908
  have hstable : (prefixWord ++ tailWord_7381908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381908).length < 2 ^ (prefixWord ++ tailWord_7381908).sum := by decide
  have hdescent : baseEnd_7381908 < baseStart_7381908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381933 : List Nat := [1, 5, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_7381933 : Nat := 118140960795 + 7381933 * 2 ^ 59
def prefixEnd_7381933 : Nat := 4983230072969 + 3 ^ 40 * 7381933 * 2
def baseEnd_7381933 : Nat := 1263493262762123962296205

theorem tailTrace_7381933 : CollatzResearch.WordTrace tailWord_7381933 prefixEnd_7381933 1263493262762123962296205 := by
  unfold tailWord_7381933
  simp only [CollatzResearch.WordTrace]
  refine ⟨269241215565524949629366453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179494143710349966419577635 269241215565524949629366453)
  ·
    refine ⟨25241363959267964027753105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269241215565524949629366453 25241363959267964027753105)
    ·
      refine ⟨18931022969450973020814829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25241363959267964027753105 18931022969450973020814829)
      ·
        refine ⟨7099133613544114882805561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18931022969450973020814829 7099133613544114882805561)
        ·
          refine ⟨5324350210158086162104171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7099133613544114882805561 5324350210158086162104171)
          ·
            refine ⟨7986525315237129243156257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5324350210158086162104171 7986525315237129243156257)
            ·
              refine ⟨5989893986427846932367193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7986525315237129243156257 5989893986427846932367193)
              ·
                refine ⟨4492420489820885199275395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5989893986427846932367193 4492420489820885199275395)
                ·
                  refine ⟨6738630734731327798913093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4492420489820885199275395 6738630734731327798913093)
                  ·
                    refine ⟨1263493262762123962296205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6738630734731327798913093 1263493262762123962296205)
                    ·
                      rfl

theorem cell23_7381933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_7381933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381933 prefixEnd_7381933 := by exact prefixLift 7381933
  have htrace : WordTrace (prefixWord ++ tailWord_7381933) baseStart_7381933 baseEnd_7381933 := by
    simpa [prefixWord, tailWord_7381933, baseEnd_7381933] using wordTrace_append hprefix tailTrace_7381933
  have hstable : (prefixWord ++ tailWord_7381933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381933).length < 2 ^ (prefixWord ++ tailWord_7381933).sum := by decide
  have hdescent : baseEnd_7381933 < baseStart_7381933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7381989 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_7381989 : Nat := 118140960795 + 7381989 * 2 ^ 59
def prefixEnd_7381989 : Nat := 4983230072969 + 3 ^ 40 * 7381989 * 2
def baseEnd_7381989 : Nat := 1263502847734341222596119

theorem tailTrace_7381989 : CollatzResearch.WordTrace tailWord_7381989 prefixEnd_7381989 1263502847734341222596119 := by
  unfold tailWord_7381989
  simp only [CollatzResearch.WordTrace]
  refine ⟨269243258053322071193405021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179495505368881380795603347 269243258053322071193405021)
  ·
    refine ⟨100966221769995776697526883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269243258053322071193405021 100966221769995776697526883)
    ·
      refine ⟨151449332654993665046290325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100966221769995776697526883 151449332654993665046290325)
      ·
        refine ⟨7099187468202828049044859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151449332654993665046290325 7099187468202828049044859)
        ·
          refine ⟨10648781202304242073567289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099187468202828049044859 10648781202304242073567289)
          ·
            refine ⟨7986585901728181555175467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10648781202304242073567289 7986585901728181555175467)
            ·
              refine ⟨11979878852592272332763201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7986585901728181555175467 11979878852592272332763201)
              ·
                refine ⟨8984909139444204249572401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11979878852592272332763201 8984909139444204249572401)
                ·
                  refine ⟨6738681854583153187179301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8984909139444204249572401 6738681854583153187179301)
                  ·
                    refine ⟨1263502847734341222596119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6738681854583153187179301 1263502847734341222596119)
                    ·
                      rfl

theorem cell23_7381989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_7381989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7381989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7381989 prefixEnd_7381989 := by exact prefixLift 7381989
  have htrace : WordTrace (prefixWord ++ tailWord_7381989) baseStart_7381989 baseEnd_7381989 := by
    simpa [prefixWord, tailWord_7381989, baseEnd_7381989] using wordTrace_append hprefix tailTrace_7381989
  have hstable : (prefixWord ++ tailWord_7381989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7381989).length < 2 ^ (prefixWord ++ tailWord_7381989).sum := by decide
  have hdescent : baseEnd_7381989 < baseStart_7381989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7381989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382041 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 9]
def baseStart_7382041 : Nat := 118140960795 + 7382041 * 2 ^ 59
def prefixEnd_7382041 : Nat := 4983230072969 + 3 ^ 40 * 7382041 * 2
def baseEnd_7382041 : Nat := 421170582688561940482013

theorem tailTrace_7382041 : CollatzResearch.WordTrace tailWord_7382041 prefixEnd_7382041 421170582688561940482013 := by
  unfold tailWord_7382041
  simp only [CollatzResearch.WordTrace]
  refine ⟨269245154649133684074297977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179496769766089122716198651 269245154649133684074297977)
  ·
    refine ⟨201933865986850263055723483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269245154649133684074297977 201933865986850263055723483)
    ·
      refine ⟨302900798980275394583585225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201933865986850263055723483 302900798980275394583585225)
      ·
        refine ⟨227175599235206545937688919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302900798980275394583585225 227175599235206545937688919)
        ·
          refine ⟨340763398852809818906533379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227175599235206545937688919 340763398852809818906533379)
          ·
            refine ⟨511145098279214728359800069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340763398852809818906533379 511145098279214728359800069)
            ·
              refine ⟨95839705927352761567462513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 511145098279214728359800069 95839705927352761567462513)
              ·
                refine ⟨71879779445514571175596885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95839705927352761567462513 71879779445514571175596885)
                ·
                  refine ⟨421170582688561940482013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71879779445514571175596885 421170582688561940482013)
                  ·
                    rfl

theorem cell23_7382041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 9].length) (baseStart_7382041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382041 prefixEnd_7382041 := by exact prefixLift 7382041
  have htrace : WordTrace (prefixWord ++ tailWord_7382041) baseStart_7382041 baseEnd_7382041 := by
    simpa [prefixWord, tailWord_7382041, baseEnd_7382041] using wordTrace_append hprefix tailTrace_7382041
  have hstable : (prefixWord ++ tailWord_7382041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382041).length < 2 ^ (prefixWord ++ tailWord_7382041).sum := by decide
  have hdescent : baseEnd_7382041 < baseStart_7382041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382109 : List Nat := [1, 4, 4, 1, 2, 1, 1, 4, 5]
def baseStart_7382109 : Nat := 118140960795 + 7382109 * 2 ^ 59
def prefixEnd_7382109 : Nat := 4983230072969 + 3 ^ 40 * 7382109 * 2
def baseEnd_7382109 : Nat := 421174462320173688698645

theorem tailTrace_7382109 : CollatzResearch.WordTrace tailWord_7382109 prefixEnd_7382109 421174462320173688698645 := by
  unfold tailWord_7382109
  simp only [CollatzResearch.WordTrace]
  refine ⟨269247634812887331687773381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179498423208591554458515587 269247634812887331687773381)
  ·
    refine ⟨50483931527416374691457509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269247634812887331687773381 50483931527416374691457509)
    ·
      refine ⟨9465737161390570254648283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50483931527416374691457509 9465737161390570254648283)
      ·
        refine ⟨14198605742085855381972425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9465737161390570254648283 14198605742085855381972425)
        ·
          refine ⟨10648954306564391536479319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14198605742085855381972425 10648954306564391536479319)
          ·
            refine ⟨15973431459846587304718979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10648954306564391536479319 15973431459846587304718979)
            ·
              refine ⟨23960147189769880957078469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15973431459846587304718979 23960147189769880957078469)
              ·
                refine ⟨4492527598081852679452213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23960147189769880957078469 4492527598081852679452213)
                ·
                  refine ⟨421174462320173688698645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4492527598081852679452213 421174462320173688698645)
                  ·
                    rfl

theorem cell23_7382109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_7382109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382109 prefixEnd_7382109 := by exact prefixLift 7382109
  have htrace : WordTrace (prefixWord ++ tailWord_7382109) baseStart_7382109 baseEnd_7382109 := by
    simpa [prefixWord, tailWord_7382109, baseEnd_7382109] using wordTrace_append hprefix tailTrace_7382109
  have hstable : (prefixWord ++ tailWord_7382109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382109).length < 2 ^ (prefixWord ++ tailWord_7382109).sum := by decide
  have hdescent : baseEnd_7382109 < baseStart_7382109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382135 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 3, 4]
def baseStart_7382135 : Nat := 118140960795 + 7382135 * 2 ^ 59
def prefixEnd_7382135 : Nat := 4983230072969 + 3 ^ 40 * 7382135 * 2
def baseEnd_7382135 : Nat := 1263527837126193365520895

theorem tailTrace_7382135 : CollatzResearch.WordTrace tailWord_7382135 prefixEnd_7382135 1263527837126193365520895 := by
  unfold tailWord_7382135
  simp only [CollatzResearch.WordTrace]
  refine ⟨269248583110793138128219859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179499055407195425418813239 269248583110793138128219859)
  ·
    refine ⟨403872874666189707192329789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269248583110793138128219859 403872874666189707192329789)
    ·
      refine ⟨151452327999821140197123671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403872874666189707192329789 151452327999821140197123671)
      ·
        refine ⟨227178491999731710295685507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151452327999821140197123671 227178491999731710295685507)
        ·
          refine ⟨340767737999597565443528261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227178491999731710295685507 340767737999597565443528261)
          ·
            refine ⟨63893950874924543520661549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340767737999597565443528261 63893950874924543520661549)
            ·
              refine ⟨23960231578096703820248081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63893950874924543520661549 23960231578096703820248081)
              ·
                refine ⟨17970173683572527865186061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23960231578096703820248081 17970173683572527865186061)
                ·
                  refine ⟨6738815131339697949444773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17970173683572527865186061 6738815131339697949444773)
                  ·
                    refine ⟨1263527837126193365520895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6738815131339697949444773 1263527837126193365520895)
                    ·
                      rfl

theorem cell23_7382135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_7382135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382135 prefixEnd_7382135 := by exact prefixLift 7382135
  have htrace : WordTrace (prefixWord ++ tailWord_7382135) baseStart_7382135 baseEnd_7382135 := by
    simpa [prefixWord, tailWord_7382135, baseEnd_7382135] using wordTrace_append hprefix tailTrace_7382135
  have hstable : (prefixWord ++ tailWord_7382135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382135).length < 2 ^ (prefixWord ++ tailWord_7382135).sum := by decide
  have hdescent : baseEnd_7382135 < baseStart_7382135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382195 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 1, 5]
def baseStart_7382195 : Nat := 118140960795 + 7382195 * 2 ^ 59
def prefixEnd_7382195 : Nat := 4983230072969 + 3 ^ 40 * 7382195 * 2
def baseEnd_7382195 : Nat := 1263538106739283287270803

theorem tailTrace_7382195 : CollatzResearch.WordTrace tailWord_7382195 prefixEnd_7382195 1263538106739283287270803 := by
  unfold tailWord_7382195
  simp only [CollatzResearch.WordTrace]
  refine ⟨269250771490575768375404039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179500514327050512250269359 269250771490575768375404039)
  ·
    refine ⟨403876157235863652563106059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269250771490575768375404039 403876157235863652563106059)
    ·
      refine ⟨605814235853795478844659089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403876157235863652563106059 605814235853795478844659089)
      ·
        refine ⟨454360676890346609133494317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605814235853795478844659089 454360676890346609133494317)
        ·
          refine ⟨170385253833879978425060369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454360676890346609133494317 170385253833879978425060369)
          ·
            refine ⟨127788940375409983818795277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170385253833879978425060369 127788940375409983818795277)
            ·
              refine ⟨47920852640778743932048229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127788940375409983818795277 47920852640778743932048229)
              ·
                refine ⟨8985159870146014487259043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47920852640778743932048229 8985159870146014487259043)
                ·
                  refine ⟨13477739805219021730888565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8985159870146014487259043 13477739805219021730888565)
                  ·
                    refine ⟨1263538106739283287270803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13477739805219021730888565 1263538106739283287270803)
                    ·
                      rfl

theorem cell23_7382195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 5].length) (baseStart_7382195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382195 prefixEnd_7382195 := by exact prefixLift 7382195
  have htrace : WordTrace (prefixWord ++ tailWord_7382195) baseStart_7382195 baseEnd_7382195 := by
    simpa [prefixWord, tailWord_7382195, baseEnd_7382195] using wordTrace_append hprefix tailTrace_7382195
  have hstable : (prefixWord ++ tailWord_7382195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382195).length < 2 ^ (prefixWord ++ tailWord_7382195).sum := by decide
  have hdescent : baseEnd_7382195 < baseStart_7382195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382202 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2]
def baseStart_7382202 : Nat := 118140960795 + 7382202 * 2 ^ 59
def prefixEnd_7382202 : Nat := 4983230072969 + 3 ^ 40 * 7382202 * 2
def baseEnd_7382202 : Nat := 3790617914582431334424877

theorem tailTrace_7382202 : CollatzResearch.WordTrace tailWord_7382202 prefixEnd_7382202 3790617914582431334424877 := by
  unfold tailWord_7382202
  simp only [CollatzResearch.WordTrace]
  refine ⟨67312756700387602142727215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179500684534366939047272573 67312756700387602142727215)
  ·
    refine ⟨100969135050581403214090823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67312756700387602142727215 100969135050581403214090823)
    ·
      refine ⟨151453702575872104821136235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100969135050581403214090823 151453702575872104821136235)
      ·
        refine ⟨227180553863808157231704353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151453702575872104821136235 227180553863808157231704353)
        ·
          refine ⟨170385415397856117923778265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227180553863808157231704353 170385415397856117923778265)
          ·
            refine ⟨127789061548392088442833699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170385415397856117923778265 127789061548392088442833699)
            ·
              refine ⟨191683592322588132664250549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127789061548392088442833699 191683592322588132664250549)
              ·
                refine ⟨17970336780242637437273489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191683592322588132664250549 17970336780242637437273489)
                ·
                  refine ⟨13477752585181978077955117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17970336780242637437273489 13477752585181978077955117)
                  ·
                    refine ⟨5054157219443241779233169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13477752585181978077955117 5054157219443241779233169)
                    ·
                      refine ⟨3790617914582431334424877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5054157219443241779233169 3790617914582431334424877)
                      ·
                        rfl

theorem cell23_7382202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_7382202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382202 prefixEnd_7382202 := by exact prefixLift 7382202
  have htrace : WordTrace (prefixWord ++ tailWord_7382202) baseStart_7382202 baseEnd_7382202 := by
    simpa [prefixWord, tailWord_7382202, baseEnd_7382202] using wordTrace_append hprefix tailTrace_7382202
  have hstable : (prefixWord ++ tailWord_7382202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382202).length < 2 ^ (prefixWord ++ tailWord_7382202).sum := by decide
  have hdescent : baseEnd_7382202 < baseStart_7382202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382252 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 3]
def baseStart_7382252 : Nat := 118140960795 + 7382252 * 2 ^ 59
def prefixEnd_7382252 : Nat := 4983230072969 + 3 ^ 40 * 7382252 * 2
def baseEnd_7382252 : Nat := 3790643588615156138799647

theorem tailTrace_7382252 : CollatzResearch.WordTrace tailWord_7382252 prefixEnd_7382252 3790643588615156138799647 := by
  unfold tailWord_7382252
  simp only [CollatzResearch.WordTrace]
  refine ⟨134626425225684633555114505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179501900300912844740152673 134626425225684633555114505)
  ·
    refine ⟨100969818919263475166335879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134626425225684633555114505 100969818919263475166335879)
    ·
      refine ⟨151454728378895212749503819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100969818919263475166335879 151454728378895212749503819)
      ·
        refine ⟨227182092568342819124255729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151454728378895212749503819 227182092568342819124255729)
        ·
          refine ⟨170386569426257114343191797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227182092568342819124255729 170386569426257114343191797)
          ·
            refine ⟨15973740883711604469674231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170386569426257114343191797 15973740883711604469674231)
            ·
              refine ⟨23960611325567406704511347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15973740883711604469674231 23960611325567406704511347)
              ·
                refine ⟨35940916988351110056767021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23960611325567406704511347 35940916988351110056767021)
                ·
                  refine ⟨13477843870631666271287633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35940916988351110056767021 13477843870631666271287633)
                  ·
                    refine ⟨10108382902973749703465725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13477843870631666271287633 10108382902973749703465725)
                    ·
                      refine ⟨3790643588615156138799647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10108382902973749703465725 3790643588615156138799647)
                      ·
                        rfl

theorem cell23_7382252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_7382252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382252 prefixEnd_7382252 := by exact prefixLift 7382252
  have htrace : WordTrace (prefixWord ++ tailWord_7382252) baseStart_7382252 baseEnd_7382252 := by
    simpa [prefixWord, tailWord_7382252, baseEnd_7382252] using wordTrace_append hprefix tailTrace_7382252
  have hstable : (prefixWord ++ tailWord_7382252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382252).length < 2 ^ (prefixWord ++ tailWord_7382252).sum := by decide
  have hdescent : baseEnd_7382252 < baseStart_7382252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382266 : List Nat := [3, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2]
def baseStart_7382266 : Nat := 118140960795 + 7382266 * 2 ^ 59
def prefixEnd_7382266 : Nat := 4983230072969 + 3 ^ 40 * 7382266 * 2
def baseEnd_7382266 : Nat := 3790650777344319084024583

theorem tailTrace_7382266 : CollatzResearch.WordTrace tailWord_7382266 prefixEnd_7382266 3790650777344319084024583 := by
  unfold tailWord_7382266
  simp only [CollatzResearch.WordTrace]
  refine ⟨67313340268329636875309663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179502240715545698334159101 67313340268329636875309663)
  ·
    refine ⟨100970010402494455312964495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67313340268329636875309663 100970010402494455312964495)
    ·
      refine ⟨151455015603741682969446743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100970010402494455312964495 151455015603741682969446743)
      ·
        refine ⟨227182523405612524454170115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151455015603741682969446743 227182523405612524454170115)
        ·
          refine ⟨340773785108418786681255173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227182523405612524454170115 340773785108418786681255173)
          ·
            refine ⟨63895084707828522502735345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340773785108418786681255173 63895084707828522502735345)
            ·
              refine ⟨47921313530871391877051509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63895084707828522502735345 47921313530871391877051509)
              ·
                refine ⟨4492623143519192988473579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47921313530871391877051509 4492623143519192988473579)
                ·
                  refine ⟨6738934715278789482710369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4492623143519192988473579 6738934715278789482710369)
                  ·
                    refine ⟨5054201036459092112032777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6738934715278789482710369 5054201036459092112032777)
                    ·
                      refine ⟨3790650777344319084024583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5054201036459092112032777 3790650777344319084024583)
                      ·
                        rfl

theorem cell23_7382266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2].length) (baseStart_7382266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382266 prefixEnd_7382266 := by exact prefixLift 7382266
  have htrace : WordTrace (prefixWord ++ tailWord_7382266) baseStart_7382266 baseEnd_7382266 := by
    simpa [prefixWord, tailWord_7382266, baseEnd_7382266] using wordTrace_append hprefix tailTrace_7382266
  have hstable : (prefixWord ++ tailWord_7382266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382266).length < 2 ^ (prefixWord ++ tailWord_7382266).sum := by decide
  have hdescent : baseEnd_7382266 < baseStart_7382266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382283 : List Nat := [1, 1, 1, 1, 5, 3, 4, 2, 1, 2, 2]
def baseStart_7382283 : Nat := 118140960795 + 7382283 * 2 ^ 59
def prefixEnd_7382283 : Nat := 4983230072969 + 3 ^ 40 * 7382283 * 2
def baseEnd_7382283 : Nat := 3790659506515445517512005

theorem tailTrace_7382283 : CollatzResearch.WordTrace tailWord_7382283 prefixEnd_7382283 3790659506515445517512005 := by
  unfold tailWord_7382283
  simp only [CollatzResearch.WordTrace]
  refine ⟨269253981114256959404607503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179502654076171306269738335 269253981114256959404607503)
  ·
    refine ⟨403880971671385439106911255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269253981114256959404607503 403880971671385439106911255)
    ·
      refine ⟨605821457507078158660366883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403880971671385439106911255 605821457507078158660366883)
      ·
        refine ⟨908732186260617237990550325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605821457507078158660366883 908732186260617237990550325)
        ·
          refine ⟨85193642461932866061614093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 908732186260617237990550325 85193642461932866061614093)
          ·
            refine ⟨31947615923224824773105285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85193642461932866061614093 31947615923224824773105285)
            ·
              refine ⟨5990177985604654644957241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31947615923224824773105285 5990177985604654644957241)
              ·
                refine ⟨4492633489203490983717931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5990177985604654644957241 4492633489203490983717931)
                ·
                  refine ⟨6738950233805236475576897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4492633489203490983717931 6738950233805236475576897)
                  ·
                    refine ⟨5054212675353927356682673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6738950233805236475576897 5054212675353927356682673)
                    ·
                      refine ⟨3790659506515445517512005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5054212675353927356682673 3790659506515445517512005)
                      ·
                        rfl

theorem cell23_7382283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 1, 2, 2].length) (baseStart_7382283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382283 prefixEnd_7382283 := by exact prefixLift 7382283
  have htrace : WordTrace (prefixWord ++ tailWord_7382283) baseStart_7382283 baseEnd_7382283 := by
    simpa [prefixWord, tailWord_7382283, baseEnd_7382283] using wordTrace_append hprefix tailTrace_7382283
  have hstable : (prefixWord ++ tailWord_7382283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382283).length < 2 ^ (prefixWord ++ tailWord_7382283).sum := by decide
  have hdescent : baseEnd_7382283 < baseStart_7382283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382305 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_7382305 : Nat := 118140960795 + 7382305 * 2 ^ 59
def prefixEnd_7382305 : Nat := 4983230072969 + 3 ^ 40 * 7382305 * 2
def baseEnd_7382305 : Nat := 3790670803089844431436903

theorem tailTrace_7382305 : CollatzResearch.WordTrace tailWord_7382305 prefixEnd_7382305 3790670803089844431436903 := by
  unfold tailWord_7382305
  simp only [CollatzResearch.WordTrace]
  refine ⟨269254783520177257161908369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179503189013451504774605579 269254783520177257161908369)
  ·
    refine ⟨201941087640132942871431277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269254783520177257161908369 201941087640132942871431277)
    ·
      refine ⟨75727907865049853576786729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201941087640132942871431277 75727907865049853576786729)
      ·
        refine ⟨56795930898787390182590047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75727907865049853576786729 56795930898787390182590047)
        ·
          refine ⟨85193896348181085273885071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56795930898787390182590047 85193896348181085273885071)
          ·
            refine ⟨127790844522271627910827607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85193896348181085273885071 127790844522271627910827607)
            ·
              refine ⟨191686266783407441866241411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127790844522271627910827607 191686266783407441866241411)
              ·
                refine ⟨287529400175111162799362117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191686266783407441866241411 287529400175111162799362117)
                ·
                  refine ⟨53911762532833343024880397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287529400175111162799362117 53911762532833343024880397)
                  ·
                    refine ⟨20216910949812503634330149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53911762532833343024880397 20216910949812503634330149)
                    ·
                      refine ⟨3790670803089844431436903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20216910949812503634330149 3790670803089844431436903)
                      ·
                        rfl

theorem cell23_7382305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_7382305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382305 prefixEnd_7382305 := by exact prefixLift 7382305
  have htrace : WordTrace (prefixWord ++ tailWord_7382305) baseStart_7382305 baseEnd_7382305 := by
    simpa [prefixWord, tailWord_7382305, baseEnd_7382305] using wordTrace_append hprefix tailTrace_7382305
  have hstable : (prefixWord ++ tailWord_7382305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382305).length < 2 ^ (prefixWord ++ tailWord_7382305).sum := by decide
  have hdescent : baseEnd_7382305 < baseStart_7382305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382309 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 3, 3, 2]
def baseStart_7382309 : Nat := 118140960795 + 7382309 * 2 ^ 59
def prefixEnd_7382309 : Nat := 4983230072969 + 3 ^ 40 * 7382309 * 2
def baseEnd_7382309 : Nat := 3790672857012462415786885

theorem tailTrace_7382309 : CollatzResearch.WordTrace tailWord_7382309 prefixEnd_7382309 3790672857012462415786885 := by
  unfold tailWord_7382309
  simp only [CollatzResearch.WordTrace]
  refine ⟨269254929412162765845053981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179503286274775177230035987 269254929412162765845053981)
  ·
    refine ⟨100970598529561037191895243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269254929412162765845053981 100970598529561037191895243)
    ·
      refine ⟨151455897794341555787842865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100970598529561037191895243 151455897794341555787842865)
      ·
        refine ⟨113591923345756166840882149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151455897794341555787842865 113591923345756166840882149)
        ·
          refine ⟨21298485627329281282665403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113591923345756166840882149 21298485627329281282665403)
          ·
            refine ⟨31947728440993921923998105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21298485627329281282665403 31947728440993921923998105)
            ·
              refine ⟨23960796330745441442998579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31947728440993921923998105 23960796330745441442998579)
              ·
                refine ⟨35941194496118162164497869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23960796330745441442998579 35941194496118162164497869)
                ·
                  refine ⟨13477947936044310811686701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35941194496118162164497869 13477947936044310811686701)
                  ·
                    refine ⟨5054230476016616554382513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13477947936044310811686701 5054230476016616554382513)
                    ·
                      refine ⟨3790672857012462415786885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5054230476016616554382513 3790672857012462415786885)
                      ·
                        rfl

theorem cell23_7382309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_7382309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382309 prefixEnd_7382309 := by exact prefixLift 7382309
  have htrace : WordTrace (prefixWord ++ tailWord_7382309) baseStart_7382309 baseEnd_7382309 := by
    simpa [prefixWord, tailWord_7382309, baseEnd_7382309] using wordTrace_append hprefix tailTrace_7382309
  have hstable : (prefixWord ++ tailWord_7382309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382309).length < 2 ^ (prefixWord ++ tailWord_7382309).sum := by decide
  have hdescent : baseEnd_7382309 < baseStart_7382309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382345 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 7]
def baseStart_7382345 : Nat := 118140960795 + 7382345 * 2 ^ 59
def prefixEnd_7382345 : Nat := 4983230072969 + 3 ^ 40 * 7382345 * 2
def baseEnd_7382345 : Nat := 421187926924002697215191

theorem tailTrace_7382345 : CollatzResearch.WordTrace tailWord_7382345 prefixEnd_7382345 421187926924002697215191 := by
  unfold tailWord_7382345
  simp only [CollatzResearch.WordTrace]
  refine ⟨269256242440032343993364489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179504161626688229328909659 269256242440032343993364489)
  ·
    refine ⟨201942181830024257995023367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269256242440032343993364489 201942181830024257995023367)
    ·
      refine ⟨302913272745036386992535051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201942181830024257995023367 302913272745036386992535051)
      ·
        refine ⟨454369909117554580488802577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302913272745036386992535051 454369909117554580488802577)
        ·
          refine ⟨340777431838165935366601933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454369909117554580488802577 340777431838165935366601933)
          ·
            refine ⟨127791536939312225762475725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340777431838165935366601933 127791536939312225762475725)
            ·
              refine ⟨47921826352242084660928397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127791536939312225762475725 47921826352242084660928397)
              ·
                refine ⟨17970684882090781747848149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47921826352242084660928397 17970684882090781747848149)
                ·
                  refine ⟨421187926924002697215191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17970684882090781747848149 421187926924002697215191)
                  ·
                    rfl

theorem cell23_7382345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 7].length) (baseStart_7382345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382345 prefixEnd_7382345 := by exact prefixLift 7382345
  have htrace : WordTrace (prefixWord ++ tailWord_7382345) baseStart_7382345 baseEnd_7382345 := by
    simpa [prefixWord, tailWord_7382345, baseEnd_7382345] using wordTrace_append hprefix tailTrace_7382345
  have hstable : (prefixWord ++ tailWord_7382345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382345).length < 2 ^ (prefixWord ++ tailWord_7382345).sum := by decide
  have hdescent : baseEnd_7382345 < baseStart_7382345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382412 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_7382412 : Nat := 118140960795 + 7382412 * 2 ^ 59
def prefixEnd_7382412 : Nat := 4983230072969 + 3 ^ 40 * 7382412 * 2
def baseEnd_7382412 : Nat := 3790725745519875512798911

theorem tailTrace_7382412 : CollatzResearch.WordTrace tailWord_7382412 prefixEnd_7382412 3790725745519875512798911 := by
  unfold tailWord_7382412
  simp only [CollatzResearch.WordTrace]
  refine ⟨134629343065394807218026745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179505790753859742957368993 134629343065394807218026745)
  ·
    refine ⟨100972007299046105413520059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134629343065394807218026745 100972007299046105413520059)
    ·
      refine ⟨151458010948569158120280089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100972007299046105413520059 151458010948569158120280089)
      ·
        refine ⟨113593508211426868590210067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151458010948569158120280089 113593508211426868590210067)
        ·
          refine ⟨170390262317140302885315101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113593508211426868590210067 170390262317140302885315101)
          ·
            refine ⟨63896348368927613581993163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170390262317140302885315101 63896348368927613581993163)
            ·
              refine ⟨95844522553391420372989745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63896348368927613581993163 95844522553391420372989745)
              ·
                refine ⟨71883391915043565279742309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95844522553391420372989745 71883391915043565279742309)
                ·
                  refine ⟨13478135984070668489951683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71883391915043565279742309 13478135984070668489951683)
                  ·
                    refine ⟨20217203976106002734927525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13478135984070668489951683 20217203976106002734927525)
                    ·
                      refine ⟨3790725745519875512798911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20217203976106002734927525 3790725745519875512798911)
                      ·
                        rfl

theorem cell23_7382412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_7382412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382412 prefixEnd_7382412 := by exact prefixLift 7382412
  have htrace : WordTrace (prefixWord ++ tailWord_7382412) baseStart_7382412 baseEnd_7382412 := by
    simpa [prefixWord, tailWord_7382412, baseEnd_7382412] using wordTrace_append hprefix tailTrace_7382412
  have hstable : (prefixWord ++ tailWord_7382412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382412).length < 2 ^ (prefixWord ++ tailWord_7382412).sum := by decide
  have hdescent : baseEnd_7382412 < baseStart_7382412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382429 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_7382429 : Nat := 118140960795 + 7382429 * 2 ^ 59
def prefixEnd_7382429 : Nat := 4983230072969 + 3 ^ 40 * 7382429 * 2
def baseEnd_7382429 : Nat := 3790734474691001946286333

theorem tailTrace_7382429 : CollatzResearch.WordTrace tailWord_7382429 prefixEnd_7382429 3790734474691001946286333 := by
  unfold tailWord_7382429
  simp only [CollatzResearch.WordTrace]
  refine ⟨269259306171728026339422341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179506204114485350892948227 269259306171728026339422341)
  ·
    refine ⟨50486119907199004938641689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269259306171728026339422341 50486119907199004938641689)
    ·
      refine ⟨37864589930399253703981267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50486119907199004938641689 37864589930399253703981267)
      ·
        refine ⟨56796884895598880555971901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37864589930399253703981267 56796884895598880555971901)
        ·
          refine ⟨21298831835849580208489463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56796884895598880555971901 21298831835849580208489463)
          ·
            refine ⟨31948247753774370312734195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21298831835849580208489463 31948247753774370312734195)
            ·
              refine ⟨47922371630661555469101293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31948247753774370312734195 47922371630661555469101293)
              ·
                refine ⟨17970889361498083300912985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47922371630661555469101293 17970889361498083300912985)
                ·
                  refine ⟨13478167021123562475684739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17970889361498083300912985 13478167021123562475684739)
                  ·
                    refine ⟨20217250531685343713527109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13478167021123562475684739 20217250531685343713527109)
                    ·
                      refine ⟨3790734474691001946286333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20217250531685343713527109 3790734474691001946286333)
                      ·
                        rfl

theorem cell23_7382429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_7382429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382429 prefixEnd_7382429 := by exact prefixLift 7382429
  have htrace : WordTrace (prefixWord ++ tailWord_7382429) baseStart_7382429 baseEnd_7382429 := by
    simpa [prefixWord, tailWord_7382429, baseEnd_7382429] using wordTrace_append hprefix tailTrace_7382429
  have hstable : (prefixWord ++ tailWord_7382429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382429).length < 2 ^ (prefixWord ++ tailWord_7382429).sum := by decide
  have hdescent : baseEnd_7382429 < baseStart_7382429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382449 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 2, 2, 3]
def baseStart_7382449 : Nat := 118140960795 + 7382449 * 2 ^ 59
def prefixEnd_7382449 : Nat := 4983230072969 + 3 ^ 40 * 7382449 * 2
def baseEnd_7382449 : Nat := 3790744744304091868036241

theorem tailTrace_7382449 : CollatzResearch.WordTrace tailWord_7382449 prefixEnd_7382449 3790744744304091868036241 := by
  unfold tailWord_7382449
  simp only [CollatzResearch.WordTrace]
  refine ⟨269260035631655569755150401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179506690421103713170100267 269260035631655569755150401)
  ·
    refine ⟨201945026723741677316362801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269260035631655569755150401 201945026723741677316362801)
    ·
      refine ⟨151458770042806257987272101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201945026723741677316362801 151458770042806257987272101)
      ·
        refine ⟨28398519383026173372613519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151458770042806257987272101 28398519383026173372613519)
        ·
          refine ⟨42597779074539260058920279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28398519383026173372613519 42597779074539260058920279)
          ·
            refine ⟨63896668611808890088380419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42597779074539260058920279 63896668611808890088380419)
            ·
              refine ⟨95845002917713335132570629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63896668611808890088380419 95845002917713335132570629)
              ·
                refine ⟨17970938047071250337356993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95845002917713335132570629 17970938047071250337356993)
                ·
                  refine ⟨13478203535303437753017745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17970938047071250337356993 13478203535303437753017745)
                  ·
                    refine ⟨10108652651477578314763309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13478203535303437753017745 10108652651477578314763309)
                    ·
                      refine ⟨3790744744304091868036241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10108652651477578314763309 3790744744304091868036241)
                      ·
                        rfl

theorem cell23_7382449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_7382449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382449 prefixEnd_7382449 := by exact prefixLift 7382449
  have htrace : WordTrace (prefixWord ++ tailWord_7382449) baseStart_7382449 baseEnd_7382449 := by
    simpa [prefixWord, tailWord_7382449, baseEnd_7382449] using wordTrace_append hprefix tailTrace_7382449
  have hstable : (prefixWord ++ tailWord_7382449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382449).length < 2 ^ (prefixWord ++ tailWord_7382449).sum := by decide
  have hdescent : baseEnd_7382449 < baseStart_7382449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382479 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 5, 1, 3]
def baseStart_7382479 : Nat := 118140960795 + 7382479 * 2 ^ 59
def prefixEnd_7382479 : Nat := 4983230072969 + 3 ^ 40 * 7382479 * 2
def baseEnd_7382479 : Nat := 3790760148723726750661103

theorem tailTrace_7382479 : CollatzResearch.WordTrace tailWord_7382479 prefixEnd_7382479 3790760148723726750661103 := by
  unfold tailWord_7382479
  simp only [CollatzResearch.WordTrace]
  refine ⟨269261129821546884878742491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179507419881031256585828327 269261129821546884878742491)
  ·
    refine ⟨403891694732320327318113737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269261129821546884878742491 403891694732320327318113737)
    ·
      refine ⟨302918771049240245488585303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403891694732320327318113737 302918771049240245488585303)
      ·
        refine ⟨454378156573860368232877955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302918771049240245488585303 454378156573860368232877955)
        ·
          refine ⟨681567234860790552349316933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454378156573860368232877955 681567234860790552349316933)
          ·
            refine ⟨127793856536398228565496925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 681567234860790552349316933 127793856536398228565496925)
            ·
              refine ⟨47922696201149335712061347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127793856536398228565496925 47922696201149335712061347)
              ·
                refine ⟨71884044301724003568092021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47922696201149335712061347 71884044301724003568092021)
                ·
                  refine ⟨6739129153286625334508627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71884044301724003568092021 6739129153286625334508627)
                  ·
                    refine ⟨10108693729929938001762941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6739129153286625334508627 10108693729929938001762941)
                    ·
                      refine ⟨3790760148723726750661103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10108693729929938001762941 3790760148723726750661103)
                      ·
                        rfl

theorem cell23_7382479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 1, 3].length) (baseStart_7382479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382479 prefixEnd_7382479 := by exact prefixLift 7382479
  have htrace : WordTrace (prefixWord ++ tailWord_7382479) baseStart_7382479 baseEnd_7382479 := by
    simpa [prefixWord, tailWord_7382479, baseEnd_7382479] using wordTrace_append hprefix tailTrace_7382479
  have hstable : (prefixWord ++ tailWord_7382479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382479).length < 2 ^ (prefixWord ++ tailWord_7382479).sum := by decide
  have hdescent : baseEnd_7382479 < baseStart_7382479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382513 : List Nat := [1, 2, 2, 2, 3, 2, 2, 4, 1, 1, 3]
def baseStart_7382513 : Nat := 118140960795 + 7382513 * 2 ^ 59
def prefixEnd_7382513 : Nat := 4983230072969 + 3 ^ 40 * 7382513 * 2
def baseEnd_7382513 : Nat := 3790777607065979617635947

theorem tailTrace_7382513 : CollatzResearch.WordTrace tailWord_7382513 prefixEnd_7382513 3790777607065979617635947 := by
  unfold tailWord_7382513
  simp only [CollatzResearch.WordTrace]
  refine ⟨269262369903423708685480193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179508246602282472456986795 269262369903423708685480193)
  ·
    refine ⟨201946777427567781514110145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269262369903423708685480193 201946777427567781514110145)
    ·
      refine ⟨151460083070675836135582609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201946777427567781514110145 151460083070675836135582609)
      ·
        refine ⟨113595062303006877101686957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151460083070675836135582609 113595062303006877101686957)
        ·
          refine ⟨42598148363627578913132609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113595062303006877101686957 42598148363627578913132609)
          ·
            refine ⟨31948611272720684184849457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42598148363627578913132609 31948611272720684184849457)
            ·
              refine ⟨23961458454540513138637093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31948611272720684184849457 23961458454540513138637093)
              ·
                refine ⟨4492773460226346213494455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23961458454540513138637093 4492773460226346213494455)
                ·
                  refine ⟨6739160190339519320241683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4492773460226346213494455 6739160190339519320241683)
                  ·
                    refine ⟨10108740285509278980362525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6739160190339519320241683 10108740285509278980362525)
                    ·
                      refine ⟨3790777607065979617635947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10108740285509278980362525 3790777607065979617635947)
                      ·
                        rfl

theorem cell23_7382513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_7382513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382513 prefixEnd_7382513 := by exact prefixLift 7382513
  have htrace : WordTrace (prefixWord ++ tailWord_7382513) baseStart_7382513 baseEnd_7382513 := by
    simpa [prefixWord, tailWord_7382513, baseEnd_7382513] using wordTrace_append hprefix tailTrace_7382513
  have hstable : (prefixWord ++ tailWord_7382513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382513).length < 2 ^ (prefixWord ++ tailWord_7382513).sum := by decide
  have hdescent : baseEnd_7382513 < baseStart_7382513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382556 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_7382556 : Nat := 118140960795 + 7382556 * 2 ^ 59
def prefixEnd_7382556 : Nat := 4983230072969 + 3 ^ 40 * 7382556 * 2
def baseEnd_7382556 : Nat := 3790799686734122949398249

theorem tailTrace_7382556 : CollatzResearch.WordTrace tailWord_7382556 prefixEnd_7382556 3790799686734122949398249 := by
  unfold tailWord_7382556
  simp only [CollatzResearch.WordTrace]
  refine ⟨134631969121133963514647761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179509292161511951352863681 134631969121133963514647761)
  ·
    refine ⟨100973976840850472635985821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134631969121133963514647761 100973976840850472635985821)
    ·
      refine ⟨37865241315318927238494683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100973976840850472635985821 37865241315318927238494683)
      ·
        refine ⟨56797861972978390857742025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37865241315318927238494683 56797861972978390857742025)
        ·
          refine ⟨42598396479733793143306519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56797861972978390857742025 42598396479733793143306519)
          ·
            refine ⟨63897594719600689714959779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42598396479733793143306519 63897594719600689714959779)
            ·
              refine ⟨95846392079401034572439669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63897594719600689714959779 95846392079401034572439669)
              ·
                refine ⟨8985599257443846991166219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95846392079401034572439669 8985599257443846991166219)
                ·
                  refine ⟨13478398886165770486749329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8985599257443846991166219 13478398886165770486749329)
                  ·
                    refine ⟨10108799164624327865061997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13478398886165770486749329 10108799164624327865061997)
                    ·
                      refine ⟨3790799686734122949398249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10108799164624327865061997 3790799686734122949398249)
                      ·
                        rfl

theorem cell23_7382556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_7382556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382556 prefixEnd_7382556 := by exact prefixLift 7382556
  have htrace : WordTrace (prefixWord ++ tailWord_7382556) baseStart_7382556 baseEnd_7382556 := by
    simpa [prefixWord, tailWord_7382556, baseEnd_7382556] using wordTrace_append hprefix tailTrace_7382556
  have hstable : (prefixWord ++ tailWord_7382556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382556).length < 2 ^ (prefixWord ++ tailWord_7382556).sum := by decide
  have hdescent : baseEnd_7382556 < baseStart_7382556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382592 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_7382592 : Nat := 118140960795 + 7382592 * 2 ^ 59
def prefixEnd_7382592 : Nat := 4983230072969 + 3 ^ 40 * 7382592 * 2
def baseEnd_7382592 : Nat := 3790818172037684808548083

theorem tailTrace_7382592 : CollatzResearch.WordTrace tailWord_7382592 prefixEnd_7382592 3790818172037684808548083 := by
  unfold tailWord_7382592
  simp only [CollatzResearch.WordTrace]
  refine ⟨134632625635068752588803015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179510167513425003451737353 134632625635068752588803015)
  ·
    refine ⟨201948938452603128883204523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134632625635068752588803015 201948938452603128883204523)
    ·
      refine ⟨302923407678904693324806785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201948938452603128883204523 302923407678904693324806785)
      ·
        refine ⟨227192555759178519993605089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302923407678904693324806785 227192555759178519993605089)
        ·
          refine ⟨170394416819383889995203817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227192555759178519993605089 170394416819383889995203817)
          ·
            refine ⟨127795812614537917496402863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170394416819383889995203817 127795812614537917496402863)
            ·
              refine ⟨191693718921806876244604295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127795812614537917496402863 191693718921806876244604295)
              ·
                refine ⟨287540578382710314366906443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191693718921806876244604295 287540578382710314366906443)
                ·
                  refine ⟨431310867574065471550359665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287540578382710314366906443 431310867574065471550359665)
                  ·
                    refine ⟨323483150680549103662769749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 431310867574065471550359665 323483150680549103662769749)
                    ·
                      refine ⟨3790818172037684808548083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 323483150680549103662769749 3790818172037684808548083)
                      ·
                        rfl

theorem cell23_7382592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_7382592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382592 prefixEnd_7382592 := by exact prefixLift 7382592
  have htrace : WordTrace (prefixWord ++ tailWord_7382592) baseStart_7382592 baseEnd_7382592 := by
    simpa [prefixWord, tailWord_7382592, baseEnd_7382592] using wordTrace_append hprefix tailTrace_7382592
  have hstable : (prefixWord ++ tailWord_7382592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382592).length < 2 ^ (prefixWord ++ tailWord_7382592).sum := by decide
  have hdescent : baseEnd_7382592 < baseStart_7382592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382620 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_7382620 : Nat := 118140960795 + 7382620 * 2 ^ 59
def prefixEnd_7382620 : Nat := 4983230072969 + 3 ^ 40 * 7382620 * 2
def baseEnd_7382620 : Nat := 3790832549496010698997955

theorem tailTrace_7382620 : CollatzResearch.WordTrace tailWord_7382620 prefixEnd_7382620 3790832549496010698997955 := by
  unfold tailWord_7382620
  simp only [CollatzResearch.WordTrace]
  refine ⟨134633136257018032979812657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179510848342690710639750209 134633136257018032979812657)
  ·
    refine ⟨100974852192763524734859493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134633136257018032979812657 100974852192763524734859493)
    ·
      refine ⟨18932784786143160887786155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100974852192763524734859493 18932784786143160887786155)
      ·
        refine ⟨28399177179214741331679233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18932784786143160887786155 28399177179214741331679233)
        ·
          refine ⟨21299382884411055998759425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28399177179214741331679233 21299382884411055998759425)
          ·
            refine ⟨15974537163308291999069569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21299382884411055998759425 15974537163308291999069569)
            ·
              refine ⟨11980902872481218999302177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15974537163308291999069569 11980902872481218999302177)
              ·
                refine ⟨8985677154360914249476633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11980902872481218999302177 8985677154360914249476633)
                ·
                  refine ⟨6739257865770685687107475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8985677154360914249476633 6739257865770685687107475)
                  ·
                    refine ⟨10108886798656028530661213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6739257865770685687107475 10108886798656028530661213)
                    ·
                      refine ⟨3790832549496010698997955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10108886798656028530661213 3790832549496010698997955)
                      ·
                        rfl

theorem cell23_7382620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_7382620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382620 prefixEnd_7382620 := by exact prefixLift 7382620
  have htrace : WordTrace (prefixWord ++ tailWord_7382620) baseStart_7382620 baseEnd_7382620 := by
    simpa [prefixWord, tailWord_7382620, baseEnd_7382620] using wordTrace_append hprefix tailTrace_7382620
  have hstable : (prefixWord ++ tailWord_7382620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382620).length < 2 ^ (prefixWord ++ tailWord_7382620).sum := by decide
  have hdescent : baseEnd_7382620 < baseStart_7382620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382649 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 7]
def baseStart_7382649 : Nat := 118140960795 + 7382649 * 2 ^ 59
def prefixEnd_7382649 : Nat := 4983230072969 + 3 ^ 40 * 7382649 * 2
def baseEnd_7382649 : Nat := 421205271159443453948369

theorem tailTrace_7382649 : CollatzResearch.WordTrace tailWord_7382649 prefixEnd_7382649 421205271159443453948369 := by
  unfold tailWord_7382649
  simp only [CollatzResearch.WordTrace]
  refine ⟨269267330230931003912431001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179511553487287335941620667 269267330230931003912431001)
  ·
    refine ⟨201950497673198252934323251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269267330230931003912431001 201950497673198252934323251)
    ·
      refine ⟨302925746509797379401484877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201950497673198252934323251 302925746509797379401484877)
      ·
        refine ⟨113597154941174017275556829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302925746509797379401484877 113597154941174017275556829)
        ·
          refine ⟨42598933102940256478333811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113597154941174017275556829 42598933102940256478333811)
          ·
            refine ⟨63898399654410384717500717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42598933102940256478333811 63898399654410384717500717)
            ·
              refine ⟨23961899870403894269062769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63898399654410384717500717 23961899870403894269062769)
              ·
                refine ⟨17971424902802920701797077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23961899870403894269062769 17971424902802920701797077)
                ·
                  refine ⟨421205271159443453948369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17971424902802920701797077 421205271159443453948369)
                  ·
                    rfl

theorem cell23_7382649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 7].length) (baseStart_7382649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382649 prefixEnd_7382649 := by exact prefixLift 7382649
  have htrace : WordTrace (prefixWord ++ tailWord_7382649) baseStart_7382649 baseEnd_7382649 := by
    simpa [prefixWord, tailWord_7382649, baseEnd_7382649] using wordTrace_append hprefix tailTrace_7382649
  have hstable : (prefixWord ++ tailWord_7382649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382649).length < 2 ^ (prefixWord ++ tailWord_7382649).sum := by decide
  have hdescent : baseEnd_7382649 < baseStart_7382649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382659 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 3]
def baseStart_7382659 : Nat := 118140960795 + 7382659 * 2 ^ 59
def prefixEnd_7382659 : Nat := 4983230072969 + 3 ^ 40 * 7382659 * 2
def baseEnd_7382659 : Nat := 3790852575241536046410275

theorem tailTrace_7382659 : CollatzResearch.WordTrace tailWord_7382659 prefixEnd_7382659 3790852575241536046410275 := by
  unfold tailWord_7382659
  simp only [CollatzResearch.WordTrace]
  refine ⟨269267694960894775620295031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179511796640596517080196687 269267694960894775620295031)
  ·
    refine ⟨403901542441342163430442547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269267694960894775620295031 403901542441342163430442547)
    ·
      refine ⟨605852313662013245145663821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403901542441342163430442547 605852313662013245145663821)
      ·
        refine ⟨227194617623254966929623933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605852313662013245145663821 227194617623254966929623933)
        ·
          refine ⟨85197981608720612598608975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227194617623254966929623933 85197981608720612598608975)
          ·
            refine ⟨127796972413080918897913463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85197981608720612598608975 127796972413080918897913463)
            ·
              refine ⟨191695458619621378346870195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127796972413080918897913463 191695458619621378346870195)
              ·
                refine ⟨287543187929432067520305293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191695458619621378346870195 287543187929432067520305293)
                ·
                  refine ⟨107828695473537025320114485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287543187929432067520305293 107828695473537025320114485)
                  ·
                    refine ⟨10108940200644096123760733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107828695473537025320114485 10108940200644096123760733)
                    ·
                      refine ⟨3790852575241536046410275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10108940200644096123760733 3790852575241536046410275)
                      ·
                        rfl

theorem cell23_7382659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_7382659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382659 prefixEnd_7382659 := by exact prefixLift 7382659
  have htrace : WordTrace (prefixWord ++ tailWord_7382659) baseStart_7382659 baseEnd_7382659 := by
    simpa [prefixWord, tailWord_7382659, baseEnd_7382659] using wordTrace_append hprefix tailTrace_7382659
  have hstable : (prefixWord ++ tailWord_7382659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382659).length < 2 ^ (prefixWord ++ tailWord_7382659).sum := by decide
  have hdescent : baseEnd_7382659 < baseStart_7382659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382664 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7382664 : Nat := 118140960795 + 7382664 * 2 ^ 59
def prefixEnd_7382664 : Nat := 4983230072969 + 3 ^ 40 * 7382664 * 2
def baseEnd_7382664 : Nat := 3790855142644808526847753

theorem tailTrace_7382664 : CollatzResearch.WordTrace tailWord_7382664 prefixEnd_7382664 3790855142644808526847753 := by
  unfold tailWord_7382664
  simp only [CollatzResearch.WordTrace]
  refine ⟨134633938662938330737113523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179511918217251107649484697 134633938662938330737113523)
  ·
    refine ⟨201950907994407496105670285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134633938662938330737113523 201950907994407496105670285)
    ·
      refine ⟨75731590497902811039626357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201950907994407496105670285 75731590497902811039626357)
      ·
        refine ⟨7099836609178388534964971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75731590497902811039626357 7099836609178388534964971)
        ·
          refine ⟨10649754913767582802447457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099836609178388534964971 10649754913767582802447457)
          ·
            refine ⟨7987316185325687101835593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10649754913767582802447457 7987316185325687101835593)
            ·
              refine ⟨5990487138994265326376695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7987316185325687101835593 5990487138994265326376695)
              ·
                refine ⟨8985730708491397989565043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990487138994265326376695 8985730708491397989565043)
                ·
                  refine ⟨13478596062737096984347565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8985730708491397989565043 13478596062737096984347565)
                  ·
                    refine ⟨5054473523526411369130337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13478596062737096984347565 5054473523526411369130337)
                    ·
                      refine ⟨3790855142644808526847753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5054473523526411369130337 3790855142644808526847753)
                      ·
                        rfl

theorem cell23_7382664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7382664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382664 prefixEnd_7382664 := by exact prefixLift 7382664
  have htrace : WordTrace (prefixWord ++ tailWord_7382664) baseStart_7382664 baseEnd_7382664 := by
    simpa [prefixWord, tailWord_7382664, baseEnd_7382664] using wordTrace_append hprefix tailTrace_7382664
  have hstable : (prefixWord ++ tailWord_7382664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382664).length < 2 ^ (prefixWord ++ tailWord_7382664).sum := by decide
  have hdescent : baseEnd_7382664 < baseStart_7382664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382716 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_7382716 : Nat := 118140960795 + 7382716 * 2 ^ 59
def prefixEnd_7382716 : Nat := 4983230072969 + 3 ^ 40 * 7382716 * 2
def baseEnd_7382716 : Nat := 3790881843638842323397513

theorem tailTrace_7382716 : CollatzResearch.WordTrace tailWord_7382716 prefixEnd_7382716 3790881843638842323397513 := by
  unfold tailWord_7382716
  simp only [CollatzResearch.WordTrace]
  refine ⟨134634886960844137177560001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179513182614458849570080001 134634886960844137177560001)
  ·
    refine ⟨100976165220633102883170001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134634886960844137177560001 100976165220633102883170001)
    ·
      refine ⟨75732123915474827162377501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100976165220633102883170001 75732123915474827162377501)
      ·
        refine ⟨28399546468303060185891563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75732123915474827162377501 28399546468303060185891563)
        ·
          refine ⟨42599319702454590278837345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28399546468303060185891563 42599319702454590278837345)
          ·
            refine ⟨31949489776840942709128009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42599319702454590278837345 31949489776840942709128009)
            ·
              refine ⟨23962117332630707031846007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31949489776840942709128009 23962117332630707031846007)
              ·
                refine ⟨35943175998946060547769011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23962117332630707031846007 35943175998946060547769011)
                ·
                  refine ⟨53914763998419090821653517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35943175998946060547769011 53914763998419090821653517)
                  ·
                    refine ⟨20218036499407159058120069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53914763998419090821653517 20218036499407159058120069)
                    ·
                      refine ⟨3790881843638842323397513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20218036499407159058120069 3790881843638842323397513)
                      ·
                        rfl

theorem cell23_7382716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_7382716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382716 prefixEnd_7382716 := by exact prefixLift 7382716
  have htrace : WordTrace (prefixWord ++ tailWord_7382716) baseStart_7382716 baseEnd_7382716 := by
    simpa [prefixWord, tailWord_7382716, baseEnd_7382716] using wordTrace_append hprefix tailTrace_7382716
  have hstable : (prefixWord ++ tailWord_7382716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382716).length < 2 ^ (prefixWord ++ tailWord_7382716).sum := by decide
  have hdescent : baseEnd_7382716 < baseStart_7382716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382756 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 6]
def baseStart_7382756 : Nat := 118140960795 + 7382756 * 2 ^ 59
def prefixEnd_7382756 : Nat := 4983230072969 + 3 ^ 40 * 7382756 * 2
def baseEnd_7382756 : Nat := 421211375873891351877481

theorem tailTrace_7382756 : CollatzResearch.WordTrace tailWord_7382756 prefixEnd_7382756 421211375873891351877481 := by
  unfold tailWord_7382756
  simp only [CollatzResearch.WordTrace]
  refine ⟨134635616420771680593288061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179514155227695574124384081 134635616420771680593288061)
  ·
    refine ⟨50488356157789380222483023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134635616420771680593288061 50488356157789380222483023)
    ·
      refine ⟨75732534236684070333724535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50488356157789380222483023 75732534236684070333724535)
      ·
        refine ⟨113598801355026105500586803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75732534236684070333724535 113598801355026105500586803)
        ·
          refine ⟨170398202032539158250880205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113598801355026105500586803 170398202032539158250880205)
          ·
            refine ⟨63899325762202184344080077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170398202032539158250880205 63899325762202184344080077)
            ·
              refine ⟨23962247160825819129030029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63899325762202184344080077 23962247160825819129030029)
              ·
                refine ⟨8985842685309682173386261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23962247160825819129030029 8985842685309682173386261)
                ·
                  refine ⟨421211375873891351877481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8985842685309682173386261 421211375873891351877481)
                  ·
                    rfl

theorem cell23_7382756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_7382756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382756 prefixEnd_7382756 := by exact prefixLift 7382756
  have htrace : WordTrace (prefixWord ++ tailWord_7382756) baseStart_7382756 baseEnd_7382756 := by
    simpa [prefixWord, tailWord_7382756, baseEnd_7382756] using wordTrace_append hprefix tailTrace_7382756
  have hstable : (prefixWord ++ tailWord_7382756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382756).length < 2 ^ (prefixWord ++ tailWord_7382756).sum := by decide
  have hdescent : baseEnd_7382756 < baseStart_7382756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382779 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5]
def baseStart_7382779 : Nat := 118140960795 + 7382779 * 2 ^ 59
def prefixEnd_7382779 : Nat := 4983230072969 + 3 ^ 40 * 7382779 * 2
def baseEnd_7382779 : Nat := 3790914192920075576909723

theorem tailTrace_7382779 : CollatzResearch.WordTrace tailWord_7382779 prefixEnd_7382779 3790914192920075576909723 := by
  unfold tailWord_7382779
  simp only [CollatzResearch.WordTrace]
  refine ⟨269272071720460036114663391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179514714480306690743108927 269272071720460036114663391)
  ·
    refine ⟨403908107580690054171995087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269272071720460036114663391 403908107580690054171995087)
    ·
      refine ⟨605862161371035081257992631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403908107580690054171995087 605862161371035081257992631)
      ·
        refine ⟨908793242056552621886988947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605862161371035081257992631 908793242056552621886988947)
        ·
          refine ⟨1363189863084828932830483421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908793242056552621886988947 1363189863084828932830483421)
          ·
            refine ⟨511196198656810849811431283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1363189863084828932830483421 511196198656810849811431283)
            ·
              refine ⟨766794297985216274717146925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511196198656810849811431283 766794297985216274717146925)
              ·
                refine ⟨287547861744456103018930097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 766794297985216274717146925 287547861744456103018930097)
                ·
                  refine ⟨215660896308342077264197573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287547861744456103018930097 215660896308342077264197573)
                  ·
                    refine ⟨40436418057814139487037045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215660896308342077264197573 40436418057814139487037045)
                    ·
                      refine ⟨3790914192920075576909723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40436418057814139487037045 3790914192920075576909723)
                      ·
                        rfl

theorem cell23_7382779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_7382779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382779 prefixEnd_7382779 := by exact prefixLift 7382779
  have htrace : WordTrace (prefixWord ++ tailWord_7382779) baseStart_7382779 baseEnd_7382779 := by
    simpa [prefixWord, tailWord_7382779, baseEnd_7382779] using wordTrace_append hprefix tailTrace_7382779
  have hstable : (prefixWord ++ tailWord_7382779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382779).length < 2 ^ (prefixWord ++ tailWord_7382779).sum := by decide
  have hdescent : baseEnd_7382779 < baseStart_7382779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382837 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 1, 5]
def baseStart_7382837 : Nat := 118140960795 + 7382837 * 2 ^ 59
def prefixEnd_7382837 : Nat := 4983230072969 + 3 ^ 40 * 7382837 * 2
def baseEnd_7382837 : Nat := 1263647991599345449994819

theorem tailTrace_7382837 : CollatzResearch.WordTrace tailWord_7382837 prefixEnd_7382837 1263647991599345449994819 := by
  unfold tailWord_7382837
  simp only [CollatzResearch.WordTrace]
  refine ⟨269274187154249912020274765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179516124769499941346849843 269274187154249912020274765)
  ·
    refine ⟨100977820182843717007603037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269274187154249912020274765 100977820182843717007603037)
    ·
      refine ⟨37866682568566393877851139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100977820182843717007603037 37866682568566393877851139)
      ·
        refine ⟨56800023852849590816776709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37866682568566393877851139 56800023852849590816776709)
        ·
          refine ⟨10650004472409298278145633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56800023852849590816776709 10650004472409298278145633)
          ·
            refine ⟨7987503354306973708609225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10650004472409298278145633 7987503354306973708609225)
            ·
              refine ⟨5990627515730230281456919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7987503354306973708609225 5990627515730230281456919)
              ·
                refine ⟨8985941273595345422185379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990627515730230281456919 8985941273595345422185379)
                ·
                  refine ⟨13478911910393018133278069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8985941273595345422185379 13478911910393018133278069)
                  ·
                    refine ⟨1263647991599345449994819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13478911910393018133278069 1263647991599345449994819)
                    ·
                      rfl

theorem cell23_7382837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_7382837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382837 prefixEnd_7382837 := by exact prefixLift 7382837
  have htrace : WordTrace (prefixWord ++ tailWord_7382837) baseStart_7382837 baseEnd_7382837 := by
    simpa [prefixWord, tailWord_7382837, baseEnd_7382837] using wordTrace_append hprefix tailTrace_7382837
  have hstable : (prefixWord ++ tailWord_7382837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382837).length < 2 ^ (prefixWord ++ tailWord_7382837).sum := by decide
  have hdescent : baseEnd_7382837 < baseStart_7382837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382840 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 1, 1, 4]
def baseStart_7382840 : Nat := 118140960795 + 7382840 * 2 ^ 59
def prefixEnd_7382840 : Nat := 4983230072969 + 3 ^ 40 * 7382840 * 2
def baseEnd_7382840 : Nat := 3790945515239999838246943

theorem tailTrace_7382840 : CollatzResearch.WordTrace tailWord_7382840 prefixEnd_7382840 3790945515239999838246943 := by
  unfold tailWord_7382840
  simp only [CollatzResearch.WordTrace]
  refine ⟨134637148286619521766316987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179516197715492695688422649 134637148286619521766316987)
  ·
    refine ⟨201955722429929282649475481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134637148286619521766316987 201955722429929282649475481)
    ·
      refine ⟨151466791822446961987106611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201955722429929282649475481 151466791822446961987106611)
      ·
        refine ⟨227200187733670442980659917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151466791822446961987106611 227200187733670442980659917)
        ·
          refine ⟨85200070400126416117747469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227200187733670442980659917 85200070400126416117747469)
          ·
            refine ⟨31950026400047406044155301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85200070400126416117747469 31950026400047406044155301)
            ·
              refine ⟨5990629950008888633279119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31950026400047406044155301 5990629950008888633279119)
              ·
                refine ⟨8985944925013332949918679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990629950008888633279119 8985944925013332949918679)
                ·
                  refine ⟨13478917387519999424878019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8985944925013332949918679 13478917387519999424878019)
                  ·
                    refine ⟨20218376081279999137317029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13478917387519999424878019 20218376081279999137317029)
                    ·
                      refine ⟨3790945515239999838246943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20218376081279999137317029 3790945515239999838246943)
                      ·
                        rfl

theorem cell23_7382840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_7382840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382840 prefixEnd_7382840 := by exact prefixLift 7382840
  have htrace : WordTrace (prefixWord ++ tailWord_7382840) baseStart_7382840 baseEnd_7382840 := by
    simpa [prefixWord, tailWord_7382840, baseEnd_7382840] using wordTrace_append hprefix tailTrace_7382840
  have hstable : (prefixWord ++ tailWord_7382840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382840).length < 2 ^ (prefixWord ++ tailWord_7382840).sum := by decide
  have hdescent : baseEnd_7382840 < baseStart_7382840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382857 : List Nat := [1, 2, 1, 1, 2, 4, 1, 6, 1, 2, 2]
def baseStart_7382857 : Nat := 118140960795 + 7382857 * 2 ^ 59
def prefixEnd_7382857 : Nat := 4983230072969 + 3 ^ 40 * 7382857 * 2
def baseEnd_7382857 : Nat := 3790954244411126271734365

theorem tailTrace_7382857 : CollatzResearch.WordTrace tailWord_7382857 prefixEnd_7382857 3790954244411126271734365 := by
  unfold tailWord_7382857
  simp only [CollatzResearch.WordTrace]
  refine ⟨269274916614177455436002825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179516611076118303624001883 269274916614177455436002825)
  ·
    refine ⟨201956187460633091577002119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269274916614177455436002825 201956187460633091577002119)
    ·
      refine ⟨302934281190949637365503179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201956187460633091577002119 302934281190949637365503179)
      ·
        refine ⟨454401421786424456048254769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302934281190949637365503179 454401421786424456048254769)
        ·
          refine ⟨340801066339818342036191077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454401421786424456048254769 340801066339818342036191077)
          ·
            refine ⟨63900199938715939131785827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340801066339818342036191077 63900199938715939131785827)
            ·
              refine ⟨95850299908073908697678741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63900199938715939131785827 95850299908073908697678741)
              ·
                refine ⟨4492982808190964470203691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95850299908073908697678741 4492982808190964470203691)
                ·
                  refine ⟨6739474212286446705305537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4492982808190964470203691 6739474212286446705305537)
                  ·
                    refine ⟨5054605659214835028979153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6739474212286446705305537 5054605659214835028979153)
                    ·
                      refine ⟨3790954244411126271734365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5054605659214835028979153 3790954244411126271734365)
                      ·
                        rfl

theorem cell23_7382857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 1, 2, 2].length) (baseStart_7382857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382857 prefixEnd_7382857 := by exact prefixLift 7382857
  have htrace : WordTrace (prefixWord ++ tailWord_7382857) baseStart_7382857 baseEnd_7382857 := by
    simpa [prefixWord, tailWord_7382857, baseEnd_7382857] using wordTrace_append hprefix tailTrace_7382857
  have hstable : (prefixWord ++ tailWord_7382857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382857).length < 2 ^ (prefixWord ++ tailWord_7382857).sum := by decide
  have hdescent : baseEnd_7382857 < baseStart_7382857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382896 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_7382896 : Nat := 118140960795 + 7382896 * 2 ^ 59
def prefixEnd_7382896 : Nat := 4983230072969 + 3 ^ 40 * 7382896 * 2
def baseEnd_7382896 : Nat := 3790974270156651619146685

theorem tailTrace_7382896 : CollatzResearch.WordTrace tailWord_7382896 prefixEnd_7382896 3790974270156651619146685 := by
  unfold tailWord_7382896
  simp only [CollatzResearch.WordTrace]
  refine ⟨134638169530518082548336271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179517559374024110064448361 134638169530518082548336271)
  ·
    refine ⟨201957254295777123822504407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134638169530518082548336271 201957254295777123822504407)
    ·
      refine ⟨302935881443665685733756611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201957254295777123822504407 302935881443665685733756611)
      ·
        refine ⟨454403822165498528600634917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302935881443665685733756611 454403822165498528600634917)
        ·
          refine ⟨85200716656030974112619047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454403822165498528600634917 85200716656030974112619047)
          ·
            refine ⟨127801074984046461168928571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85200716656030974112619047 127801074984046461168928571)
            ·
              refine ⟨191701612476069691753392857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127801074984046461168928571 191701612476069691753392857)
              ·
                refine ⟨143776209357052268815044643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191701612476069691753392857 143776209357052268815044643)
                ·
                  refine ⟨215664314035578403222566965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143776209357052268815044643 215664314035578403222566965)
                  ·
                    refine ⟨20218529440835475302115653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 215664314035578403222566965 20218529440835475302115653)
                    ·
                      refine ⟨3790974270156651619146685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20218529440835475302115653 3790974270156651619146685)
                      ·
                        rfl

theorem cell23_7382896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_7382896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382896 prefixEnd_7382896 := by exact prefixLift 7382896
  have htrace : WordTrace (prefixWord ++ tailWord_7382896) baseStart_7382896 baseEnd_7382896 := by
    simpa [prefixWord, tailWord_7382896, baseEnd_7382896] using wordTrace_append hprefix tailTrace_7382896
  have hstable : (prefixWord ++ tailWord_7382896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382896).length < 2 ^ (prefixWord ++ tailWord_7382896).sum := by decide
  have hdescent : baseEnd_7382896 < baseStart_7382896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382906 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_7382906 : Nat := 118140960795 + 7382906 * 2 ^ 59
def prefixEnd_7382906 : Nat := 4983230072969 + 3 ^ 40 * 7382906 * 2
def baseEnd_7382906 : Nat := 1263659801654398860007213

theorem tailTrace_7382906 : CollatzResearch.WordTrace tailWord_7382906 prefixEnd_7382906 1263659801654398860007213 := by
  unfold tailWord_7382906
  simp only [CollatzResearch.WordTrace]
  refine ⟨67319175947749984201134143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179517802527333291203024381 67319175947749984201134143)
  ·
    refine ⟨100978763921624976301701215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67319175947749984201134143 100978763921624976301701215)
    ·
      refine ⟨151468145882437464452551823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100978763921624976301701215 151468145882437464452551823)
      ·
        refine ⟨227202218823656196678827735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151468145882437464452551823 227202218823656196678827735)
        ·
          refine ⟨340803328235484295018241603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227202218823656196678827735 340803328235484295018241603)
          ·
            refine ⟨511204992353226442527362405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340803328235484295018241603 511204992353226442527362405)
            ·
              refine ⟨95850936066229957973880451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 511204992353226442527362405 95850936066229957973880451)
              ·
                refine ⟨143776404099344936960820677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95850936066229957973880451 143776404099344936960820677)
                ·
                  refine ⟨26958075768627175680153877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143776404099344936960820677 26958075768627175680153877)
                  ·
                    refine ⟨1263659801654398860007213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26958075768627175680153877 1263659801654398860007213)
                    ·
                      rfl

theorem cell23_7382906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_7382906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382906 prefixEnd_7382906 := by exact prefixLift 7382906
  have htrace : WordTrace (prefixWord ++ tailWord_7382906) baseStart_7382906 baseEnd_7382906 := by
    simpa [prefixWord, tailWord_7382906, baseEnd_7382906] using wordTrace_append hprefix tailTrace_7382906
  have hstable : (prefixWord ++ tailWord_7382906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382906).length < 2 ^ (prefixWord ++ tailWord_7382906).sum := by decide
  have hdescent : baseEnd_7382906 < baseStart_7382906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382956 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_7382956 : Nat := 118140960795 + 7382956 * 2 ^ 59
def prefixEnd_7382956 : Nat := 4983230072969 + 3 ^ 40 * 7382956 * 2
def baseEnd_7382956 : Nat := 3791005078995921384396409

theorem tailTrace_7382956 : CollatzResearch.WordTrace tailWord_7382956 prefixEnd_7382956 3791005078995921384396409 := by
  unfold tailWord_7382956
  simp only [CollatzResearch.WordTrace]
  refine ⟨134639263720409397671928361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179519018293879196895904481 134639263720409397671928361)
  ·
    refine ⟨100979447790307048253946271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134639263720409397671928361 100979447790307048253946271)
    ·
      refine ⟨151469171685460572380919407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100979447790307048253946271 151469171685460572380919407)
      ·
        refine ⟨227203757528190858571379111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151469171685460572380919407 227203757528190858571379111)
        ·
          refine ⟨340805636292286287857068667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227203757528190858571379111 340805636292286287857068667)
          ·
            refine ⟨511208454438429431785603001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340805636292286287857068667 511208454438429431785603001)
            ·
              refine ⟨383406340828822073839202251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511208454438429431785603001 383406340828822073839202251)
              ·
                refine ⟨575109511243233110758803377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383406340828822073839202251 575109511243233110758803377)
                ·
                  refine ⟨431332133432424833069102533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575109511243233110758803377 431332133432424833069102533)
                  ·
                    refine ⟨80874775018579656200456725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 431332133432424833069102533 80874775018579656200456725)
                    ·
                      refine ⟨3791005078995921384396409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80874775018579656200456725 3791005078995921384396409)
                      ·
                        rfl

theorem cell23_7382956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_7382956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382956 prefixEnd_7382956 := by exact prefixLift 7382956
  have htrace : WordTrace (prefixWord ++ tailWord_7382956) baseStart_7382956 baseEnd_7382956 := by
    simpa [prefixWord, tailWord_7382956, baseEnd_7382956] using wordTrace_append hprefix tailTrace_7382956
  have hstable : (prefixWord ++ tailWord_7382956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382956).length < 2 ^ (prefixWord ++ tailWord_7382956).sum := by decide
  have hdescent : baseEnd_7382956 < baseStart_7382956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382958 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7382958 : Nat := 118140960795 + 7382958 * 2 ^ 59
def prefixEnd_7382958 : Nat := 4983230072969 + 3 ^ 40 * 7382958 * 2
def baseEnd_7382958 : Nat := 3791006105957230376571401

theorem tailTrace_7382958 : CollatzResearch.WordTrace tailWord_7382958 prefixEnd_7382958 3791006105957230376571401 := by
  unfold tailWord_7382958
  simp only [CollatzResearch.WordTrace]
  refine ⟨33659825048351443710678691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179519066924541033123619685 33659825048351443710678691)
  ·
    refine ⟨50489737572527165566018037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33659825048351443710678691 50489737572527165566018037)
    ·
      refine ⟨4733412897424421771814191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50489737572527165566018037 4733412897424421771814191)
      ·
        refine ⟨7100119346136632657721287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733412897424421771814191 7100119346136632657721287)
        ·
          refine ⟨10650179019204948986581931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100119346136632657721287 10650179019204948986581931)
          ·
            refine ⟨15975268528807423479872897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10650179019204948986581931 15975268528807423479872897)
            ·
              refine ⟨11981451396605567609904673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15975268528807423479872897 11981451396605567609904673)
              ·
                refine ⟨8986088547454175707428505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11981451396605567609904673 8986088547454175707428505)
                ·
                  refine ⟨6739566410590631780571379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8986088547454175707428505 6739566410590631780571379)
                  ·
                    refine ⟨10109349615885947670857069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6739566410590631780571379 10109349615885947670857069)
                    ·
                      refine ⟨3791006105957230376571401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10109349615885947670857069 3791006105957230376571401)
                      ·
                        rfl

theorem cell23_7382958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7382958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382958 prefixEnd_7382958 := by exact prefixLift 7382958
  have htrace : WordTrace (prefixWord ++ tailWord_7382958) baseStart_7382958 baseEnd_7382958 := by
    simpa [prefixWord, tailWord_7382958, baseEnd_7382958] using wordTrace_append hprefix tailTrace_7382958
  have hstable : (prefixWord ++ tailWord_7382958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382958).length < 2 ^ (prefixWord ++ tailWord_7382958).sum := by decide
  have hdescent : baseEnd_7382958 < baseStart_7382958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382963 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 3]
def baseStart_7382963 : Nat := 118140960795 + 7382963 * 2 ^ 59
def prefixEnd_7382963 : Nat := 4983230072969 + 3 ^ 40 * 7382963 * 2
def baseEnd_7382963 : Nat := 3791008673360502857008877

theorem tailTrace_7382963 : CollatzResearch.WordTrace tailWord_7382963 prefixEnd_7382963 3791008673360502857008877 := by
  unfold tailWord_7382963
  simp only [CollatzResearch.WordTrace]
  refine ⟨269278782751793435539361543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179519188501195623692907695 269278782751793435539361543)
  ·
    refine ⟨403918174127690153309042315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269278782751793435539361543 403918174127690153309042315)
    ·
      refine ⟨605877261191535229963563473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403918174127690153309042315 605877261191535229963563473)
      ·
        refine ⟨454407945893651422472672605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605877261191535229963563473 454407945893651422472672605)
        ·
          refine ⟨170402979710119283427252227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454407945893651422472672605 170402979710119283427252227)
          ·
            refine ⟨255604469565178925140878341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170402979710119283427252227 255604469565178925140878341)
            ·
              refine ⟨47925838043471048463914689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255604469565178925140878341 47925838043471048463914689)
              ·
                refine ⟨35944378532603286347936017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47925838043471048463914689 35944378532603286347936017)
                ·
                  refine ⟨26958283899452464760952013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35944378532603286347936017 26958283899452464760952013)
                  ·
                    refine ⟨10109356462294674285357005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26958283899452464760952013 10109356462294674285357005)
                    ·
                      refine ⟨3791008673360502857008877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10109356462294674285357005 3791008673360502857008877)
                      ·
                        rfl

theorem cell23_7382963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 3].length) (baseStart_7382963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382963 prefixEnd_7382963 := by exact prefixLift 7382963
  have htrace : WordTrace (prefixWord ++ tailWord_7382963) baseStart_7382963 baseEnd_7382963 := by
    simpa [prefixWord, tailWord_7382963, baseEnd_7382963] using wordTrace_append hprefix tailTrace_7382963
  have hstable : (prefixWord ++ tailWord_7382963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382963).length < 2 ^ (prefixWord ++ tailWord_7382963).sum := by decide
  have hdescent : baseEnd_7382963 < baseStart_7382963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7382990 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2]
def baseStart_7382990 : Nat := 118140960795 + 7382990 * 2 ^ 59
def prefixEnd_7382990 : Nat := 4983230072969 + 3 ^ 40 * 7382990 * 2
def baseEnd_7382990 : Nat := 3791022537338174251371253

theorem tailTrace_7382990 : CollatzResearch.WordTrace tailWord_7382990 prefixEnd_7382990 3791022537338174251371253 := by
  unfold tailWord_7382990
  simp only [CollatzResearch.WordTrace]
  refine ⟨33659970940336952393824303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179519845015130412767062949 33659970940336952393824303)
  ·
    refine ⟨50489956410505428590736455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33659970940336952393824303 50489956410505428590736455)
    ·
      refine ⟨75734934615758142886104683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50489956410505428590736455 75734934615758142886104683)
      ·
        refine ⟨113602401923637214329157025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75734934615758142886104683 113602401923637214329157025)
        ·
          refine ⟨85201801442727910746867769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113602401923637214329157025 85201801442727910746867769)
          ·
            refine ⟨63901351082045933060150827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85201801442727910746867769 63901351082045933060150827)
            ·
              refine ⟨95852026623068899590226241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63901351082045933060150827 95852026623068899590226241)
              ·
                refine ⟨71889019967301674692669681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95852026623068899590226241 71889019967301674692669681)
                ·
                  refine ⟨53916764975476256019502261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71889019967301674692669681 53916764975476256019502261)
                  ·
                    refine ⟨5054696716450899001828337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53916764975476256019502261 5054696716450899001828337)
                    ·
                      refine ⟨3791022537338174251371253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5054696716450899001828337 3791022537338174251371253)
                      ·
                        rfl

theorem cell23_7382990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_7382990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7382990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7382990 prefixEnd_7382990 := by exact prefixLift 7382990
  have htrace : WordTrace (prefixWord ++ tailWord_7382990) baseStart_7382990 baseEnd_7382990 := by
    simpa [prefixWord, tailWord_7382990, baseEnd_7382990] using wordTrace_append hprefix tailTrace_7382990
  have hstable : (prefixWord ++ tailWord_7382990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7382990).length < 2 ^ (prefixWord ++ tailWord_7382990).sum := by decide
  have hdescent : baseEnd_7382990 < baseStart_7382990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7382990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383043 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 6]
def baseStart_7383043 : Nat := 118140960795 + 7383043 * 2 ^ 59
def prefixEnd_7383043 : Nat := 4983230072969 + 3 ^ 40 * 7383043 * 2
def baseEnd_7383043 : Nat := 421227750201429171556501

theorem tailTrace_7383043 : CollatzResearch.WordTrace tailWord_7383043 prefixEnd_7383043 421227750201429171556501 := by
  unfold tailWord_7383043
  simp only [CollatzResearch.WordTrace]
  refine ⟨269281700591503609202273783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179521133727669072801515855 269281700591503609202273783)
  ·
    refine ⟨403922550887255413803410675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269281700591503609202273783 403922550887255413803410675)
    ·
      refine ⟨605883826330883120705116013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403922550887255413803410675 605883826330883120705116013)
      ·
        refine ⟨227206434874081170264418505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605883826330883120705116013 227206434874081170264418505)
        ·
          refine ⟨170404826155560877698313879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227206434874081170264418505 170404826155560877698313879)
          ·
            refine ⟨255607239233341316547470819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170404826155560877698313879 255607239233341316547470819)
            ·
              refine ⟨383410858850011974821206229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255607239233341316547470819 383410858850011974821206229)
              ·
                refine ⟨8986192004297155659872021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 383410858850011974821206229 8986192004297155659872021)
                ·
                  refine ⟨421227750201429171556501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8986192004297155659872021 421227750201429171556501)
                  ·
                    rfl

theorem cell23_7383043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 6].length) (baseStart_7383043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383043 prefixEnd_7383043 := by exact prefixLift 7383043
  have htrace : WordTrace (prefixWord ++ tailWord_7383043) baseStart_7383043 baseEnd_7383043 := by
    simpa [prefixWord, tailWord_7383043, baseEnd_7383043] using wordTrace_append hprefix tailTrace_7383043
  have hstable : (prefixWord ++ tailWord_7383043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383043).length < 2 ^ (prefixWord ++ tailWord_7383043).sum := by decide
  have hdescent : baseEnd_7383043 < baseStart_7383043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383123 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 4]
def baseStart_7383123 : Nat := 118140960795 + 7383123 * 2 ^ 59
def prefixEnd_7383123 : Nat := 4983230072969 + 3 ^ 40 * 7383123 * 2
def baseEnd_7383123 : Nat := 3791090830265222231008141

theorem tailTrace_7383123 : CollatzResearch.WordTrace tailWord_7383123 prefixEnd_7383123 3791090830265222231008141 := by
  unfold tailWord_7383123
  simp only [CollatzResearch.WordTrace]
  refine ⟨269284618431213782865186023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179523078954142521910124015 269284618431213782865186023)
  ·
    refine ⟨403926927646820674297779035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269284618431213782865186023 403926927646820674297779035)
    ·
      refine ⟨605890391470231011446668553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403926927646820674297779035 605890391470231011446668553)
      ·
        refine ⟨454417793602673258585001415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605890391470231011446668553 454417793602673258585001415)
        ·
          refine ⟨681626690404009887877502123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454417793602673258585001415 681626690404009887877502123)
          ·
            refine ⟨1022440035606014831816253185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681626690404009887877502123 1022440035606014831816253185)
            ·
              refine ⟨766830026704511123862189889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022440035606014831816253185 766830026704511123862189889)
              ·
                refine ⟨575122520028383342896642417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766830026704511123862189889 575122520028383342896642417)
                ·
                  refine ⟨431341890021287507172481813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575122520028383342896642417 431341890021287507172481813)
                  ·
                    refine ⟨20219151094747851898710085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 431341890021287507172481813 20219151094747851898710085)
                    ·
                      refine ⟨3791090830265222231008141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20219151094747851898710085 3791090830265222231008141)
                      ·
                        rfl

theorem cell23_7383123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_7383123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383123 prefixEnd_7383123 := by exact prefixLift 7383123
  have htrace : WordTrace (prefixWord ++ tailWord_7383123) baseStart_7383123 baseEnd_7383123 := by
    simpa [prefixWord, tailWord_7383123, baseEnd_7383123] using wordTrace_append hprefix tailTrace_7383123
  have hstable : (prefixWord ++ tailWord_7383123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383123).length < 2 ^ (prefixWord ++ tailWord_7383123).sum := by decide
  have hdescent : baseEnd_7383123 < baseStart_7383123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383138 : List Nat := [3, 3, 2, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7383138 : Nat := 118140960795 + 7383138 * 2 ^ 59
def prefixEnd_7383138 : Nat := 4983230072969 + 3 ^ 40 * 7383138 * 2
def baseEnd_7383138 : Nat := 3791098532475039672320573

theorem tailTrace_7383138 : CollatzResearch.WordTrace tailWord_7383138 prefixEnd_7383138 3791098532475039672320573 := by
  unfold tailWord_7383138
  simp only [CollatzResearch.WordTrace]
  refine ⟨67321291381539860106745517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179523443684106293617988045 67321291381539860106745517)
  ·
    refine ⟨25245484268077447540029569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67321291381539860106745517 25245484268077447540029569)
    ·
      refine ⟨18934113201058085655022177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25245484268077447540029569 18934113201058085655022177)
      ·
        refine ⟨14200584900793564241266633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18934113201058085655022177 14200584900793564241266633)
        ·
          refine ⟨10650438675595173180949975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14200584900793564241266633 10650438675595173180949975)
          ·
            refine ⟨15975658013392759771424963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10650438675595173180949975 15975658013392759771424963)
            ·
              refine ⟨23963487020089139657137445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15975658013392759771424963 23963487020089139657137445)
              ·
                refine ⟨4493153816266713685713271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23963487020089139657137445 4493153816266713685713271)
                ·
                  refine ⟨6739730724400070528569907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493153816266713685713271 6739730724400070528569907)
                  ·
                    refine ⟨10109596086600105792854861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6739730724400070528569907 10109596086600105792854861)
                    ·
                      refine ⟨3791098532475039672320573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10109596086600105792854861 3791098532475039672320573)
                      ·
                        rfl

theorem cell23_7383138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7383138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383138 prefixEnd_7383138 := by exact prefixLift 7383138
  have htrace : WordTrace (prefixWord ++ tailWord_7383138) baseStart_7383138 baseEnd_7383138 := by
    simpa [prefixWord, tailWord_7383138, baseEnd_7383138] using wordTrace_append hprefix tailTrace_7383138
  have hstable : (prefixWord ++ tailWord_7383138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383138).length < 2 ^ (prefixWord ++ tailWord_7383138).sum := by decide
  have hdescent : baseEnd_7383138 < baseStart_7383138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383177 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 4, 1, 3]
def baseStart_7383177 : Nat := 118140960795 + 7383177 * 2 ^ 59
def prefixEnd_7383177 : Nat := 4983230072969 + 3 ^ 40 * 7383177 * 2
def baseEnd_7383177 : Nat := 3791118558220565019732893

theorem tailTrace_7383177 : CollatzResearch.WordTrace tailWord_7383177 prefixEnd_7383177 3791118558220565019732893 := by
  unfold tailWord_7383177
  simp only [CollatzResearch.WordTrace]
  refine ⟨269286587973018150087651785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179524391982012100058434523 269286587973018150087651785)
  ·
    refine ⟨201964940979763612565738839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269286587973018150087651785 201964940979763612565738839)
    ·
      refine ⟨302947411469645418848608259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201964940979763612565738839 302947411469645418848608259)
      ·
        refine ⟨454421117204468128272912389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302947411469645418848608259 454421117204468128272912389)
        ·
          refine ⟨85203959475837774051171073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454421117204468128272912389 85203959475837774051171073)
          ·
            refine ⟨63902969606878330538378305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85203959475837774051171073 63902969606878330538378305)
            ·
              refine ⟨47927227205158747903783729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63902969606878330538378305 47927227205158747903783729)
              ·
                refine ⟨35945420403869060927837797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47927227205158747903783729 35945420403869060927837797)
                ·
                  refine ⟨6739766325725448923969587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35945420403869060927837797 6739766325725448923969587)
                  ·
                    refine ⟨10109649488588173385954381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6739766325725448923969587 10109649488588173385954381)
                    ·
                      refine ⟨3791118558220565019732893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10109649488588173385954381 3791118558220565019732893)
                      ·
                        rfl

theorem cell23_7383177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 1, 3].length) (baseStart_7383177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383177 prefixEnd_7383177 := by exact prefixLift 7383177
  have htrace : WordTrace (prefixWord ++ tailWord_7383177) baseStart_7383177 baseEnd_7383177 := by
    simpa [prefixWord, tailWord_7383177, baseEnd_7383177] using wordTrace_append hprefix tailTrace_7383177
  have hstable : (prefixWord ++ tailWord_7383177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383177).length < 2 ^ (prefixWord ++ tailWord_7383177).sum := by decide
  have hdescent : baseEnd_7383177 < baseStart_7383177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383178 : List Nat := [3, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2]
def baseStart_7383178 : Nat := 118140960795 + 7383178 * 2 ^ 59
def prefixEnd_7383178 : Nat := 4983230072969 + 3 ^ 40 * 7383178 * 2
def baseEnd_7383178 : Nat := 3791119071701219515820389

theorem tailTrace_7383178 : CollatzResearch.WordTrace tailWord_7383178 prefixEnd_7383178 3791119071701219515820389 := by
  unfold tailWord_7383178
  simp only [CollatzResearch.WordTrace]
  refine ⟨67321656111503631814609547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179524416297343018172292125 67321656111503631814609547)
  ·
    refine ⟨100982484167255447721914321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67321656111503631814609547 100982484167255447721914321)
    ·
      refine ⟨75736863125441585791435741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100982484167255447721914321 75736863125441585791435741)
      ·
        refine ⟨28401323672040594671788403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75736863125441585791435741 28401323672040594671788403)
        ·
          refine ⟨42601985508060892007682605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28401323672040594671788403 42601985508060892007682605)
          ·
            refine ⟨15975744565522834502880977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42601985508060892007682605 15975744565522834502880977)
            ·
              refine ⟨11981808424142125877160733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15975744565522834502880977 11981808424142125877160733)
              ·
                refine ⟨4493178159053297203935275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11981808424142125877160733 4493178159053297203935275)
                ·
                  refine ⟨6739767238579945805902913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493178159053297203935275 6739767238579945805902913)
                  ·
                    refine ⟨5054825428934959354427185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6739767238579945805902913 5054825428934959354427185)
                    ·
                      refine ⟨3791119071701219515820389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5054825428934959354427185 3791119071701219515820389)
                      ·
                        rfl

theorem cell23_7383178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_7383178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383178 prefixEnd_7383178 := by exact prefixLift 7383178
  have htrace : WordTrace (prefixWord ++ tailWord_7383178) baseStart_7383178 baseEnd_7383178 := by
    simpa [prefixWord, tailWord_7383178, baseEnd_7383178] using wordTrace_append hprefix tailTrace_7383178
  have hstable : (prefixWord ++ tailWord_7383178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383178).length < 2 ^ (prefixWord ++ tailWord_7383178).sum := by decide
  have hdescent : baseEnd_7383178 < baseStart_7383178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383188 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_7383188 : Nat := 118140960795 + 7383188 * 2 ^ 59
def prefixEnd_7383188 : Nat := 4983230072969 + 3 ^ 40 * 7383188 * 2
def baseEnd_7383188 : Nat := 1263708068835921492231781

theorem tailTrace_7383188 : CollatzResearch.WordTrace tailWord_7383188 prefixEnd_7383188 1263708068835921492231781 := by
  unfold tailWord_7383188
  simp only [CollatzResearch.WordTrace]
  refine ⟨134643494587989149483151109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179524659450652199310868145 134643494587989149483151109)
  ·
    refine ⟨25245655235247965528090833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134643494587989149483151109 25245655235247965528090833)
    ·
      refine ⟨18934241426435974146068125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25245655235247965528090833 18934241426435974146068125)
      ·
        refine ⟨7100340534913490304775547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18934241426435974146068125 7100340534913490304775547)
        ·
          refine ⟨10650510802370235457163321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100340534913490304775547 10650510802370235457163321)
          ·
            refine ⟨7987883101777676592872491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10650510802370235457163321 7987883101777676592872491)
            ·
              refine ⟨11981824652666514889308737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7987883101777676592872491 11981824652666514889308737)
              ·
                refine ⟨8986368489499886166981553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11981824652666514889308737 8986368489499886166981553)
                ·
                  refine ⟨6739776367124914625236165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8986368489499886166981553 6739776367124914625236165)
                  ·
                    refine ⟨1263708068835921492231781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6739776367124914625236165 1263708068835921492231781)
                    ·
                      rfl

theorem cell23_7383188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_7383188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383188 prefixEnd_7383188 := by exact prefixLift 7383188
  have htrace : WordTrace (prefixWord ++ tailWord_7383188) baseStart_7383188 baseEnd_7383188 := by
    simpa [prefixWord, tailWord_7383188, baseEnd_7383188] using wordTrace_append hprefix tailTrace_7383188
  have hstable : (prefixWord ++ tailWord_7383188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383188).length < 2 ^ (prefixWord ++ tailWord_7383188).sum := by decide
  have hdescent : baseEnd_7383188 < baseStart_7383188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383257 : List Nat := [1, 2, 1, 2, 3, 1, 2, 6, 5]
def baseStart_7383257 : Nat := 118140960795 + 7383257 * 2 ^ 59
def prefixEnd_7383257 : Nat := 4983230072969 + 3 ^ 40 * 7383257 * 2
def baseEnd_7383257 : Nat := 421239959630324967414725

theorem tailTrace_7383257 : CollatzResearch.WordTrace tailWord_7383257 prefixEnd_7383257 421239959630324967414725 := by
  unfold tailWord_7383257
  simp only [CollatzResearch.WordTrace]
  refine ⟨269289505812728323750564025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179526337208485549167042683 269289505812728323750564025)
  ·
    refine ⟨201967129359546242812923019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269289505812728323750564025 201967129359546242812923019)
    ·
      refine ⟨302950694039319364219384529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201967129359546242812923019 302950694039319364219384529)
      ·
        refine ⟨227213020529489523164538397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302950694039319364219384529 227213020529489523164538397)
        ·
          refine ⟨85204882698558571186701899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227213020529489523164538397 85204882698558571186701899)
          ·
            refine ⟨127807324047837856780052849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85204882698558571186701899 127807324047837856780052849)
            ·
              refine ⟨95855493035878392585039637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127807324047837856780052849 95855493035878392585039637)
              ·
                refine ⟨4493226236056799652423733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95855493035878392585039637 4493226236056799652423733)
                ·
                  refine ⟨421239959630324967414725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4493226236056799652423733 421239959630324967414725)
                  ·
                    rfl

theorem cell23_7383257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 5].length) (baseStart_7383257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383257 prefixEnd_7383257 := by exact prefixLift 7383257
  have htrace : WordTrace (prefixWord ++ tailWord_7383257) baseStart_7383257 baseEnd_7383257 := by
    simpa [prefixWord, tailWord_7383257, baseEnd_7383257] using wordTrace_append hprefix tailTrace_7383257
  have hstable : (prefixWord ++ tailWord_7383257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383257).length < 2 ^ (prefixWord ++ tailWord_7383257).sum := by decide
  have hdescent : baseEnd_7383257 < baseStart_7383257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383307 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 4]
def baseStart_7383307 : Nat := 118140960795 + 7383307 * 2 ^ 59
def prefixEnd_7383307 : Nat := 4983230072969 + 3 ^ 40 * 7383307 * 2
def baseEnd_7383307 : Nat := 3791185310705649511107295

theorem tailTrace_7383307 : CollatzResearch.WordTrace tailWord_7383307 prefixEnd_7383307 3791185310705649511107295 := by
  unfold tailWord_7383307
  simp only [CollatzResearch.WordTrace]
  refine ⟨269291329462547182289884175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179527552975031454859922783 269291329462547182289884175)
  ·
    refine ⟨403936994193820773434826263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269291329462547182289884175 403936994193820773434826263)
    ·
      refine ⟨605905491290731160152239395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403936994193820773434826263 605905491290731160152239395)
      ·
        refine ⟨908858236936096740228359093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605905491290731160152239395 908858236936096740228359093)
        ·
          refine ⟨85205459712759069396408665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 908858236936096740228359093 85205459712759069396408665)
          ·
            refine ⟨63904094784569302047306499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85205459712759069396408665 63904094784569302047306499)
            ·
              refine ⟨95856142176853953070959749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63904094784569302047306499 95856142176853953070959749)
              ·
                refine ⟨17973026658160116200804953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95856142176853953070959749 17973026658160116200804953)
                ·
                  refine ⟨13479769993620087150603715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17973026658160116200804953 13479769993620087150603715)
                  ·
                    refine ⟨20219654990430130725905573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13479769993620087150603715 20219654990430130725905573)
                    ·
                      refine ⟨3791185310705649511107295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20219654990430130725905573 3791185310705649511107295)
                      ·
                        rfl

theorem cell23_7383307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 4].length) (baseStart_7383307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383307 prefixEnd_7383307 := by exact prefixLift 7383307
  have htrace : WordTrace (prefixWord ++ tailWord_7383307) baseStart_7383307 baseEnd_7383307 := by
    simpa [prefixWord, tailWord_7383307, baseEnd_7383307] using wordTrace_append hprefix tailTrace_7383307
  have hstable : (prefixWord ++ tailWord_7383307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383307).length < 2 ^ (prefixWord ++ tailWord_7383307).sum := by decide
  have hdescent : baseEnd_7383307 < baseStart_7383307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383338 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 2, 5]
def baseStart_7383338 : Nat := 118140960795 + 7383338 * 2 ^ 59
def prefixEnd_7383338 : Nat := 4983230072969 + 3 ^ 40 * 7383338 * 2
def baseEnd_7383338 : Nat := 1263733742868646296606551

theorem tailTrace_7383338 : CollatzResearch.WordTrace tailWord_7383338 prefixEnd_7383338 1263733742868646296606551 := by
  unfold tailWord_7383338
  simp only [CollatzResearch.WordTrace]
  refine ⟨67323115031358718646065667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179528306750289916389508445 67323115031358718646065667)
  ·
    refine ⟨100984672547038077969098501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67323115031358718646065667 100984672547038077969098501)
    ·
      refine ⟨18934626102569639619205969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100984672547038077969098501 18934626102569639619205969)
      ·
        refine ⟨14200969576927229714404477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18934626102569639619205969 14200969576927229714404477)
        ·
          refine ⟨5325363591347711142901679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14200969576927229714404477 5325363591347711142901679)
          ·
            refine ⟨7988045387021566714352519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5325363591347711142901679 7988045387021566714352519)
            ·
              refine ⟨11982068080532350071528779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7988045387021566714352519 11982068080532350071528779)
              ·
                refine ⟨17973102120798525107293169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11982068080532350071528779 17973102120798525107293169)
                ·
                  refine ⟨13479826590598893830469877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17973102120798525107293169 13479826590598893830469877)
                  ·
                    refine ⟨1263733742868646296606551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13479826590598893830469877 1263733742868646296606551)
                    ·
                      rfl

theorem cell23_7383338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_7383338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383338 prefixEnd_7383338 := by exact prefixLift 7383338
  have htrace : WordTrace (prefixWord ++ tailWord_7383338) baseStart_7383338 baseEnd_7383338 := by
    simpa [prefixWord, tailWord_7383338, baseEnd_7383338] using wordTrace_append hprefix tailTrace_7383338
  have hstable : (prefixWord ++ tailWord_7383338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383338).length < 2 ^ (prefixWord ++ tailWord_7383338).sum := by decide
  have hdescent : baseEnd_7383338 < baseStart_7383338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383341 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_7383341 : Nat := 118140960795 + 7383341 * 2 ^ 59
def prefixEnd_7383341 : Nat := 4983230072969 + 3 ^ 40 * 7383341 * 2
def baseEnd_7383341 : Nat := 3791202769047902378082139

theorem tailTrace_7383341 : CollatzResearch.WordTrace tailWord_7383341 prefixEnd_7383341 3791202769047902378082139 := by
  unfold tailWord_7383341
  simp only [CollatzResearch.WordTrace]
  refine ⟨269292569544424006096621877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179528379696282670731081251 269292569544424006096621877)
  ·
    refine ⟨25246178394789750571558301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269292569544424006096621877 25246178394789750571558301)
    ·
      refine ⟨9467316898046156464334363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25246178394789750571558301 9467316898046156464334363)
      ·
        refine ⟨14200975347069234696501545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9467316898046156464334363 14200975347069234696501545)
        ·
          refine ⟨10650731510301926022376159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14200975347069234696501545 10650731510301926022376159)
          ·
            refine ⟨15976097265452889033564239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10650731510301926022376159 15976097265452889033564239)
            ·
              refine ⟨23964145898179333550346359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15976097265452889033564239 23964145898179333550346359)
              ·
                refine ⟨35946218847269000325519539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23964145898179333550346359 35946218847269000325519539)
                ·
                  refine ⟨53919328270903500488279309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35946218847269000325519539 53919328270903500488279309)
                  ·
                    refine ⟨20219748101588812683104741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53919328270903500488279309 20219748101588812683104741)
                    ·
                      refine ⟨3791202769047902378082139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20219748101588812683104741 3791202769047902378082139)
                      ·
                        rfl

theorem cell23_7383341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_7383341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383341 prefixEnd_7383341 := by exact prefixLift 7383341
  have htrace : WordTrace (prefixWord ++ tailWord_7383341) baseStart_7383341 baseEnd_7383341 := by
    simpa [prefixWord, tailWord_7383341, baseEnd_7383341] using wordTrace_append hprefix tailTrace_7383341
  have hstable : (prefixWord ++ tailWord_7383341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383341).length < 2 ^ (prefixWord ++ tailWord_7383341).sum := by decide
  have hdescent : baseEnd_7383341 < baseStart_7383341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383381 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 6]
def baseStart_7383381 : Nat := 118140960795 + 7383381 * 2 ^ 59
def prefixEnd_7383381 : Nat := 4983230072969 + 3 ^ 40 * 7383381 * 2
def baseEnd_7383381 : Nat := 421247034252675802397995

theorem tailTrace_7383381 : CollatzResearch.WordTrace tailWord_7383381 prefixEnd_7383381 421247034252675802397995 := by
  unfold tailWord_7383381
  simp only [CollatzResearch.WordTrace]
  refine ⟨269294028464279092928077997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179529352309519395285385331 269294028464279092928077997)
  ·
    refine ⟨100985260674104659848029249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269294028464279092928077997 100985260674104659848029249)
    ·
      refine ⟨75738945505578494886021937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100985260674104659848029249 75738945505578494886021937)
      ·
        refine ⟨56804209129183871164516453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75738945505578494886021937 56804209129183871164516453)
        ·
          refine ⟨10650789211721975843346835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56804209129183871164516453 10650789211721975843346835)
          ·
            refine ⟨15976183817582963765020253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10650789211721975843346835 15976183817582963765020253)
            ·
              refine ⟨5991068931593611411882595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15976183817582963765020253 5991068931593611411882595)
              ·
                refine ⟨8986603397390417117823893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991068931593611411882595 8986603397390417117823893)
                ·
                  refine ⟨421247034252675802397995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8986603397390417117823893 421247034252675802397995)
                  ·
                    rfl

theorem cell23_7383381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_7383381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383381 prefixEnd_7383381 := by exact prefixLift 7383381
  have htrace : WordTrace (prefixWord ++ tailWord_7383381) baseStart_7383381 baseEnd_7383381 := by
    simpa [prefixWord, tailWord_7383381, baseEnd_7383381] using wordTrace_append hprefix tailTrace_7383381
  have hstable : (prefixWord ++ tailWord_7383381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383381).length < 2 ^ (prefixWord ++ tailWord_7383381).sum := by decide
  have hdescent : baseEnd_7383381 < baseStart_7383381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383384 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 6, 3, 2]
def baseStart_7383384 : Nat := 118140960795 + 7383384 * 2 ^ 59
def prefixEnd_7383384 : Nat := 4983230072969 + 3 ^ 40 * 7383384 * 2
def baseEnd_7383384 : Nat := 3791224848716045709844441

theorem tailTrace_7383384 : CollatzResearch.WordTrace tailWord_7383384 prefixEnd_7383384 3791224848716045709844441 := by
  unfold tailWord_7383384
  simp only [CollatzResearch.WordTrace]
  refine ⟨134647068941634112220218603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179529425255512149626958137 134647068941634112220218603)
  ·
    refine ⟨201970603412451168330327905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134647068941634112220218603 201970603412451168330327905)
    ·
      refine ⟨151477952559338376247745929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201970603412451168330327905 151477952559338376247745929)
      ·
        refine ⟨113608464419503782185809447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151477952559338376247745929 113608464419503782185809447)
        ·
          refine ⟨170412696629255673278714171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113608464419503782185809447 170412696629255673278714171)
          ·
            refine ⟨255619044943883509918071257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170412696629255673278714171 255619044943883509918071257)
            ·
              refine ⟨191714283707912632438553443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255619044943883509918071257 191714283707912632438553443)
              ·
                refine ⟨287571425561868948657830165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191714283707912632438553443 287571425561868948657830165)
                ·
                  refine ⟨13479910573212606968335789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 287571425561868948657830165 13479910573212606968335789)
                  ·
                    refine ⟨5054966464954727613125921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13479910573212606968335789 5054966464954727613125921)
                    ·
                      refine ⟨3791224848716045709844441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5054966464954727613125921 3791224848716045709844441)
                      ·
                        rfl

theorem cell23_7383384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_7383384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383384 prefixEnd_7383384 := by exact prefixLift 7383384
  have htrace : WordTrace (prefixWord ++ tailWord_7383384) baseStart_7383384 baseEnd_7383384 := by
    simpa [prefixWord, tailWord_7383384, baseEnd_7383384] using wordTrace_append hprefix tailTrace_7383384
  have hstable : (prefixWord ++ tailWord_7383384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383384).length < 2 ^ (prefixWord ++ tailWord_7383384).sum := by decide
  have hdescent : baseEnd_7383384 < baseStart_7383384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383408 : List Nat := [2, 1, 1, 1, 4, 3, 3, 3, 1, 1, 3]
def baseStart_7383408 : Nat := 118140960795 + 7383408 * 2 ^ 59
def prefixEnd_7383408 : Nat := 4983230072969 + 3 ^ 40 * 7383408 * 2
def baseEnd_7383408 : Nat := 3791237172251753615944331

theorem tailTrace_7383408 : CollatzResearch.WordTrace tailWord_7383408 prefixEnd_7383408 3791237172251753615944331 := by
  unfold tailWord_7383408
  simp only [CollatzResearch.WordTrace]
  refine ⟨134647506617590638269655439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179530008823454184359540585 134647506617590638269655439)
  ·
    refine ⟨201971259926385957404483159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134647506617590638269655439 201971259926385957404483159)
    ·
      refine ⟨302956889889578936106724739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201971259926385957404483159 302956889889578936106724739)
      ·
        refine ⟨454435334834368404160087109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302956889889578936106724739 454435334834368404160087109)
        ·
          refine ⟨85206625281444075780016333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454435334834368404160087109 85206625281444075780016333)
          ·
            refine ⟨31952484480541528417506125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85206625281444075780016333 31952484480541528417506125)
            ·
              refine ⟨11982181680203073156564797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31952484480541528417506125 11982181680203073156564797)
              ·
                refine ⟨4493318130076152433711799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11982181680203073156564797 4493318130076152433711799)
                ·
                  refine ⟨6739977195114228650567699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493318130076152433711799 6739977195114228650567699)
                  ·
                    refine ⟨10109965792671342975851549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6739977195114228650567699 10109965792671342975851549)
                    ·
                      refine ⟨3791237172251753615944331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10109965792671342975851549 3791237172251753615944331)
                      ·
                        rfl

theorem cell23_7383408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 1, 1, 3].length) (baseStart_7383408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383408 prefixEnd_7383408 := by exact prefixLift 7383408
  have htrace : WordTrace (prefixWord ++ tailWord_7383408) baseStart_7383408 baseEnd_7383408 := by
    simpa [prefixWord, tailWord_7383408, baseEnd_7383408] using wordTrace_append hprefix tailTrace_7383408
  have hstable : (prefixWord ++ tailWord_7383408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383408).length < 2 ^ (prefixWord ++ tailWord_7383408).sum := by decide
  have hdescent : baseEnd_7383408 < baseStart_7383408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383448 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 1, 1, 4]
def baseStart_7383448 : Nat := 118140960795 + 7383448 * 2 ^ 59
def prefixEnd_7383448 : Nat := 4983230072969 + 3 ^ 40 * 7383448 * 2
def baseEnd_7383448 : Nat := 3791257711477933459444147

theorem tailTrace_7383448 : CollatzResearch.WordTrace tailWord_7383448 prefixEnd_7383448 3791257711477933459444147 := by
  unfold tailWord_7383448
  simp only [CollatzResearch.WordTrace]
  refine ⟨134648236077518181685383499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179530981436690908913844665 134648236077518181685383499)
  ·
    refine ⟨201972354116277272528075249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134648236077518181685383499 201972354116277272528075249)
    ·
      refine ⟨151479265587207954396056437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201972354116277272528075249 151479265587207954396056437)
      ·
        refine ⟨14201181148800745724630291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151479265587207954396056437 14201181148800745724630291)
        ·
          refine ⟨21301771723201118586945437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14201181148800745724630291 21301771723201118586945437)
          ·
            refine ⟨7988164396200419470104539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21301771723201118586945437 7988164396200419470104539)
            ·
              refine ⟨11982246594300629205156809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7988164396200419470104539 11982246594300629205156809)
              ·
                refine ⟨8986684945725471903867607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11982246594300629205156809 8986684945725471903867607)
                ·
                  refine ⟨13480027418588207855801411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8986684945725471903867607 13480027418588207855801411)
                  ·
                    refine ⟨20220041127882311783702117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13480027418588207855801411 20220041127882311783702117)
                    ·
                      refine ⟨3791257711477933459444147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20220041127882311783702117 3791257711477933459444147)
                      ·
                        rfl

theorem cell23_7383448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_7383448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383448 prefixEnd_7383448 := by exact prefixLift 7383448
  have htrace : WordTrace (prefixWord ++ tailWord_7383448) baseStart_7383448 baseEnd_7383448 := by
    simpa [prefixWord, tailWord_7383448, baseEnd_7383448] using wordTrace_append hprefix tailTrace_7383448
  have hstable : (prefixWord ++ tailWord_7383448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383448).length < 2 ^ (prefixWord ++ tailWord_7383448).sum := by decide
  have hdescent : baseEnd_7383448 < baseStart_7383448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383476 : List Nat := [2, 5, 2, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_7383476 : Nat := 118140960795 + 7383476 * 2 ^ 59
def prefixEnd_7383476 : Nat := 4983230072969 + 3 ^ 40 * 7383476 * 2
def baseEnd_7383476 : Nat := 3791272088936259349894019

theorem tailTrace_7383476 : CollatzResearch.WordTrace tailWord_7383476 prefixEnd_7383476 3791272088936259349894019 := by
  unfold tailWord_7383476
  simp only [CollatzResearch.WordTrace]
  refine ⟨134648746699467462076393141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179531662265956616101857521 134648746699467462076393141)
  ·
    refine ⟨12623320003075074569661857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134648746699467462076393141 12623320003075074569661857)
    ·
      refine ⟨9467490002306305927246393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12623320003075074569661857 9467490002306305927246393)
      ·
        refine ⟨7100617501729729445434795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9467490002306305927246393 7100617501729729445434795)
        ·
          refine ⟨10650926252594594168152193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100617501729729445434795 10650926252594594168152193)
          ·
            refine ⟨7988194689445945626114145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10650926252594594168152193 7988194689445945626114145)
            ·
              refine ⟨5991146017084459219585609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7988194689445945626114145 5991146017084459219585609)
              ·
                refine ⟨4493359512813344414689207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5991146017084459219585609 4493359512813344414689207)
                ·
                  refine ⟨6740039269220016622033811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493359512813344414689207 6740039269220016622033811)
                  ·
                    refine ⟨10110058903830024933050717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6740039269220016622033811 10110058903830024933050717)
                    ·
                      refine ⟨3791272088936259349894019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10110058903830024933050717 3791272088936259349894019)
                      ·
                        rfl

theorem cell23_7383476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_7383476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383476 prefixEnd_7383476 := by exact prefixLift 7383476
  have htrace : WordTrace (prefixWord ++ tailWord_7383476) baseStart_7383476 baseEnd_7383476 := by
    simpa [prefixWord, tailWord_7383476, baseEnd_7383476] using wordTrace_append hprefix tailTrace_7383476
  have hstable : (prefixWord ++ tailWord_7383476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383476).length < 2 ^ (prefixWord ++ tailWord_7383476).sum := by decide
  have hdescent : baseEnd_7383476 < baseStart_7383476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383484 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_7383484 : Nat := 118140960795 + 7383484 * 2 ^ 59
def prefixEnd_7383484 : Nat := 4983230072969 + 3 ^ 40 * 7383484 * 2
def baseEnd_7383484 : Nat := 1263758732260498439531327

theorem tailTrace_7383484 : CollatzResearch.WordTrace tailWord_7383484 prefixEnd_7383484 1263758732260498439531327 := by
  unfold tailWord_7383484
  simp only [CollatzResearch.WordTrace]
  refine ⟨134648892591452970759538753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179531856788603961012718337 134648892591452970759538753)
  ·
    refine ⟨100986669443589728069654065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134648892591452970759538753 100986669443589728069654065)
    ·
      refine ⟨75740002082692296052240549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100986669443589728069654065 75740002082692296052240549)
      ·
        refine ⟨14201250390504805509795103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75740002082692296052240549 14201250390504805509795103)
        ·
          refine ⟨21301875585757208264692655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14201250390504805509795103 21301875585757208264692655)
          ·
            refine ⟨31952813378635812397038983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21301875585757208264692655 31952813378635812397038983)
            ·
              refine ⟨47929220067953718595558475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31952813378635812397038983 47929220067953718595558475)
              ·
                refine ⟨71893830101930577893337713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47929220067953718595558475 71893830101930577893337713)
                ·
                  refine ⟨53920372576447933420003285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71893830101930577893337713 53920372576447933420003285)
                  ·
                    refine ⟨1263758732260498439531327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53920372576447933420003285 1263758732260498439531327)
                    ·
                      rfl

theorem cell23_7383484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_7383484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383484 prefixEnd_7383484 := by exact prefixLift 7383484
  have htrace : WordTrace (prefixWord ++ tailWord_7383484) baseStart_7383484 baseEnd_7383484 := by
    simpa [prefixWord, tailWord_7383484, baseEnd_7383484] using wordTrace_append hprefix tailTrace_7383484
  have hstable : (prefixWord ++ tailWord_7383484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383484).length < 2 ^ (prefixWord ++ tailWord_7383484).sum := by decide
  have hdescent : baseEnd_7383484 < baseStart_7383484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383497 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 1, 8]
def baseStart_7383497 : Nat := 118140960795 + 7383497 * 2 ^ 59
def prefixEnd_7383497 : Nat := 4983230072969 + 3 ^ 40 * 7383497 * 2
def baseEnd_7383497 : Nat := 1263760957343334589243807

theorem tailTrace_7383497 : CollatzResearch.WordTrace tailWord_7383497 prefixEnd_7383497 1263760957343334589243807 := by
  unfold tailWord_7383497
  simp only [CollatzResearch.WordTrace]
  refine ⟨269298259331858844739300745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179532172887905896492867163 269298259331858844739300745)
  ·
    refine ⟨201973694498894133554475559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269298259331858844739300745 201973694498894133554475559)
    ·
      refine ⟨302960541748341200331713339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201973694498894133554475559 302960541748341200331713339)
      ·
        refine ⟨454440812622511800497570009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302960541748341200331713339 454440812622511800497570009)
        ·
          refine ⟨340830609466883850373177507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454440812622511800497570009 340830609466883850373177507)
          ·
            refine ⟨511245914200325775559766261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340830609466883850373177507 511245914200325775559766261)
            ·
              refine ⟨47929304456280541458728087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 511245914200325775559766261 47929304456280541458728087)
              ·
                refine ⟨71893956684420812188092131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47929304456280541458728087 71893956684420812188092131)
                ·
                  refine ⟨107840935026631218282138197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71893956684420812188092131 107840935026631218282138197)
                  ·
                    refine ⟨1263760957343334589243807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107840935026631218282138197 1263760957343334589243807)
                    ·
                      rfl

theorem cell23_7383497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_7383497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383497 prefixEnd_7383497 := by exact prefixLift 7383497
  have htrace : WordTrace (prefixWord ++ tailWord_7383497) baseStart_7383497 baseEnd_7383497 := by
    simpa [prefixWord, tailWord_7383497, baseEnd_7383497] using wordTrace_append hprefix tailTrace_7383497
  have hstable : (prefixWord ++ tailWord_7383497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383497).length < 2 ^ (prefixWord ++ tailWord_7383497).sum := by decide
  have hdescent : baseEnd_7383497 < baseStart_7383497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383508 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_7383508 : Nat := 118140960795 + 7383508 * 2 ^ 59
def prefixEnd_7383508 : Nat := 4983230072969 + 3 ^ 40 * 7383508 * 2
def baseEnd_7383508 : Nat := 3791288520317203224693871

theorem tailTrace_7383508 : CollatzResearch.WordTrace tailWord_7383508 prefixEnd_7383508 3791288520317203224693871 := by
  unfold tailWord_7383508
  simp only [CollatzResearch.WordTrace]
  refine ⟨134649330267409496808975589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179532440356545995745300785 134649330267409496808975589)
  ·
    refine ⟨25246749425139280651682923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134649330267409496808975589 25246749425139280651682923)
    ·
      refine ⟨37870124137708920977524385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25246749425139280651682923 37870124137708920977524385)
      ·
        refine ⟨28402593103281690733143289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37870124137708920977524385 28402593103281690733143289)
        ·
          refine ⟨21301944827461268049857467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28402593103281690733143289 21301944827461268049857467)
          ·
            refine ⟨31952917241191902074786201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21301944827461268049857467 31952917241191902074786201)
            ·
              refine ⟨23964687930893926556089651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31952917241191902074786201 23964687930893926556089651)
              ·
                refine ⟨35947031896340889834134477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23964687930893926556089651 35947031896340889834134477)
                ·
                  refine ⟨13480136961127833687800429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35947031896340889834134477 13480136961127833687800429)
                  ·
                    refine ⟨5055051360422937632925161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13480136961127833687800429 5055051360422937632925161)
                    ·
                      refine ⟨3791288520317203224693871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055051360422937632925161 3791288520317203224693871)
                      ·
                        rfl

theorem cell23_7383508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_7383508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383508 prefixEnd_7383508 := by exact prefixLift 7383508
  have htrace : WordTrace (prefixWord ++ tailWord_7383508) baseStart_7383508 baseEnd_7383508 := by
    simpa [prefixWord, tailWord_7383508, baseEnd_7383508] using wordTrace_append hprefix tailTrace_7383508
  have hstable : (prefixWord ++ tailWord_7383508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383508).length < 2 ^ (prefixWord ++ tailWord_7383508).sum := by decide
  have hdescent : baseEnd_7383508 < baseStart_7383508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383521 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 1, 4, 2]
def baseStart_7383521 : Nat := 118140960795 + 7383521 * 2 ^ 59
def prefixEnd_7383521 : Nat := 4983230072969 + 3 ^ 40 * 7383521 * 2
def baseEnd_7383521 : Nat := 3791295195565711673831311

theorem tailTrace_7383521 : CollatzResearch.WordTrace tailWord_7383521 prefixEnd_7383521 3791295195565711673831311 := by
  unfold tailWord_7383521
  simp only [CollatzResearch.WordTrace]
  refine ⟨269299134683771896838174417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179532756455847931225449611 269299134683771896838174417)
  ·
    refine ⟨201974351012828922628630813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269299134683771896838174417 201974351012828922628630813)
    ·
      refine ⟨75740381629810845985736555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201974351012828922628630813 75740381629810845985736555)
      ·
        refine ⟨113610572444716268978604833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75740381629810845985736555 113610572444716268978604833)
        ·
          refine ⟨85207929333537201733953625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113610572444716268978604833 85207929333537201733953625)
          ·
            refine ⟨63905947000152901300465219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85207929333537201733953625 63905947000152901300465219)
            ·
              refine ⟨95858920500229351950697829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63905947000152901300465219 95858920500229351950697829)
              ·
                refine ⟨17973547593793003490755843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95858920500229351950697829 17973547593793003490755843)
                ·
                  refine ⟨26960321390689505236133765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17973547593793003490755843 26960321390689505236133765)
                  ·
                    refine ⟨5055060260754282231775081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26960321390689505236133765 5055060260754282231775081)
                    ·
                      refine ⟨3791295195565711673831311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055060260754282231775081 3791295195565711673831311)
                      ·
                        rfl

theorem cell23_7383521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_7383521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383521 prefixEnd_7383521 := by exact prefixLift 7383521
  have htrace : WordTrace (prefixWord ++ tailWord_7383521) baseStart_7383521 baseEnd_7383521 := by
    simpa [prefixWord, tailWord_7383521, baseEnd_7383521] using wordTrace_append hprefix tailTrace_7383521
  have hstable : (prefixWord ++ tailWord_7383521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383521).length < 2 ^ (prefixWord ++ tailWord_7383521).sum := by decide
  have hdescent : baseEnd_7383521 < baseStart_7383521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383525 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 1, 3, 2]
def baseStart_7383525 : Nat := 118140960795 + 7383525 * 2 ^ 59
def prefixEnd_7383525 : Nat := 4983230072969 + 3 ^ 40 * 7383525 * 2
def baseEnd_7383525 : Nat := 3791297249488329658181293

theorem tailTrace_7383525 : CollatzResearch.WordTrace tailWord_7383525 prefixEnd_7383525 3791297249488329658181293 := by
  unfold tailWord_7383525
  simp only [CollatzResearch.WordTrace]
  refine ⟨269299280575757405521320029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179532853717171603680880019 269299280575757405521320029)
  ·
    refine ⟨100987230215909027070495011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269299280575757405521320029 100987230215909027070495011)
    ·
      refine ⟨151480845323863540605742517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100987230215909027070495011 151480845323863540605742517)
      ·
        refine ⟨14201329249112206931788361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151480845323863540605742517 14201329249112206931788361)
        ·
          refine ⟨10650996936834155198841271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14201329249112206931788361 10650996936834155198841271)
          ·
            refine ⟨15976495405251232798261907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10650996936834155198841271 15976495405251232798261907)
            ·
              refine ⟨23964743107876849197392861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15976495405251232798261907 23964743107876849197392861)
              ·
                refine ⟨8986778665453818449022323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23964743107876849197392861 8986778665453818449022323)
                ·
                  refine ⟨13480167998180727673533485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8986778665453818449022323 13480167998180727673533485)
                  ·
                    refine ⟨5055062999317772877575057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13480167998180727673533485 5055062999317772877575057)
                    ·
                      refine ⟨3791297249488329658181293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055062999317772877575057 3791297249488329658181293)
                      ·
                        rfl

theorem cell23_7383525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_7383525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383525 prefixEnd_7383525 := by exact prefixLift 7383525
  have htrace : WordTrace (prefixWord ++ tailWord_7383525) baseStart_7383525 baseEnd_7383525 := by
    simpa [prefixWord, tailWord_7383525, baseEnd_7383525] using wordTrace_append hprefix tailTrace_7383525
  have hstable : (prefixWord ++ tailWord_7383525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383525).length < 2 ^ (prefixWord ++ tailWord_7383525).sum := by decide
  have hdescent : baseEnd_7383525 < baseStart_7383525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383544 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 7]
def baseStart_7383544 : Nat := 118140960795 + 7383544 * 2 ^ 59
def prefixEnd_7383544 : Nat := 4983230072969 + 3 ^ 40 * 7383544 * 2
def baseEnd_7383544 : Nat := 421256333957862787093745

theorem tailTrace_7383544 : CollatzResearch.WordTrace tailWord_7383544 prefixEnd_7383544 421256333957862787093745 := by
  unfold tailWord_7383544
  simp only [CollatzResearch.WordTrace]
  refine ⟨134649986781344285883130843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179533315708459047844174457 134649986781344285883130843)
  ·
    refine ⟨201974980172016428824696265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134649986781344285883130843 201974980172016428824696265)
    ·
      refine ⟨151481235129012321618522199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201974980172016428824696265 151481235129012321618522199)
      ·
        refine ⟨227221852693518482427783299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151481235129012321618522199 227221852693518482427783299)
        ·
          refine ⟨340832779040277723641674949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227221852693518482427783299 340832779040277723641674949)
          ·
            refine ⟨63906146070052073182814053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340832779040277723641674949 63906146070052073182814053)
            ·
              refine ⟨11982402388134763721777635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63906146070052073182814053 11982402388134763721777635)
              ·
                refine ⟨17973603582202145582666453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11982402388134763721777635 17973603582202145582666453)
                ·
                  refine ⟨421256333957862787093745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17973603582202145582666453 421256333957862787093745)
                  ·
                    rfl

theorem cell23_7383544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 7].length) (baseStart_7383544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383544 prefixEnd_7383544 := by exact prefixLift 7383544
  have htrace : WordTrace (prefixWord ++ tailWord_7383544) baseStart_7383544 baseEnd_7383544 := by
    simpa [prefixWord, tailWord_7383544, baseEnd_7383544] using wordTrace_append hprefix tailTrace_7383544
  have hstable : (prefixWord ++ tailWord_7383544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383544).length < 2 ^ (prefixWord ++ tailWord_7383544).sum := by decide
  have hdescent : baseEnd_7383544 < baseStart_7383544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383547 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 8]
def baseStart_7383547 : Nat := 118140960795 + 7383547 * 2 ^ 59
def prefixEnd_7383547 : Nat := 4983230072969 + 3 ^ 40 * 7383547 * 2
def baseEnd_7383547 : Nat := 3791308546062728572106191

theorem tailTrace_7383547 : CollatzResearch.WordTrace tailWord_7383547 prefixEnd_7383547 3791308546062728572106191 := by
  unfold tailWord_7383547
  simp only [CollatzResearch.WordTrace]
  refine ⟨269300082981677703278620895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179533388654451802185747263 269300082981677703278620895)
  ·
    refine ⟨403950124472516554917931343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269300082981677703278620895 403950124472516554917931343)
    ·
      refine ⟨605925186708774832376897015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403950124472516554917931343 605925186708774832376897015)
      ·
        refine ⟨908887780063162248565345523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605925186708774832376897015 908887780063162248565345523)
        ·
          refine ⟨1363331670094743372848018285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908887780063162248565345523 1363331670094743372848018285)
          ·
            refine ⟨511249376285528764818006857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1363331670094743372848018285 511249376285528764818006857)
            ·
              refine ⟨383437032214146573613505143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511249376285528764818006857 383437032214146573613505143)
              ·
                refine ⟨575155548321219860420257715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383437032214146573613505143 575155548321219860420257715)
                ·
                  refine ⟨862733322481829790630386573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575155548321219860420257715 862733322481829790630386573)
                  ·
                    refine ⟨323524995930686171486394965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 862733322481829790630386573 323524995930686171486394965)
                    ·
                      refine ⟨3791308546062728572106191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 323524995930686171486394965 3791308546062728572106191)
                      ·
                        rfl

theorem cell23_7383547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_7383547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383547 prefixEnd_7383547 := by exact prefixLift 7383547
  have htrace : WordTrace (prefixWord ++ tailWord_7383547) baseStart_7383547 baseEnd_7383547 := by
    simpa [prefixWord, tailWord_7383547, baseEnd_7383547] using wordTrace_append hprefix tailTrace_7383547
  have hstable : (prefixWord ++ tailWord_7383547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383547).length < 2 ^ (prefixWord ++ tailWord_7383547).sum := by decide
  have hdescent : baseEnd_7383547 < baseStart_7383547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383555 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 2, 2, 2]
def baseStart_7383555 : Nat := 118140960795 + 7383555 * 2 ^ 59
def prefixEnd_7383555 : Nat := 4983230072969 + 3 ^ 40 * 7383555 * 2
def baseEnd_7383555 : Nat := 3791312653907964540806155

theorem tailTrace_7383555 : CollatzResearch.WordTrace tailWord_7383555 prefixEnd_7383555 3791312653907964540806155 := by
  unfold tailWord_7383555
  simp only [CollatzResearch.WordTrace]
  refine ⟨269300374765648720644912119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179533583177099147096608079 269300374765648720644912119)
  ·
    refine ⟨403950562148473080967368179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269300374765648720644912119 403950562148473080967368179)
    ·
      refine ⟨605925843222709621451052269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403950562148473080967368179 605925843222709621451052269)
      ·
        refine ⟨227222191208516108044144601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605925843222709621451052269 227222191208516108044144601)
        ·
          refine ⟨170416643406387081033108451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227222191208516108044144601 170416643406387081033108451)
          ·
            refine ⟨255624965109580621549662677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170416643406387081033108451 255624965109580621549662677)
            ·
              refine ⟨5991210119755795817570219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 255624965109580621549662677 5991210119755795817570219)
              ·
                refine ⟨8986815179633693726355329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991210119755795817570219 8986815179633693726355329)
                ·
                  refine ⟨6740111384725270294766497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8986815179633693726355329 6740111384725270294766497)
                  ·
                    refine ⟨5055083538543952721074873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6740111384725270294766497 5055083538543952721074873)
                    ·
                      refine ⟨3791312653907964540806155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055083538543952721074873 3791312653907964540806155)
                      ·
                        rfl

theorem cell23_7383555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_7383555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383555 prefixEnd_7383555 := by exact prefixLift 7383555
  have htrace : WordTrace (prefixWord ++ tailWord_7383555) baseStart_7383555 baseEnd_7383555 := by
    simpa [prefixWord, tailWord_7383555, baseEnd_7383555] using wordTrace_append hprefix tailTrace_7383555
  have hstable : (prefixWord ++ tailWord_7383555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383555).length < 2 ^ (prefixWord ++ tailWord_7383555).sum := by decide
  have hdescent : baseEnd_7383555 < baseStart_7383555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383624 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_7383624 : Nat := 118140960795 + 7383624 * 2 ^ 59
def prefixEnd_7383624 : Nat := 4983230072969 + 3 ^ 40 * 7383624 * 2
def baseEnd_7383624 : Nat := 3791348084073124770843337

theorem tailTrace_7383624 : CollatzResearch.WordTrace tailWord_7383624 prefixEnd_7383624 3791348084073124770843337 := by
  unfold tailWord_7383624
  simp only [CollatzResearch.WordTrace]
  refine ⟨134651445701199372714586963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179535260934932496952782617 134651445701199372714586963)
  ·
    refine ⟨201977168551799059071880445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134651445701199372714586963 201977168551799059071880445)
    ·
      refine ⟨75741438206924647151955167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201977168551799059071880445 75741438206924647151955167)
      ·
        refine ⟨113612157310386970727932751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75741438206924647151955167 113612157310386970727932751)
        ·
          refine ⟨170418235965580456091899127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113612157310386970727932751 170418235965580456091899127)
          ·
            refine ⟨255627353948370684137848691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170418235965580456091899127 255627353948370684137848691)
            ·
              refine ⟨383441030922556026206773037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255627353948370684137848691 383441030922556026206773037)
              ·
                refine ⟨143790386595958509827539889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383441030922556026206773037 143790386595958509827539889)
                ·
                  refine ⟨107842789946968882370654917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143790386595958509827539889 107842789946968882370654917)
                  ·
                    refine ⟨20220523115056665444497797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107842789946968882370654917 20220523115056665444497797)
                    ·
                      refine ⟨3791348084073124770843337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20220523115056665444497797 3791348084073124770843337)
                      ·
                        rfl

theorem cell23_7383624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_7383624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383624 prefixEnd_7383624 := by exact prefixLift 7383624
  have htrace : WordTrace (prefixWord ++ tailWord_7383624) baseStart_7383624 baseEnd_7383624 := by
    simpa [prefixWord, tailWord_7383624, baseEnd_7383624] using wordTrace_append hprefix tailTrace_7383624
  have hstable : (prefixWord ++ tailWord_7383624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383624).length < 2 ^ (prefixWord ++ tailWord_7383624).sum := by decide
  have hdescent : baseEnd_7383624 < baseStart_7383624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383631 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 3]
def baseStart_7383631 : Nat := 118140960795 + 7383631 * 2 ^ 59
def prefixEnd_7383631 : Nat := 4983230072969 + 3 ^ 40 * 7383631 * 2
def baseEnd_7383631 : Nat := 3791351678437706243455805

theorem tailTrace_7383631 : CollatzResearch.WordTrace tailWord_7383631 prefixEnd_7383631 3791351678437706243455805 := by
  unfold tailWord_7383631
  simp only [CollatzResearch.WordTrace]
  refine ⟨269303146713373385624678747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179535431142248923749785831 269303146713373385624678747)
  ·
    refine ⟨403954720070060078437018121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269303146713373385624678747 403954720070060078437018121)
    ·
      refine ⟨302966040052545058827763591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403954720070060078437018121 302966040052545058827763591)
      ·
        refine ⟨454449060078817588241645387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302966040052545058827763591 454449060078817588241645387)
        ·
          refine ⟨681673590118226382362468081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454449060078817588241645387 681673590118226382362468081)
          ·
            refine ⟨511255192588669786771851061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681673590118226382362468081 511255192588669786771851061)
            ·
              refine ⟨47930174305187792509861037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 511255192588669786771851061 47930174305187792509861037)
              ·
                refine ⟨17973815364445422191197889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47930174305187792509861037 17973815364445422191197889)
                ·
                  refine ⟨13480361523334066643398417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17973815364445422191197889 13480361523334066643398417)
                  ·
                    refine ⟨10110271142500549982548813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13480361523334066643398417 10110271142500549982548813)
                    ·
                      refine ⟨3791351678437706243455805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10110271142500549982548813 3791351678437706243455805)
                      ·
                        rfl

theorem cell23_7383631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 3].length) (baseStart_7383631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383631 prefixEnd_7383631 := by exact prefixLift 7383631
  have htrace : WordTrace (prefixWord ++ tailWord_7383631) baseStart_7383631 baseEnd_7383631 := by
    simpa [prefixWord, tailWord_7383631, baseEnd_7383631] using wordTrace_append hprefix tailTrace_7383631
  have hstable : (prefixWord ++ tailWord_7383631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383631).length < 2 ^ (prefixWord ++ tailWord_7383631).sum := by decide
  have hdescent : baseEnd_7383631 < baseStart_7383631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383646 : List Nat := [4, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_7383646 : Nat := 118140960795 + 7383646 * 2 ^ 59
def prefixEnd_7383646 : Nat := 4983230072969 + 3 ^ 40 * 7383646 * 2
def baseEnd_7383646 : Nat := 421262153405280409418693

theorem tailTrace_7383646 : CollatzResearch.WordTrace tailWord_7383646 prefixEnd_7383646 421262153405280409418693 := by
  unfold tailWord_7383646
  simp only [CollatzResearch.WordTrace]
  refine ⟨33662961726039880398309349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179535795872212695457649861 33662961726039880398309349)
  ·
    refine ⟨6311805323632477574683003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33662961726039880398309349 6311805323632477574683003)
    ·
      refine ⟨9467707985448716362024505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6311805323632477574683003 9467707985448716362024505)
      ·
        refine ⟨7100780989086537271518379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9467707985448716362024505 7100780989086537271518379)
        ·
          refine ⟨10651171483629805907277569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100780989086537271518379 10651171483629805907277569)
          ·
            refine ⟨7988378612722354430458177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10651171483629805907277569 7988378612722354430458177)
            ·
              refine ⟨5991283959541765822843633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7988378612722354430458177 5991283959541765822843633)
              ·
                refine ⟨4493462969656324367132725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5991283959541765822843633 4493462969656324367132725)
                ·
                  refine ⟨421262153405280409418693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4493462969656324367132725 421262153405280409418693)
                  ·
                    rfl

theorem cell23_7383646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_7383646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383646 prefixEnd_7383646 := by exact prefixLift 7383646
  have htrace : WordTrace (prefixWord ++ tailWord_7383646) baseStart_7383646 baseEnd_7383646 := by
    simpa [prefixWord, tailWord_7383646, baseEnd_7383646] using wordTrace_append hprefix tailTrace_7383646
  have hstable : (prefixWord ++ tailWord_7383646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383646).length < 2 ^ (prefixWord ++ tailWord_7383646).sum := by decide
  have hdescent : baseEnd_7383646 < baseStart_7383646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383651 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 6]
def baseStart_7383651 : Nat := 118140960795 + 7383651 * 2 ^ 59
def prefixEnd_7383651 : Nat := 4983230072969 + 3 ^ 40 * 7383651 * 2
def baseEnd_7383651 : Nat := 421262438672310685022857

theorem tailTrace_7383651 : CollatzResearch.WordTrace tailWord_7383651 prefixEnd_7383651 421262438672310685022857 := by
  unfold tailWord_7383651
  simp only [CollatzResearch.WordTrace]
  refine ⟨269303876173300929040406807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179535917448867286026937871 269303876173300929040406807)
  ·
    refine ⟨403955814259951393560610211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269303876173300929040406807 403955814259951393560610211)
    ·
      refine ⟨605933721389927090340915317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403955814259951393560610211 605933721389927090340915317)
      ·
        refine ⟨56806286380305664719460811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 605933721389927090340915317 56806286380305664719460811)
        ·
          refine ⟨85209429570458497079191217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56806286380305664719460811 85209429570458497079191217)
          ·
            refine ⟨63907072177843872809393413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85209429570458497079191217 63907072177843872809393413)
            ·
              refine ⟨11982576033345726151761265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63907072177843872809393413 11982576033345726151761265)
              ·
                refine ⟨8986932025009294613820949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11982576033345726151761265 8986932025009294613820949)
                ·
                  refine ⟨421262438672310685022857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8986932025009294613820949 421262438672310685022857)
                  ·
                    rfl

theorem cell23_7383651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 6].length) (baseStart_7383651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383651 prefixEnd_7383651 := by exact prefixLift 7383651
  have htrace : WordTrace (prefixWord ++ tailWord_7383651) baseStart_7383651 baseEnd_7383651 := by
    simpa [prefixWord, tailWord_7383651, baseEnd_7383651] using wordTrace_append hprefix tailTrace_7383651
  have hstable : (prefixWord ++ tailWord_7383651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383651).length < 2 ^ (prefixWord ++ tailWord_7383651).sum := by decide
  have hdescent : baseEnd_7383651 < baseStart_7383651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383674 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_7383674 : Nat := 118140960795 + 7383674 * 2 ^ 59
def prefixEnd_7383674 : Nat := 4983230072969 + 3 ^ 40 * 7383674 * 2
def baseEnd_7383674 : Nat := 3791373758105849575218107

theorem tailTrace_7383674 : CollatzResearch.WordTrace tailWord_7383674 prefixEnd_7383674 3791373758105849575218107 := by
  unfold tailWord_7383674
  simp only [CollatzResearch.WordTrace]
  refine ⟨67326178763054400992123519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179536476701478402645662717 67326178763054400992123519)
  ·
    refine ⟨100989268144581601488185279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67326178763054400992123519 100989268144581601488185279)
    ·
      refine ⟨151483902216872402232277919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100989268144581601488185279 151483902216872402232277919)
      ·
        refine ⟨227225853325308603348416879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151483902216872402232277919 227225853325308603348416879)
        ·
          refine ⟨340838779987962905022625319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227225853325308603348416879 340838779987962905022625319)
          ·
            refine ⟨511258169981944357533937979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340838779987962905022625319 511258169981944357533937979)
            ·
              refine ⟨766887254972916536300906969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511258169981944357533937979 766887254972916536300906969)
              ·
                refine ⟨575165441229687402225680227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766887254972916536300906969 575165441229687402225680227)
                ·
                  refine ⟨862748161844531103338520341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575165441229687402225680227 862748161844531103338520341)
                  ·
                    refine ⟨40441320086462395468993141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 862748161844531103338520341 40441320086462395468993141)
                    ·
                      refine ⟨3791373758105849575218107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40441320086462395468993141 3791373758105849575218107)
                      ·
                        rfl

theorem cell23_7383674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_7383674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383674 prefixEnd_7383674 := by exact prefixLift 7383674
  have htrace : WordTrace (prefixWord ++ tailWord_7383674) baseStart_7383674 baseEnd_7383674 := by
    simpa [prefixWord, tailWord_7383674, baseEnd_7383674] using wordTrace_append hprefix tailTrace_7383674
  have hstable : (prefixWord ++ tailWord_7383674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383674).length < 2 ^ (prefixWord ++ tailWord_7383674).sum := by decide
  have hdescent : baseEnd_7383674 < baseStart_7383674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383681 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 3, 5]
def baseStart_7383681 : Nat := 118140960795 + 7383681 * 2 ^ 59
def prefixEnd_7383681 : Nat := 4983230072969 + 3 ^ 40 * 7383681 * 2
def baseEnd_7383681 : Nat := 1263792450823477015943525

theorem tailTrace_7383681 : CollatzResearch.WordTrace tailWord_7383681 prefixEnd_7383681 1263792450823477015943525 := by
  unfold tailWord_7383681
  simp only [CollatzResearch.WordTrace]
  refine ⟨269304970363192244163998897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179536646908794829442665931 269304970363192244163998897)
  ·
    refine ⟨201978727772394183122999173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269304970363192244163998897 201978727772394183122999173)
    ·
      refine ⟨37871011457323909335562345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201978727772394183122999173 37871011457323909335562345)
      ·
        refine ⟨28403258592992932001671759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37871011457323909335562345 28403258592992932001671759)
        ·
          refine ⟨42604887889489398002507639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28403258592992932001671759 42604887889489398002507639)
          ·
            refine ⟨63907331834234097003761459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42604887889489398002507639 63907331834234097003761459)
            ·
              refine ⟨95860997751351145505642189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63907331834234097003761459 95860997751351145505642189)
              ·
                refine ⟨35947874156756679564615821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95860997751351145505642189 35947874156756679564615821)
                ·
                  refine ⟨13480452808783754836730933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35947874156756679564615821 13480452808783754836730933)
                  ·
                    refine ⟨1263792450823477015943525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13480452808783754836730933 1263792450823477015943525)
                    ·
                      rfl

theorem cell23_7383681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_7383681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383681 prefixEnd_7383681 := by exact prefixLift 7383681
  have htrace : WordTrace (prefixWord ++ tailWord_7383681) baseStart_7383681 baseEnd_7383681 := by
    simpa [prefixWord, tailWord_7383681, baseEnd_7383681] using wordTrace_append hprefix tailTrace_7383681
  have hstable : (prefixWord ++ tailWord_7383681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383681).length < 2 ^ (prefixWord ++ tailWord_7383681).sum := by decide
  have hdescent : baseEnd_7383681 < baseStart_7383681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383731 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 6]
def baseStart_7383731 : Nat := 118140960795 + 7383731 * 2 ^ 59
def prefixEnd_7383731 : Nat := 4983230072969 + 3 ^ 40 * 7383731 * 2
def baseEnd_7383731 : Nat := 3791403026503155852205345

theorem tailTrace_7383731 : CollatzResearch.WordTrace tailWord_7383731 prefixEnd_7383731 3791403026503155852205345 := by
  unfold tailWord_7383731
  simp only [CollatzResearch.WordTrace]
  refine ⟨269306794013011102703319047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179537862675340735135546031 269306794013011102703319047)
  ·
    refine ⟨403960191019516654054978571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269306794013011102703319047 403960191019516654054978571)
    ·
      refine ⟨605940286529274981082467857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403960191019516654054978571 605940286529274981082467857)
      ·
        refine ⟨454455214896956235811850893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605940286529274981082467857 454455214896956235811850893)
        ·
          refine ⟨170420705586358588429444085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454455214896956235811850893 170420705586358588429444085)
          ·
            refine ⟨15976941148721117665260383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170420705586358588429444085 15976941148721117665260383)
            ·
              refine ⟨23965411723081676497890575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15976941148721117665260383 23965411723081676497890575)
              ·
                refine ⟨35948117584622514746835863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23965411723081676497890575 35948117584622514746835863)
                ·
                  refine ⟨53922176376933772120253795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35948117584622514746835863 53922176376933772120253795)
                  ·
                    refine ⟨80883264565400658180380693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53922176376933772120253795 80883264565400658180380693)
                    ·
                      refine ⟨3791403026503155852205345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80883264565400658180380693 3791403026503155852205345)
                      ·
                        rfl

theorem cell23_7383731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_7383731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383731 prefixEnd_7383731 := by exact prefixLift 7383731
  have htrace : WordTrace (prefixWord ++ tailWord_7383731) baseStart_7383731 baseEnd_7383731 := by
    simpa [prefixWord, tailWord_7383731, baseEnd_7383731] using wordTrace_append hprefix tailTrace_7383731
  have hstable : (prefixWord ++ tailWord_7383731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383731).length < 2 ^ (prefixWord ++ tailWord_7383731).sum := by decide
  have hdescent : baseEnd_7383731 < baseStart_7383731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383735 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 4]
def baseStart_7383735 : Nat := 118140960795 + 7383735 * 2 ^ 59
def prefixEnd_7383735 : Nat := 4983230072969 + 3 ^ 40 * 7383735 * 2
def baseEnd_7383735 : Nat := 3791405080425773836555327

theorem tailTrace_7383735 : CollatzResearch.WordTrace tailWord_7383735 prefixEnd_7383735 3791405080425773836555327 := by
  unfold tailWord_7383735
  simp only [CollatzResearch.WordTrace]
  refine ⟨269306939904996611386464659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179537959936664407590976439 269306939904996611386464659)
  ·
    refine ⟨403960409857494917079696989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269306939904996611386464659 403960409857494917079696989)
    ·
      refine ⟨151485153696560593904886371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403960409857494917079696989 151485153696560593904886371)
      ·
        refine ⟨227227730544840890857329557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151485153696560593904886371 227227730544840890857329557)
        ·
          refine ⟨10651299869289416758937323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227227730544840890857329557 10651299869289416758937323)
          ·
            refine ⟨15976949803934125138405985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10651299869289416758937323 15976949803934125138405985)
            ·
              refine ⟨11982712352950593853804489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15976949803934125138405985 11982712352950593853804489)
              ·
                refine ⟨8987034264712945390353367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11982712352950593853804489 8987034264712945390353367)
                ·
                  refine ⟨13480551397069418085530051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8987034264712945390353367 13480551397069418085530051)
                  ·
                    refine ⟨20220827095604127128295077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13480551397069418085530051 20220827095604127128295077)
                    ·
                      refine ⟨3791405080425773836555327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20220827095604127128295077 3791405080425773836555327)
                      ·
                        rfl

theorem cell23_7383735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_7383735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383735 prefixEnd_7383735 := by exact prefixLift 7383735
  have htrace : WordTrace (prefixWord ++ tailWord_7383735) baseStart_7383735 baseEnd_7383735 := by
    simpa [prefixWord, tailWord_7383735, baseEnd_7383735] using wordTrace_append hprefix tailTrace_7383735
  have hstable : (prefixWord ++ tailWord_7383735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383735).length < 2 ^ (prefixWord ++ tailWord_7383735).sum := by decide
  have hdescent : baseEnd_7383735 < baseStart_7383735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383741 : List Nat := [1, 4, 1, 2, 1, 4, 1, 9]
def baseStart_7383741 : Nat := 118140960795 + 7383741 * 2 ^ 59
def prefixEnd_7383741 : Nat := 4983230072969 + 3 ^ 40 * 7383741 * 2
def baseEnd_7383741 : Nat := 140422524492951881965937

theorem tailTrace_7383741 : CollatzResearch.WordTrace tailWord_7383741 prefixEnd_7383741 140422524492951881965937 := by
  unfold tailWord_7383741
  simp only [CollatzResearch.WordTrace]
  refine ⟨269307158742974874411183077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179538105828649916274122051 269307158742974874411183077)
  ·
    refine ⟨50495092264307788952096827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269307158742974874411183077 50495092264307788952096827)
    ·
      refine ⟨75742638396461683428145241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50495092264307788952096827 75742638396461683428145241)
      ·
        refine ⟨56806978797346262571108931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75742638396461683428145241 56806978797346262571108931)
        ·
          refine ⟨85210468196019393856663397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56806978797346262571108931 85210468196019393856663397)
          ·
            refine ⟨15976962786753636348124387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85210468196019393856663397 15976962786753636348124387)
            ·
              refine ⟨23965444180130454522186581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15976962786753636348124387 23965444180130454522186581)
              ·
                refine ⟨140422524492951881965937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23965444180130454522186581 140422524492951881965937)
                ·
                  rfl

theorem cell23_7383741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 9].length) (baseStart_7383741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383741 prefixEnd_7383741 := by exact prefixLift 7383741
  have htrace : WordTrace (prefixWord ++ tailWord_7383741) baseStart_7383741 baseEnd_7383741 := by
    simpa [prefixWord, tailWord_7383741, baseEnd_7383741] using wordTrace_append hprefix tailTrace_7383741
  have hstable : (prefixWord ++ tailWord_7383741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383741).length < 2 ^ (prefixWord ++ tailWord_7383741).sum := by decide
  have hdescent : baseEnd_7383741 < baseStart_7383741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383769 : List Nat := [1, 2, 1, 2, 3, 2, 5, 2, 1, 2, 2]
def baseStart_7383769 : Nat := 118140960795 + 7383769 * 2 ^ 59
def prefixEnd_7383769 : Nat := 4983230072969 + 3 ^ 40 * 7383769 * 2
def baseEnd_7383769 : Nat := 3791422538768026703530171

theorem tailTrace_7383769 : CollatzResearch.WordTrace tailWord_7383769 prefixEnd_7383769 3791422538768026703530171 := by
  unfold tailWord_7383769
  simp only [CollatzResearch.WordTrace]
  refine ⟨269308179986873435193202361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179538786657915623462134907 269308179986873435193202361)
  ·
    refine ⟨201981134990155076394901771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269308179986873435193202361 201981134990155076394901771)
    ·
      refine ⟨302971702485232614592352657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201981134990155076394901771 302971702485232614592352657)
      ·
        refine ⟨227228776863924460944264493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302971702485232614592352657 227228776863924460944264493)
        ·
          refine ⟨85210791323971672854099185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227228776863924460944264493 85210791323971672854099185)
          ·
            refine ⟨63908093492978754640574389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85210791323971672854099185 63908093492978754640574389)
            ·
              refine ⟨5991383764966758247553849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63908093492978754640574389 5991383764966758247553849)
              ·
                refine ⟨4493537823725068685665387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5991383764966758247553849 4493537823725068685665387)
                ·
                  refine ⟨6740306735587603028498081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493537823725068685665387 6740306735587603028498081)
                  ·
                    refine ⟨5055230051690702271373561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6740306735587603028498081 5055230051690702271373561)
                    ·
                      refine ⟨3791422538768026703530171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055230051690702271373561 3791422538768026703530171)
                      ·
                        rfl

theorem cell23_7383769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 1, 2, 2].length) (baseStart_7383769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383769 prefixEnd_7383769 := by exact prefixLift 7383769
  have htrace : WordTrace (prefixWord ++ tailWord_7383769) baseStart_7383769 baseEnd_7383769 := by
    simpa [prefixWord, tailWord_7383769, baseEnd_7383769] using wordTrace_append hprefix tailTrace_7383769
  have hstable : (prefixWord ++ tailWord_7383769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383769).length < 2 ^ (prefixWord ++ tailWord_7383769).sum := by decide
  have hdescent : baseEnd_7383769 < baseStart_7383769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383825 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 4, 2, 2]
def baseStart_7383825 : Nat := 118140960795 + 7383825 * 2 ^ 59
def prefixEnd_7383825 : Nat := 4983230072969 + 3 ^ 40 * 7383825 * 2
def baseEnd_7383825 : Nat := 3791451293684678484429913

theorem tailTrace_7383825 : CollatzResearch.WordTrace tailWord_7383825 prefixEnd_7383825 3791451293684678484429913 := by
  unfold tailWord_7383825
  simp only [CollatzResearch.WordTrace]
  refine ⟨269310222474670556757240929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179540148316447037838160619 269310222474670556757240929)
  ·
    refine ⟨201982666856002917567930697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269310222474670556757240929 201982666856002917567930697)
    ·
      refine ⟨151487000142002188175948023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201982666856002917567930697 151487000142002188175948023)
      ·
        refine ⟨227230500213003282263922035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151487000142002188175948023 227230500213003282263922035)
        ·
          refine ⟨340845750319504923395883053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227230500213003282263922035 340845750319504923395883053)
          ·
            refine ⟨127817156369814346273456145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340845750319504923395883053 127817156369814346273456145)
            ·
              refine ⟨95862867277360759705092109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127817156369814346273456145 95862867277360759705092109)
              ·
                refine ⟨35948575229010284889409541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95862867277360759705092109 35948575229010284889409541)
                ·
                  refine ⟨6740357855439428416764289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35948575229010284889409541 6740357855439428416764289)
                  ·
                    refine ⟨5055268391579571312573217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6740357855439428416764289 5055268391579571312573217)
                    ·
                      refine ⟨3791451293684678484429913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055268391579571312573217 3791451293684678484429913)
                      ·
                        rfl

theorem cell23_7383825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_7383825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383825 prefixEnd_7383825 := by exact prefixLift 7383825
  have htrace : WordTrace (prefixWord ++ tailWord_7383825) baseStart_7383825 baseEnd_7383825 := by
    simpa [prefixWord, tailWord_7383825, baseEnd_7383825] using wordTrace_append hprefix tailTrace_7383825
  have hstable : (prefixWord ++ tailWord_7383825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383825).length < 2 ^ (prefixWord ++ tailWord_7383825).sum := by decide
  have hdescent : baseEnd_7383825 < baseStart_7383825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383842 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_7383842 : Nat := 118140960795 + 7383842 * 2 ^ 59
def prefixEnd_7383842 : Nat := 4983230072969 + 3 ^ 40 * 7383842 * 2
def baseEnd_7383842 : Nat := 3791460022855804917917335

theorem tailTrace_7383842 : CollatzResearch.WordTrace tailWord_7383842 prefixEnd_7383842 3791460022855804917917335 := by
  unfold tailWord_7383842
  simp only [CollatzResearch.WordTrace]
  refine ⟨67327710628902242165152445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179540561677072645773739853 67327710628902242165152445)
  ·
    refine ⟨25247891485838340811932167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67327710628902242165152445 25247891485838340811932167)
    ·
      refine ⟨37871837228757511217898251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25247891485838340811932167 37871837228757511217898251)
      ·
        refine ⟨56807755843136266826847377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37871837228757511217898251 56807755843136266826847377)
        ·
          refine ⟨42605816882352200120135533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56807755843136266826847377 42605816882352200120135533)
          ·
            refine ⟨15977181330882075045050825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42605816882352200120135533 15977181330882075045050825)
            ·
              refine ⟨11982885998161556283788119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15977181330882075045050825 11982885998161556283788119)
              ·
                refine ⟨17974328997242334425682179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11982885998161556283788119 17974328997242334425682179)
                ·
                  refine ⟨26961493495863501638523269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17974328997242334425682179 26961493495863501638523269)
                  ·
                    refine ⟨5055280030474406557223113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26961493495863501638523269 5055280030474406557223113)
                    ·
                      refine ⟨3791460022855804917917335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055280030474406557223113 3791460022855804917917335)
                      ·
                        rfl

theorem cell23_7383842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_7383842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383842 prefixEnd_7383842 := by exact prefixLift 7383842
  have htrace : WordTrace (prefixWord ++ tailWord_7383842) baseStart_7383842 baseEnd_7383842 := by
    simpa [prefixWord, tailWord_7383842, baseEnd_7383842] using wordTrace_append hprefix tailTrace_7383842
  have hstable : (prefixWord ++ tailWord_7383842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383842).length < 2 ^ (prefixWord ++ tailWord_7383842).sum := by decide
  have hdescent : baseEnd_7383842 < baseStart_7383842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383848 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 7]
def baseStart_7383848 : Nat := 118140960795 + 7383848 * 2 ^ 59
def prefixEnd_7383848 : Nat := 4983230072969 + 3 ^ 40 * 7383848 * 2
def baseEnd_7383848 : Nat := 421273678193303543826923

theorem tailTrace_7383848 : CollatzResearch.WordTrace tailWord_7383848 prefixEnd_7383848 421273678193303543826923 := by
  unfold tailWord_7383848
  simp only [CollatzResearch.WordTrace]
  refine ⟨134655530676793615842664099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179540707569058154456885465 134655530676793615842664099)
  ·
    refine ⟨201983296015190423763996149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134655530676793615842664099 201983296015190423763996149)
    ·
      refine ⟨18935934001424102227874639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201983296015190423763996149 18935934001424102227874639)
      ·
        refine ⟨28403901002136153341811959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18935934001424102227874639 28403901002136153341811959)
        ·
          refine ⟨42605851503204230012717939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28403901002136153341811959 42605851503204230012717939)
          ·
            refine ⟨63908777254806345019076909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42605851503204230012717939 63908777254806345019076909)
            ·
              refine ⟨23965791470552379382153841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63908777254806345019076909 23965791470552379382153841)
              ·
                refine ⟨17974343602914284536615381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23965791470552379382153841 17974343602914284536615381)
                ·
                  refine ⟨421273678193303543826923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17974343602914284536615381 421273678193303543826923)
                  ·
                    rfl

theorem cell23_7383848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 7].length) (baseStart_7383848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383848 prefixEnd_7383848 := by exact prefixLift 7383848
  have htrace : WordTrace (prefixWord ++ tailWord_7383848) baseStart_7383848 baseEnd_7383848 := by
    simpa [prefixWord, tailWord_7383848, baseEnd_7383848] using wordTrace_append hprefix tailTrace_7383848
  have hstable : (prefixWord ++ tailWord_7383848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383848).length < 2 ^ (prefixWord ++ tailWord_7383848).sum := by decide
  have hdescent : baseEnd_7383848 < baseStart_7383848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383858 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_7383858 : Nat := 118140960795 + 7383858 * 2 ^ 59
def prefixEnd_7383858 : Nat := 4983230072969 + 3 ^ 40 * 7383858 * 2
def baseEnd_7383858 : Nat := 3791468238546276855317261

theorem tailTrace_7383858 : CollatzResearch.WordTrace tailWord_7383858 prefixEnd_7383858 3791468238546276855317261 := by
  unfold tailWord_7383858
  simp only [CollatzResearch.WordTrace]
  refine ⟨67327856520887750848298057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179540950722367335595461485 67327856520887750848298057)
  ·
    refine ⟨50495892390665813136223543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67327856520887750848298057 50495892390665813136223543)
    ·
      refine ⟨75743838585998719704335315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50495892390665813136223543 75743838585998719704335315)
      ·
        refine ⟨113615757878998079556502973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75743838585998719704335315 113615757878998079556502973)
        ·
          refine ⟨42605909204624279833688615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113615757878998079556502973 42605909204624279833688615)
          ·
            refine ⟨63908863806936419750532923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42605909204624279833688615 63908863806936419750532923)
            ·
              refine ⟨95863295710404629625799385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63908863806936419750532923 95863295710404629625799385)
              ·
                refine ⟨71897471782803472219349539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95863295710404629625799385 71897471782803472219349539)
                ·
                  refine ⟨107846207674205208329024309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71897471782803472219349539 107846207674205208329024309)
                  ·
                    refine ⟨10110581969456738280846029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107846207674205208329024309 10110581969456738280846029)
                    ·
                      refine ⟨3791468238546276855317261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10110581969456738280846029 3791468238546276855317261)
                      ·
                        rfl

theorem cell23_7383858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_7383858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383858 prefixEnd_7383858 := by exact prefixLift 7383858
  have htrace : WordTrace (prefixWord ++ tailWord_7383858) baseStart_7383858 baseEnd_7383858 := by
    simpa [prefixWord, tailWord_7383858, baseEnd_7383858] using wordTrace_append hprefix tailTrace_7383858
  have hstable : (prefixWord ++ tailWord_7383858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383858).length < 2 ^ (prefixWord ++ tailWord_7383858).sum := by decide
  have hdescent : baseEnd_7383858 < baseStart_7383858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383876 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7383876 : Nat := 118140960795 + 7383876 * 2 ^ 59
def prefixEnd_7383876 : Nat := 4983230072969 + 3 ^ 40 * 7383876 * 2
def baseEnd_7383876 : Nat := 3791477481198057784892179

theorem tailTrace_7383876 : CollatzResearch.WordTrace tailWord_7383876 prefixEnd_7383876 3791477481198057784892179 := by
  unfold tailWord_7383876
  simp only [CollatzResearch.WordTrace]
  refine ⟨134656041298742896233673741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179541388398323861644898321 134656041298742896233673741)
  ·
    refine ⟨50496015487028586087627653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134656041298742896233673741 50496015487028586087627653)
    ·
      refine ⟨9468002903817859891430185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50496015487028586087627653 9468002903817859891430185)
      ·
        refine ⟨7101002177863394918572639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9468002903817859891430185 7101002177863394918572639)
        ·
          refine ⟨10651503266795092377858959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101002177863394918572639 10651503266795092377858959)
          ·
            refine ⟨15977254900192638566788439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10651503266795092377858959 15977254900192638566788439)
            ·
              refine ⟨23965882350288957850182659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15977254900192638566788439 23965882350288957850182659)
              ·
                refine ⟨35948823525433436775273989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23965882350288957850182659 35948823525433436775273989)
                ·
                  refine ⟨6740404411018769395363873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35948823525433436775273989 6740404411018769395363873)
                  ·
                    refine ⟨5055303308264077046522905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6740404411018769395363873 5055303308264077046522905)
                    ·
                      refine ⟨3791477481198057784892179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055303308264077046522905 3791477481198057784892179)
                      ·
                        rfl

theorem cell23_7383876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7383876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383876 prefixEnd_7383876 := by exact prefixLift 7383876
  have htrace : WordTrace (prefixWord ++ tailWord_7383876) baseStart_7383876 baseEnd_7383876 := by
    simpa [prefixWord, tailWord_7383876, baseEnd_7383876] using wordTrace_append hprefix tailTrace_7383876
  have hstable : (prefixWord ++ tailWord_7383876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383876).length < 2 ^ (prefixWord ++ tailWord_7383876).sum := by decide
  have hdescent : baseEnd_7383876 < baseStart_7383876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383898 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_7383898 : Nat := 118140960795 + 7383898 * 2 ^ 59
def prefixEnd_7383898 : Nat := 4983230072969 + 3 ^ 40 * 7383898 * 2
def baseEnd_7383898 : Nat := 3791488777772456698817077

theorem tailTrace_7383898 : CollatzResearch.WordTrace tailWord_7383898 prefixEnd_7383898 3791488777772456698817077 := by
  unfold tailWord_7383898
  simp only [CollatzResearch.WordTrace]
  refine ⟨67328221250851522556162087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179541923335604060149765565 67328221250851522556162087)
  ·
    refine ⟨100992331876277283834243131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67328221250851522556162087 100992331876277283834243131)
    ·
      refine ⟨151488497814415925751364697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100992331876277283834243131 151488497814415925751364697)
      ·
        refine ⟨113616373360811944313523523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151488497814415925751364697 113616373360811944313523523)
        ·
          refine ⟨170424560041217916470285285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113616373360811944313523523 170424560041217916470285285)
          ·
            refine ⟨31954605007728359338178491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170424560041217916470285285 31954605007728359338178491)
            ·
              refine ⟨47931907511592539007267737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31954605007728359338178491 47931907511592539007267737)
              ·
                refine ⟨35948930633694404255450803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47931907511592539007267737 35948930633694404255450803)
                ·
                  refine ⟨53923395950541606383176205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35948930633694404255450803 53923395950541606383176205)
                  ·
                    refine ⟨20221273481453102393691077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53923395950541606383176205 20221273481453102393691077)
                    ·
                      refine ⟨3791488777772456698817077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20221273481453102393691077 3791488777772456698817077)
                      ·
                        rfl

theorem cell23_7383898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_7383898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383898 prefixEnd_7383898 := by exact prefixLift 7383898
  have htrace : WordTrace (prefixWord ++ tailWord_7383898) baseStart_7383898 baseEnd_7383898 := by
    simpa [prefixWord, tailWord_7383898, baseEnd_7383898] using wordTrace_append hprefix tailTrace_7383898
  have hstable : (prefixWord ++ tailWord_7383898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383898).length < 2 ^ (prefixWord ++ tailWord_7383898).sum := by decide
  have hdescent : baseEnd_7383898 < baseStart_7383898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7383992 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 2, 3, 2]
def baseStart_7383992 : Nat := 118140960795 + 7383992 * 2 ^ 59
def prefixEnd_7383992 : Nat := 4983230072969 + 3 ^ 40 * 7383992 * 2
def baseEnd_7383992 : Nat := 3791537044953979331041645

theorem tailTrace_7383992 : CollatzResearch.WordTrace tailWord_7383992 prefixEnd_7383992 3791537044953979331041645 := by
  unfold tailWord_7383992
  simp only [CollatzResearch.WordTrace]
  refine ⟨134658156732532772139285115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179544208976710362852380153 134658156732532772139285115)
  ·
    refine ⟨201987235098799158208927673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134658156732532772139285115 201987235098799158208927673)
    ·
      refine ⟨151490426324099368656695755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201987235098799158208927673 151490426324099368656695755)
      ·
        refine ⟨227235639486149052985043633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151490426324099368656695755 227235639486149052985043633)
        ·
          refine ⟨170426729614611789738782725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227235639486149052985043633 170426729614611789738782725)
          ·
            refine ⟨31955011802739710576021761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170426729614611789738782725 31955011802739710576021761)
            ·
              refine ⟨23966258852054782932016321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31955011802739710576021761 23966258852054782932016321)
              ·
                refine ⟨17974694139041087199012241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23966258852054782932016321 17974694139041087199012241)
                ·
                  refine ⟨13481020604280815399259181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17974694139041087199012241 13481020604280815399259181)
                  ·
                    refine ⟨5055382726605305774722193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13481020604280815399259181 5055382726605305774722193)
                    ·
                      refine ⟨3791537044953979331041645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055382726605305774722193 3791537044953979331041645)
                      ·
                        rfl

theorem cell23_7383992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_7383992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7383992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7383992 prefixEnd_7383992 := by exact prefixLift 7383992
  have htrace : WordTrace (prefixWord ++ tailWord_7383992) baseStart_7383992 baseEnd_7383992 := by
    simpa [prefixWord, tailWord_7383992, baseEnd_7383992] using wordTrace_append hprefix tailTrace_7383992
  have hstable : (prefixWord ++ tailWord_7383992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7383992).length < 2 ^ (prefixWord ++ tailWord_7383992).sum := by decide
  have hdescent : baseEnd_7383992 < baseStart_7383992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7383992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384015 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 1, 6]
def baseStart_7384015 : Nat := 118140960795 + 7384015 * 2 ^ 59
def prefixEnd_7384015 : Nat := 4983230072969 + 3 ^ 40 * 7384015 * 2
def baseEnd_7384015 : Nat := 1263849618336344247018013

theorem tailTrace_7384015 : CollatzResearch.WordTrace tailWord_7384015 prefixEnd_7384015 1263849618336344247018013 := by
  unfold tailWord_7384015
  simp only [CollatzResearch.WordTrace]
  refine ⟨269317152343982219206657499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179544768229321479471104999 269317152343982219206657499)
  ·
    refine ⟨403975728515973328809986249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269317152343982219206657499 403975728515973328809986249)
    ·
      refine ⟨302981796386979996607489687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403975728515973328809986249 302981796386979996607489687)
      ·
        refine ⟨454472694580469994911234531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302981796386979996607489687 454472694580469994911234531)
        ·
          refine ⟨681709041870704992366851797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454472694580469994911234531 681709041870704992366851797)
          ·
            refine ⟨15977555668844648258598089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 681709041870704992366851797 15977555668844648258598089)
            ·
              refine ⟨11983166751633486193948567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15977555668844648258598089 11983166751633486193948567)
              ·
                refine ⟨17974750127450229290922851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11983166751633486193948567 17974750127450229290922851)
                ·
                  refine ⟨26962125191175343936384277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17974750127450229290922851 26962125191175343936384277)
                  ·
                    refine ⟨1263849618336344247018013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26962125191175343936384277 1263849618336344247018013)
                    ·
                      rfl

theorem cell23_7384015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 6].length) (baseStart_7384015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384015 prefixEnd_7384015 := by exact prefixLift 7384015
  have htrace : WordTrace (prefixWord ++ tailWord_7384015) baseStart_7384015 baseEnd_7384015 := by
    simpa [prefixWord, tailWord_7384015, baseEnd_7384015] using wordTrace_append hprefix tailTrace_7384015
  have hstable : (prefixWord ++ tailWord_7384015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384015).length < 2 ^ (prefixWord ++ tailWord_7384015).sum := by decide
  have hdescent : baseEnd_7384015 < baseStart_7384015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384035 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 4]
def baseStart_7384035 : Nat := 118140960795 + 7384035 * 2 ^ 59
def prefixEnd_7384035 : Nat := 4983230072969 + 3 ^ 40 * 7384035 * 2
def baseEnd_7384035 : Nat := 3791559124622122662803947

theorem tailTrace_7384035 : CollatzResearch.WordTrace tailWord_7384035 prefixEnd_7384035 3791559124622122662803947 := by
  unfold tailWord_7384035
  simp only [CollatzResearch.WordTrace]
  refine ⟨269317881803909762622385559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179545254535939841748257039 269317881803909762622385559)
  ·
    refine ⟨403976822705864643933578339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269317881803909762622385559 403976822705864643933578339)
    ·
      refine ⟨605965234058796965900367509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403976822705864643933578339 605965234058796965900367509)
      ·
        refine ⟨28404620346506107776579727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 605965234058796965900367509 28404620346506107776579727)
        ·
          refine ⟨42606930519759161664869591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28404620346506107776579727 42606930519759161664869591)
          ·
            refine ⟨63910395779638742497304387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42606930519759161664869591 63910395779638742497304387)
            ·
              refine ⟨95865593669458113745956581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63910395779638742497304387 95865593669458113745956581)
              ·
                refine ⟨17974798813023396327366859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95865593669458113745956581 17974798813023396327366859)
                ·
                  refine ⟨26962198219535094491050289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17974798813023396327366859 26962198219535094491050289)
                  ·
                    refine ⟨20221648664651320868287717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26962198219535094491050289 20221648664651320868287717)
                    ·
                      refine ⟨3791559124622122662803947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20221648664651320868287717 3791559124622122662803947)
                      ·
                        rfl

theorem cell23_7384035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_7384035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384035 prefixEnd_7384035 := by exact prefixLift 7384035
  have htrace : WordTrace (prefixWord ++ tailWord_7384035) baseStart_7384035 baseEnd_7384035 := by
    simpa [prefixWord, tailWord_7384035, baseEnd_7384035] using wordTrace_append hprefix tailTrace_7384035
  have hstable : (prefixWord ++ tailWord_7384035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384035).length < 2 ^ (prefixWord ++ tailWord_7384035).sum := by decide
  have hdescent : baseEnd_7384035 < baseStart_7384035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384039 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_7384039 : Nat := 118140960795 + 7384039 * 2 ^ 59
def prefixEnd_7384039 : Nat := 4983230072969 + 3 ^ 40 * 7384039 * 2
def baseEnd_7384039 : Nat := 3791561178544740647153929

theorem tailTrace_7384039 : CollatzResearch.WordTrace tailWord_7384039 prefixEnd_7384039 3791561178544740647153929 := by
  unfold tailWord_7384039
  simp only [CollatzResearch.WordTrace]
  refine ⟨269318027695895271305531171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179545351797263514203687447 269318027695895271305531171)
  ·
    refine ⟨403977041543842906958296757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269318027695895271305531171 403977041543842906958296757)
    ·
      refine ⟨37872847644735272527340321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 403977041543842906958296757 37872847644735272527340321)
      ·
        refine ⟨28404635733551454395505241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37872847644735272527340321 28404635733551454395505241)
        ·
          refine ⟨21303476800163590796628931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28404635733551454395505241 21303476800163590796628931)
          ·
            refine ⟨31955215200245386194943397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21303476800163590796628931 31955215200245386194943397)
            ·
              refine ⟨5991602850046009911551887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31955215200245386194943397 5991602850046009911551887)
              ·
                refine ⟨8987404275069014867327831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991602850046009911551887 8987404275069014867327831)
                ·
                  refine ⟨13481106412603522300991747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8987404275069014867327831 13481106412603522300991747)
                  ·
                    refine ⟨20221659618905283451487621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13481106412603522300991747 20221659618905283451487621)
                    ·
                      refine ⟨3791561178544740647153929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20221659618905283451487621 3791561178544740647153929)
                      ·
                        rfl

theorem cell23_7384039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_7384039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384039 prefixEnd_7384039 := by exact prefixLift 7384039
  have htrace : WordTrace (prefixWord ++ tailWord_7384039) baseStart_7384039 baseEnd_7384039 := by
    simpa [prefixWord, tailWord_7384039, baseEnd_7384039] using wordTrace_append hprefix tailTrace_7384039
  have hstable : (prefixWord ++ tailWord_7384039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384039).length < 2 ^ (prefixWord ++ tailWord_7384039).sum := by decide
  have hdescent : baseEnd_7384039 < baseStart_7384039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384048 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_7384048 : Nat := 118140960795 + 7384048 * 2 ^ 59
def prefixEnd_7384048 : Nat := 4983230072969 + 3 ^ 40 * 7384048 * 2
def baseEnd_7384048 : Nat := 3791565799870631111941387

theorem tailTrace_7384048 : CollatzResearch.WordTrace tailWord_7384048 prefixEnd_7384048 3791565799870631111941387 := by
  unfold tailWord_7384048
  simp only [CollatzResearch.WordTrace]
  refine ⟨134659177976431332921304399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179545570635241777228405865 134659177976431332921304399)
  ·
    refine ⟨201988766964646999381956599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134659177976431332921304399 201988766964646999381956599)
    ·
      refine ⟨302983150446970499072934899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201988766964646999381956599 302983150446970499072934899)
      ·
        refine ⟨454474725670455748609402349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302983150446970499072934899 454474725670455748609402349)
        ·
          refine ⟨170428022126420905728525881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454474725670455748609402349 170428022126420905728525881)
          ·
            refine ⟨127821016594815679296394411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170428022126420905728525881 127821016594815679296394411)
            ·
              refine ⟨191731524892223518944591617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127821016594815679296394411 191731524892223518944591617)
              ·
                refine ⟨143798643669167639208443713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191731524892223518944591617 143798643669167639208443713)
                ·
                  refine ⟨107848982751875729406332785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143798643669167639208443713 107848982751875729406332785)
                  ·
                    refine ⟨80886737063906797054749589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107848982751875729406332785 80886737063906797054749589)
                    ·
                      refine ⟨3791565799870631111941387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80886737063906797054749589 3791565799870631111941387)
                      ·
                        rfl

theorem cell23_7384048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_7384048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384048 prefixEnd_7384048 := by exact prefixLift 7384048
  have htrace : WordTrace (prefixWord ++ tailWord_7384048) baseStart_7384048 baseEnd_7384048 := by
    simpa [prefixWord, tailWord_7384048, baseEnd_7384048] using wordTrace_append hprefix tailTrace_7384048
  have hstable : (prefixWord ++ tailWord_7384048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384048).length < 2 ^ (prefixWord ++ tailWord_7384048).sum := by decide
  have hdescent : baseEnd_7384048 < baseStart_7384048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384049 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 2, 4]
def baseStart_7384049 : Nat := 118140960795 + 7384049 * 2 ^ 59
def prefixEnd_7384049 : Nat := 4983230072969 + 3 ^ 40 * 7384049 * 2
def baseEnd_7384049 : Nat := 1263855437783761869342961

theorem tailTrace_7384049 : CollatzResearch.WordTrace tailWord_7384049 prefixEnd_7384049 1263855437783761869342961 := by
  unfold tailWord_7384049
  simp only [CollatzResearch.WordTrace]
  refine ⟨269318392425859043013395201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179545594950572695342263467 269318392425859043013395201)
  ·
    refine ⟨201988794319394282260046401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269318392425859043013395201 201988794319394282260046401)
    ·
      refine ⟨151491595739545711695034801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201988794319394282260046401 151491595739545711695034801)
      ·
        refine ⟨113618696804659283771276101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151491595739545711695034801 113618696804659283771276101)
        ·
          refine ⟨21303505650873615707114269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113618696804659283771276101 21303505650873615707114269)
          ·
            refine ⟨7988814619077605890167851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21303505650873615707114269 7988814619077605890167851)
            ·
              refine ⟨11983221928616408835251777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7988814619077605890167851 11983221928616408835251777)
              ·
                refine ⟨8987416446462306626438833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11983221928616408835251777 8987416446462306626438833)
                ·
                  refine ⟨6740562334846729969829125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8987416446462306626438833 6740562334846729969829125)
                  ·
                    refine ⟨1263855437783761869342961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6740562334846729969829125 1263855437783761869342961)
                    ·
                      rfl

theorem cell23_7384049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_7384049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384049 prefixEnd_7384049 := by exact prefixLift 7384049
  have htrace : WordTrace (prefixWord ++ tailWord_7384049) baseStart_7384049 baseEnd_7384049 := by
    simpa [prefixWord, tailWord_7384049, baseEnd_7384049] using wordTrace_append hprefix tailTrace_7384049
  have hstable : (prefixWord ++ tailWord_7384049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384049).length < 2 ^ (prefixWord ++ tailWord_7384049).sum := by decide
  have hdescent : baseEnd_7384049 < baseStart_7384049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384058 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_7384058 : Nat := 118140960795 + 7384058 * 2 ^ 59
def prefixEnd_7384058 : Nat := 4983230072969 + 3 ^ 40 * 7384058 * 2
def baseEnd_7384058 : Nat := 1263856978225725357605447

theorem tailTrace_7384058 : CollatzResearch.WordTrace tailWord_7384058 prefixEnd_7384058 1263856978225725357605447 := by
  unfold tailWord_7384058
  simp only [CollatzResearch.WordTrace]
  refine ⟨67329680170706609387618207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179545813788550958366981885 67329680170706609387618207)
  ·
    refine ⟨100994520256059914081427311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67329680170706609387618207 100994520256059914081427311)
    ·
      refine ⟨151491780384089871122140967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100994520256059914081427311 151491780384089871122140967)
      ·
        refine ⟨227237670576134806683211451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151491780384089871122140967 227237670576134806683211451)
        ·
          refine ⟨340856505864202210024817177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227237670576134806683211451 340856505864202210024817177)
          ·
            refine ⟨255642379398151657518612883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340856505864202210024817177 255642379398151657518612883)
            ·
              refine ⟨383463569097227486277919325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255642379398151657518612883 383463569097227486277919325)
              ·
                refine ⟨143798838411460307354219747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383463569097227486277919325 143798838411460307354219747)
                ·
                  refine ⟨215698257617190461031329621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143798838411460307354219747 215698257617190461031329621)
                  ·
                    refine ⟨1263856978225725357605447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 215698257617190461031329621 1263856978225725357605447)
                    ·
                      rfl

theorem cell23_7384058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_7384058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384058 prefixEnd_7384058 := by exact prefixLift 7384058
  have htrace : WordTrace (prefixWord ++ tailWord_7384058) baseStart_7384058 baseEnd_7384058 := by
    simpa [prefixWord, tailWord_7384058, baseEnd_7384058] using wordTrace_append hprefix tailTrace_7384058
  have hstable : (prefixWord ++ tailWord_7384058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384058).length < 2 ^ (prefixWord ++ tailWord_7384058).sum := by decide
  have hdescent : baseEnd_7384058 < baseStart_7384058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384066 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_7384066 : Nat := 118140960795 + 7384066 * 2 ^ 59
def prefixEnd_7384066 : Nat := 4983230072969 + 3 ^ 40 * 7384066 * 2
def baseEnd_7384066 : Nat := 1263858347507470680505435

theorem tailTrace_7384066 : CollatzResearch.WordTrace tailWord_7384066 prefixEnd_7384066 1263858347507470680505435 := by
  unfold tailWord_7384066
  simp only [CollatzResearch.WordTrace]
  refine ⟨67329753116699363729191013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179546008311198303277842701 67329753116699363729191013)
  ·
    refine ⟨12624328709381130699223315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67329753116699363729191013 12624328709381130699223315)
    ·
      refine ⟨18936493064071696048834973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12624328709381130699223315 18936493064071696048834973)
      ·
        refine ⟨7101184899026886018313115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18936493064071696048834973 7101184899026886018313115)
        ·
          refine ⟨10651777348540329027469673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101184899026886018313115 10651777348540329027469673)
          ·
            refine ⟨7988833011405246770602255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10651777348540329027469673 7988833011405246770602255)
            ·
              refine ⟨11983249517107870155903383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7988833011405246770602255 11983249517107870155903383)
              ·
                refine ⟨17974874275661805233855075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11983249517107870155903383 17974874275661805233855075)
                ·
                  refine ⟨26962311413492707850782613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17974874275661805233855075 26962311413492707850782613)
                  ·
                    refine ⟨1263858347507470680505435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26962311413492707850782613 1263858347507470680505435)
                    ·
                      rfl

theorem cell23_7384066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_7384066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384066 prefixEnd_7384066 := by exact prefixLift 7384066
  have htrace : WordTrace (prefixWord ++ tailWord_7384066) baseStart_7384066 baseEnd_7384066 := by
    simpa [prefixWord, tailWord_7384066, baseEnd_7384066] using wordTrace_append hprefix tailTrace_7384066
  have hstable : (prefixWord ++ tailWord_7384066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384066).length < 2 ^ (prefixWord ++ tailWord_7384066).sum := by decide
  have hdescent : baseEnd_7384066 < baseStart_7384066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384072 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_7384072 : Nat := 118140960795 + 7384072 * 2 ^ 59
def prefixEnd_7384072 : Nat := 4983230072969 + 3 ^ 40 * 7384072 * 2
def baseEnd_7384072 : Nat := 3791578123406339018041277

theorem tailTrace_7384072 : CollatzResearch.WordTrace tailWord_7384072 prefixEnd_7384072 3791578123406339018041277 := by
  unfold tailWord_7384072
  simp only [CollatzResearch.WordTrace]
  refine ⟨134659615652387858970741235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179546154203183811960988313 134659615652387858970741235)
  ·
    refine ⟨201989423478581788456111853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134659615652387858970741235 201989423478581788456111853)
    ·
      refine ⟨75746033804468170671041945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201989423478581788456111853 75746033804468170671041945)
      ·
        refine ⟨56809525353351128003281459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75746033804468170671041945 56809525353351128003281459)
        ·
          refine ⟨85214288030026692004922189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56809525353351128003281459 85214288030026692004922189)
          ·
            refine ⟨31955358011260009501845821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85214288030026692004922189 31955358011260009501845821)
            ·
              refine ⟨11983259254222503563192183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31955358011260009501845821 11983259254222503563192183)
              ·
                refine ⟨17974888881333755344788275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11983259254222503563192183 17974888881333755344788275)
                ·
                  refine ⟨26962333322000633017182413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17974888881333755344788275 26962333322000633017182413)
                  ·
                    refine ⟨10110874995750237381443405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26962333322000633017182413 10110874995750237381443405)
                    ·
                      refine ⟨3791578123406339018041277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10110874995750237381443405 3791578123406339018041277)
                      ·
                        rfl

theorem cell23_7384072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_7384072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384072 prefixEnd_7384072 := by exact prefixLift 7384072
  have htrace : WordTrace (prefixWord ++ tailWord_7384072) baseStart_7384072 baseEnd_7384072 := by
    simpa [prefixWord, tailWord_7384072, baseEnd_7384072] using wordTrace_append hprefix tailTrace_7384072
  have hstable : (prefixWord ++ tailWord_7384072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384072).length < 2 ^ (prefixWord ++ tailWord_7384072).sum := by decide
  have hdescent : baseEnd_7384072 < baseStart_7384072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384085 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_7384085 : Nat := 118140960795 + 7384085 * 2 ^ 59
def prefixEnd_7384085 : Nat := 4983230072969 + 3 ^ 40 * 7384085 * 2
def baseEnd_7384085 : Nat := 3791584798654847467178717

theorem tailTrace_7384085 : CollatzResearch.WordTrace tailWord_7384085 prefixEnd_7384085 3791584798654847467178717 := by
  unfold tailWord_7384085
  simp only [CollatzResearch.WordTrace]
  refine ⟨269319705453728621161705709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179546470302485747441137139 269319705453728621161705709)
  ·
    refine ⟨100994889545148232935639641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269319705453728621161705709 100994889545148232935639641)
    ·
      refine ⟨75746167158861174701729731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100994889545148232935639641 75746167158861174701729731)
      ·
        refine ⟨113619250738291762052594597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75746167158861174701729731 113619250738291762052594597)
        ·
          refine ⟨21303609513429705384861487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113619250738291762052594597 21303609513429705384861487)
          ·
            refine ⟨31955414270144558077292231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21303609513429705384861487 31955414270144558077292231)
            ·
              refine ⟨47933121405216837115938347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31955414270144558077292231 47933121405216837115938347)
              ·
                refine ⟨71899682107825255673907521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47933121405216837115938347 71899682107825255673907521)
                ·
                  refine ⟨53924761580868941755430641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71899682107825255673907521 53924761580868941755430641)
                  ·
                    refine ⟨40443571185651706316572981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53924761580868941755430641 40443571185651706316572981)
                    ·
                      refine ⟨3791584798654847467178717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40443571185651706316572981 3791584798654847467178717)
                      ·
                        rfl

theorem cell23_7384085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_7384085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384085 prefixEnd_7384085 := by exact prefixLift 7384085
  have htrace : WordTrace (prefixWord ++ tailWord_7384085) baseStart_7384085 baseEnd_7384085 := by
    simpa [prefixWord, tailWord_7384085, baseEnd_7384085] using wordTrace_append hprefix tailTrace_7384085
  have hstable : (prefixWord ++ tailWord_7384085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384085).length < 2 ^ (prefixWord ++ tailWord_7384085).sum := by decide
  have hdescent : baseEnd_7384085 < baseStart_7384085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384099 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 1, 3, 2]
def baseStart_7384099 : Nat := 118140960795 + 7384099 * 2 ^ 59
def prefixEnd_7384099 : Nat := 4983230072969 + 3 ^ 40 * 7384099 * 2
def baseEnd_7384099 : Nat := 3791591987384010412403653

theorem tailTrace_7384099 : CollatzResearch.WordTrace tailWord_7384099 prefixEnd_7384099 3791591987384010412403653 := by
  unfold tailWord_7384099
  simp only [CollatzResearch.WordTrace]
  refine ⟨269320216075677901552715351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179546810717118601035143567 269320216075677901552715351)
  ·
    refine ⟨403980324113516852329073027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269320216075677901552715351 403980324113516852329073027)
    ·
      refine ⟨605970486170275278493609541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403980324113516852329073027 605970486170275278493609541)
      ·
        refine ⟨113619466156926614717551789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 605970486170275278493609541 113619466156926614717551789)
        ·
          refine ⟨42607299808847480519081921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113619466156926614717551789 42607299808847480519081921)
          ·
            refine ⟨31955474856635610389311441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42607299808847480519081921 31955474856635610389311441)
            ·
              refine ⟨23966606142476707791983581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31955474856635610389311441 23966606142476707791983581)
              ·
                refine ⟨8987477303428765421993843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23966606142476707791983581 8987477303428765421993843)
                ·
                  refine ⟨13481215955143148132990765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8987477303428765421993843 13481215955143148132990765)
                  ·
                    refine ⟨5055455983178680549871537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13481215955143148132990765 5055455983178680549871537)
                    ·
                      refine ⟨3791591987384010412403653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055455983178680549871537 3791591987384010412403653)
                      ·
                        rfl

theorem cell23_7384099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_7384099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384099 prefixEnd_7384099 := by exact prefixLift 7384099
  have htrace : WordTrace (prefixWord ++ tailWord_7384099) baseStart_7384099 baseEnd_7384099 := by
    simpa [prefixWord, tailWord_7384099, baseEnd_7384099] using wordTrace_append hprefix tailTrace_7384099
  have hstable : (prefixWord ++ tailWord_7384099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384099).length < 2 ^ (prefixWord ++ tailWord_7384099).sum := by decide
  have hdescent : baseEnd_7384099 < baseStart_7384099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384115 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 3]
def baseStart_7384115 : Nat := 118140960795 + 7384115 * 2 ^ 59
def prefixEnd_7384115 : Nat := 4983230072969 + 3 ^ 40 * 7384115 * 2
def baseEnd_7384115 : Nat := 3791600203074482349803579

theorem tailTrace_7384115 : CollatzResearch.WordTrace tailWord_7384115 prefixEnd_7384115 3791600203074482349803579 := by
  unfold tailWord_7384115
  simp only [CollatzResearch.WordTrace]
  refine ⟨269320799643619936285297799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179547199762413290856865199 269320799643619936285297799)
  ·
    refine ⟨403981199465429904427946699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269320799643619936285297799 403981199465429904427946699)
    ·
      refine ⟨605971799198144856641920049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403981199465429904427946699 605971799198144856641920049)
      ·
        refine ⟨454478849398608642481440037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605971799198144856641920049 454478849398608642481440037)
        ·
          refine ⟨85214784262239120465270007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454478849398608642481440037 85214784262239120465270007)
          ·
            refine ⟨127822176393358680697905011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85214784262239120465270007 127822176393358680697905011)
            ·
              refine ⟨191733264590038021046857517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127822176393358680697905011 191733264590038021046857517)
              ·
                refine ⟨71899974221264257892571569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191733264590038021046857517 71899974221264257892571569)
                ·
                  refine ⟨53924980665948193419428677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71899974221264257892571569 53924980665948193419428677)
                  ·
                    refine ⟨10110933874865286266142877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53924980665948193419428677 10110933874865286266142877)
                    ·
                      refine ⟨3791600203074482349803579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10110933874865286266142877 3791600203074482349803579)
                      ·
                        rfl

theorem cell23_7384115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 3].length) (baseStart_7384115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384115 prefixEnd_7384115 := by exact prefixLift 7384115
  have htrace : WordTrace (prefixWord ++ tailWord_7384115) baseStart_7384115 baseEnd_7384115 := by
    simpa [prefixWord, tailWord_7384115, baseEnd_7384115] using wordTrace_append hprefix tailTrace_7384115
  have hstable : (prefixWord ++ tailWord_7384115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384115).length < 2 ^ (prefixWord ++ tailWord_7384115).sum := by decide
  have hdescent : baseEnd_7384115 < baseStart_7384115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384152 : List Nat := [2, 1, 2, 2, 1, 3, 2, 5, 5]
def baseStart_7384152 : Nat := 118140960795 + 7384152 * 2 ^ 59
def prefixEnd_7384152 : Nat := 4983230072969 + 3 ^ 40 * 7384152 * 2
def baseEnd_7384152 : Nat := 421291022428744300560101

theorem tailTrace_7384152 : CollatzResearch.WordTrace tailWord_7384152 prefixEnd_7384152 421291022428744300560101 := by
  unfold tailWord_7384152
  simp only [CollatzResearch.WordTrace]
  refine ⟨134661074572242945802197355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179548099429657261069596473 134661074572242945802197355)
  ·
    refine ⟨201991611858364418703296033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134661074572242945802197355 201991611858364418703296033)
    ·
      refine ⟨151493708893773314027472025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201991611858364418703296033 151493708893773314027472025)
      ·
        refine ⟨113620281670329985520604019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151493708893773314027472025 113620281670329985520604019)
        ·
          refine ⟨170430422505494978280906029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113620281670329985520604019 170430422505494978280906029)
          ·
            refine ⟨63911408439560616855339761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170430422505494978280906029 63911408439560616855339761)
            ·
              refine ⟨47933556329670462641504821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63911408439560616855339761 47933556329670462641504821)
              ·
                refine ⟨4493770905906605872641077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47933556329670462641504821 4493770905906605872641077)
                ·
                  refine ⟨421291022428744300560101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4493770905906605872641077 421291022428744300560101)
                  ·
                    rfl

theorem cell23_7384152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 5].length) (baseStart_7384152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384152 prefixEnd_7384152 := by exact prefixLift 7384152
  have htrace : WordTrace (prefixWord ++ tailWord_7384152) baseStart_7384152 baseEnd_7384152 := by
    simpa [prefixWord, tailWord_7384152, baseEnd_7384152] using wordTrace_append hprefix tailTrace_7384152
  have hstable : (prefixWord ++ tailWord_7384152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384152).length < 2 ^ (prefixWord ++ tailWord_7384152).sum := by decide
  have hdescent : baseEnd_7384152 < baseStart_7384152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384169 : List Nat := [1, 2, 1, 1, 1, 6, 4, 2, 5]
def baseStart_7384169 : Nat := 118140960795 + 7384169 * 2 ^ 59
def prefixEnd_7384169 : Nat := 4983230072969 + 3 ^ 40 * 7384169 * 2
def baseEnd_7384169 : Nat := 421291992336647237614259

theorem tailTrace_7384169 : CollatzResearch.WordTrace tailWord_7384169 prefixEnd_7384169 421291992336647237614259 := by
  unfold tailWord_7384169
  simp only [CollatzResearch.WordTrace]
  refine ⟨269322769185424303507763561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179548512790282869005175707 269322769185424303507763561)
  ·
    refine ⟨201992076889068227630822671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269322769185424303507763561 201992076889068227630822671)
    ·
      refine ⟨302988115333602341446234007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201992076889068227630822671 302988115333602341446234007)
      ·
        refine ⟨454482173000403512169351011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302988115333602341446234007 454482173000403512169351011)
        ·
          refine ⟨681723259500605268254026517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454482173000403512169351011 681723259500605268254026517)
          ·
            refine ⟨31955777789090871949407493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 681723259500605268254026517 31955777789090871949407493)
            ·
              refine ⟨5991708335454538490513905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31955777789090871949407493 5991708335454538490513905)
              ·
                refine ⟨4493781251590903867885429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5991708335454538490513905 4493781251590903867885429)
                ·
                  refine ⟨421291992336647237614259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4493781251590903867885429 421291992336647237614259)
                  ·
                    rfl

theorem cell23_7384169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 5].length) (baseStart_7384169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384169 prefixEnd_7384169 := by exact prefixLift 7384169
  have htrace : WordTrace (prefixWord ++ tailWord_7384169) baseStart_7384169 baseEnd_7384169 := by
    simpa [prefixWord, tailWord_7384169, baseEnd_7384169] using wordTrace_append hprefix tailTrace_7384169
  have hstable : (prefixWord ++ tailWord_7384169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384169).length < 2 ^ (prefixWord ++ tailWord_7384169).sum := by decide
  have hdescent : baseEnd_7384169 < baseStart_7384169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384172 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 1, 7, 2]
def baseStart_7384172 : Nat := 118140960795 + 7384172 * 2 ^ 59
def prefixEnd_7384172 : Nat := 4983230072969 + 3 ^ 40 * 7384172 * 2
def baseEnd_7384172 : Nat := 3791629471471788626790817

theorem tailTrace_7384172 : CollatzResearch.WordTrace tailWord_7384172 prefixEnd_7384172 3791629471471788626790817 := by
  unfold tailWord_7384172
  simp only [CollatzResearch.WordTrace]
  refine ⟨134661439302206717510061385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179548585736275623346748513 134661439302206717510061385)
  ·
    refine ⟨100996079476655038132546039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134661439302206717510061385 100996079476655038132546039)
    ·
      refine ⟨151494119214982557198819059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100996079476655038132546039 151494119214982557198819059)
      ·
        refine ⟨227241178822473835798228589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151494119214982557198819059 227241178822473835798228589)
        ·
          refine ⟨85215442058427688424335721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227241178822473835798228589 85215442058427688424335721)
          ·
            refine ⟨63911581543820766318251791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85215442058427688424335721 63911581543820766318251791)
            ·
              refine ⟨95867372315731149477377687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63911581543820766318251791 95867372315731149477377687)
              ·
                refine ⟨143801058473596724216066531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95867372315731149477377687 143801058473596724216066531)
                ·
                  refine ⟨215701587710395086324099797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143801058473596724216066531 215701587710395086324099797)
                  ·
                    refine ⟨5055505961962384835721089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 215701587710395086324099797 5055505961962384835721089)
                    ·
                      refine ⟨3791629471471788626790817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055505961962384835721089 3791629471471788626790817)
                      ·
                        rfl

theorem cell23_7384172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_7384172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384172 prefixEnd_7384172 := by exact prefixLift 7384172
  have htrace : WordTrace (prefixWord ++ tailWord_7384172) baseStart_7384172 baseEnd_7384172 := by
    simpa [prefixWord, tailWord_7384172, baseEnd_7384172] using wordTrace_append hprefix tailTrace_7384172
  have hstable : (prefixWord ++ tailWord_7384172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384172).length < 2 ^ (prefixWord ++ tailWord_7384172).sum := by decide
  have hdescent : baseEnd_7384172 < baseStart_7384172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384175 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_7384175 : Nat := 118140960795 + 7384175 * 2 ^ 59
def prefixEnd_7384175 : Nat := 4983230072969 + 3 ^ 40 * 7384175 * 2
def baseEnd_7384175 : Nat := 3791631011913752115053303

theorem tailTrace_7384175 : CollatzResearch.WordTrace tailWord_7384175 prefixEnd_7384175 3791631011913752115053303 := by
  unfold tailWord_7384175
  simp only [CollatzResearch.WordTrace]
  refine ⟨269322988023402566532481979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179548658682268377688321319 269322988023402566532481979)
  ·
    refine ⟨403984482035103849798722969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269322988023402566532481979 403984482035103849798722969)
    ·
      refine ⟨302988361526327887349042227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403984482035103849798722969 302988361526327887349042227)
      ·
        refine ⟨454482542289491831023563341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302988361526327887349042227 454482542289491831023563341)
        ·
          refine ⟨170430953358559436633836253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454482542289491831023563341 170430953358559436633836253)
          ·
            refine ⟨63911607509459788737688595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170430953358559436633836253 63911607509459788737688595)
            ·
              refine ⟨95867411264189683106532893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63911607509459788737688595 95867411264189683106532893)
              ·
                refine ⟨35950279224071131164949835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95867411264189683106532893 35950279224071131164949835)
                ·
                  refine ⟨53925418836106696747424753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35950279224071131164949835 53925418836106696747424753)
                  ·
                    refine ⟨40444064127080022560568565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53925418836106696747424753 40444064127080022560568565)
                    ·
                      refine ⟨3791631011913752115053303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40444064127080022560568565 3791631011913752115053303)
                      ·
                        rfl

theorem cell23_7384175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_7384175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384175 prefixEnd_7384175 := by exact prefixLift 7384175
  have htrace : WordTrace (prefixWord ++ tailWord_7384175) baseStart_7384175 baseEnd_7384175 := by
    simpa [prefixWord, tailWord_7384175, baseEnd_7384175] using wordTrace_append hprefix tailTrace_7384175
  have hstable : (prefixWord ++ tailWord_7384175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384175).length < 2 ^ (prefixWord ++ tailWord_7384175).sum := by decide
  have hdescent : baseEnd_7384175 < baseStart_7384175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384182 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_7384182 : Nat := 118140960795 + 7384182 * 2 ^ 59
def prefixEnd_7384182 : Nat := 4983230072969 + 3 ^ 40 * 7384182 * 2
def baseEnd_7384182 : Nat := 1263878202092777862555257

theorem tailTrace_7384182 : CollatzResearch.WordTrace tailWord_7384182 prefixEnd_7384182 1263878202092777862555257 := by
  unfold tailWord_7384182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16832702708398575420499175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179548828889584804485324533 16832702708398575420499175)
  ·
    refine ⟨25249054062597863130748763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16832702708398575420499175 25249054062597863130748763)
    ·
      refine ⟨37873581093896794696123145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25249054062597863130748763 37873581093896794696123145)
      ·
        refine ⟨28405185820422596022092359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37873581093896794696123145 28405185820422596022092359)
        ·
          refine ⟨42607778730633894033138539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28405185820422596022092359 42607778730633894033138539)
          ·
            refine ⟨63911668095950841049707809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42607778730633894033138539 63911668095950841049707809)
            ·
              refine ⟨47933751071963130787280857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63911668095950841049707809 47933751071963130787280857)
              ·
                refine ⟨35950313303972348090460643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47933751071963130787280857 35950313303972348090460643)
                ·
                  refine ⟨53925469955958522135690965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35950313303972348090460643 53925469955958522135690965)
                  ·
                    refine ⟨1263878202092777862555257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53925469955958522135690965 1263878202092777862555257)
                    ·
                      rfl

theorem cell23_7384182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_7384182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384182 prefixEnd_7384182 := by exact prefixLift 7384182
  have htrace : WordTrace (prefixWord ++ tailWord_7384182) baseStart_7384182 baseEnd_7384182 := by
    simpa [prefixWord, tailWord_7384182, baseEnd_7384182] using wordTrace_append hprefix tailTrace_7384182
  have hstable : (prefixWord ++ tailWord_7384182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384182).length < 2 ^ (prefixWord ++ tailWord_7384182).sum := by decide
  have hdescent : baseEnd_7384182 < baseStart_7384182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384202 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_7384202 : Nat := 118140960795 + 7384202 * 2 ^ 59
def prefixEnd_7384202 : Nat := 4983230072969 + 3 ^ 40 * 7384202 * 2
def baseEnd_7384202 : Nat := 3791644875891423509415679

theorem tailTrace_7384202 : CollatzResearch.WordTrace tailWord_7384202 prefixEnd_7384202 3791644875891423509415679 := by
  unfold tailWord_7384202
  simp only [CollatzResearch.WordTrace]
  refine ⟨67330993198576187535928715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179549315196203166762476573 67330993198576187535928715)
  ·
    refine ⟨100996489797864281303893073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67330993198576187535928715 100996489797864281303893073)
    ·
      refine ⟨75747367348398210977919805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100996489797864281303893073 75747367348398210977919805)
      ·
        refine ⟨28405262755649329116719927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75747367348398210977919805 28405262755649329116719927)
        ·
          refine ⟨42607894133473993675079891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28405262755649329116719927 42607894133473993675079891)
          ·
            refine ⟨63911841200210990512619837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42607894133473993675079891 63911841200210990512619837)
            ·
              refine ⟨23966940450079121442232439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63911841200210990512619837 23966940450079121442232439)
              ·
                refine ⟨35950410675118682163348659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23966940450079121442232439 35950410675118682163348659)
                ·
                  refine ⟨53925616012678023245022989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35950410675118682163348659 53925616012678023245022989)
                  ·
                    refine ⟨20222106004754258716883621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53925616012678023245022989 20222106004754258716883621)
                    ·
                      refine ⟨3791644875891423509415679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20222106004754258716883621 3791644875891423509415679)
                      ·
                        rfl

theorem cell23_7384202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_7384202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384202 prefixEnd_7384202 := by exact prefixLift 7384202
  have htrace : WordTrace (prefixWord ++ tailWord_7384202) baseStart_7384202 baseEnd_7384202 := by
    simpa [prefixWord, tailWord_7384202, baseEnd_7384202] using wordTrace_append hprefix tailTrace_7384202
  have hstable : (prefixWord ++ tailWord_7384202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384202).length < 2 ^ (prefixWord ++ tailWord_7384202).sum := by decide
  have hdescent : baseEnd_7384202 < baseStart_7384202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384229 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_7384229 : Nat := 118140960795 + 7384229 * 2 ^ 59
def prefixEnd_7384229 : Nat := 4983230072969 + 3 ^ 40 * 7384229 * 2
def baseEnd_7384229 : Nat := 1263886246623031634592685

theorem tailTrace_7384229 : CollatzResearch.WordTrace tailWord_7384229 prefixEnd_7384229 1263886246623031634592685 := by
  unfold tailWord_7384229
  simp only [CollatzResearch.WordTrace]
  refine ⟨269324957565206933754947741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179549971710137955836631827 269324957565206933754947741)
  ·
    refine ⟨100996859086952600158105403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269324957565206933754947741 100996859086952600158105403)
    ·
      refine ⟨151495288630428900237158105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100996859086952600158105403 151495288630428900237158105)
      ·
        refine ⟨113621466472821675177868579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151495288630428900237158105 113621466472821675177868579)
        ·
          refine ⟨170432199709232512766802869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113621466472821675177868579 170432199709232512766802869)
          ·
            refine ⟨15978018722740548071887769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170432199709232512766802869 15978018722740548071887769)
            ·
              refine ⟨11983514042055411053915827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15978018722740548071887769 11983514042055411053915827)
              ·
                refine ⟨17975271063083116580873741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11983514042055411053915827 17975271063083116580873741)
                ·
                  refine ⟨6740726648656168717827653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17975271063083116580873741 6740726648656168717827653)
                  ·
                    refine ⟨1263886246623031634592685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6740726648656168717827653 1263886246623031634592685)
                    ·
                      rfl

theorem cell23_7384229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_7384229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384229 prefixEnd_7384229 := by exact prefixLift 7384229
  have htrace : WordTrace (prefixWord ++ tailWord_7384229) baseStart_7384229 baseEnd_7384229 := by
    simpa [prefixWord, tailWord_7384229, baseEnd_7384229] using wordTrace_append hprefix tailTrace_7384229
  have hstable : (prefixWord ++ tailWord_7384229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384229).length < 2 ^ (prefixWord ++ tailWord_7384229).sum := by decide
  have hdescent : baseEnd_7384229 < baseStart_7384229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384265 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_7384265 : Nat := 118140960795 + 7384265 * 2 ^ 59
def prefixEnd_7384265 : Nat := 4983230072969 + 3 ^ 40 * 7384265 * 2
def baseEnd_7384265 : Nat := 3791677225172656762927889

theorem tailTrace_7384265 : CollatzResearch.WordTrace tailWord_7384265 prefixEnd_7384265 3791677225172656762927889 := by
  unfold tailWord_7384265
  simp only [CollatzResearch.WordTrace]
  refine ⟨269326270593076511903258249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179550847062051007935505499 269326270593076511903258249)
  ·
    refine ⟨201994702944807383927443687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269326270593076511903258249 201994702944807383927443687)
    ·
      refine ⟨302992054417211075891165531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201994702944807383927443687 302992054417211075891165531)
      ·
        refine ⟨454488081625816613836748297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302992054417211075891165531 454488081625816613836748297)
        ·
          refine ⟨340866061219362460377561223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454488081625816613836748297 340866061219362460377561223)
          ·
            refine ⟨511299091829043690566341835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340866061219362460377561223 511299091829043690566341835)
            ·
              refine ⟨766948637743565535849512753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511299091829043690566341835 766948637743565535849512753)
              ·
                refine ⟨575211478307674151887134565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766948637743565535849512753 575211478307674151887134565)
                ·
                  refine ⟨107852152182688903478837731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575211478307674151887134565 107852152182688903478837731)
                  ·
                    refine ⟨161778228274033355218256597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107852152182688903478837731 161778228274033355218256597)
                    ·
                      refine ⟨3791677225172656762927889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161778228274033355218256597 3791677225172656762927889)
                      ·
                        rfl

theorem cell23_7384265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_7384265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384265 prefixEnd_7384265 := by exact prefixLift 7384265
  have htrace : WordTrace (prefixWord ++ tailWord_7384265) baseStart_7384265 baseEnd_7384265 := by
    simpa [prefixWord, tailWord_7384265, baseEnd_7384265] using wordTrace_append hprefix tailTrace_7384265
  have hstable : (prefixWord ++ tailWord_7384265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384265).length < 2 ^ (prefixWord ++ tailWord_7384265).sum := by decide
  have hdescent : baseEnd_7384265 < baseStart_7384265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384279 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 4, 3, 2]
def baseStart_7384279 : Nat := 118140960795 + 7384279 * 2 ^ 59
def prefixEnd_7384279 : Nat := 4983230072969 + 3 ^ 40 * 7384279 * 2
def baseEnd_7384279 : Nat := 3791684413901819708152825

theorem tailTrace_7384279 : CollatzResearch.WordTrace tailWord_7384279 prefixEnd_7384279 3791684413901819708152825 := by
  unfold tailWord_7384279
  simp only [CollatzResearch.WordTrace]
  refine ⟨269326781215025792294267891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179551187476683861529511927 269326781215025792294267891)
  ·
    refine ⟨403990171822538688441401837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269326781215025792294267891 403990171822538688441401837)
    ·
      refine ⟨151496314433452008165525689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403990171822538688441401837 151496314433452008165525689)
      ·
        refine ⟨113622235825089006124144267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151496314433452008165525689 113622235825089006124144267)
        ·
          refine ⟨170433353737633509186216401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113622235825089006124144267 170433353737633509186216401)
          ·
            refine ⟨127825015303225131889662301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170433353737633509186216401 127825015303225131889662301)
            ·
              refine ⟨47934380738709424458623363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127825015303225131889662301 47934380738709424458623363)
              ·
                refine ⟨71901571108064136687935045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47934380738709424458623363 71901571108064136687935045)
                ·
                  refine ⟨13481544582762025628987821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71901571108064136687935045 13481544582762025628987821)
                  ·
                    refine ⟨5055579218535759610870433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13481544582762025628987821 5055579218535759610870433)
                    ·
                      refine ⟨3791684413901819708152825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055579218535759610870433 3791684413901819708152825)
                      ·
                        rfl

theorem cell23_7384279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_7384279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384279 prefixEnd_7384279 := by exact prefixLift 7384279
  have htrace : WordTrace (prefixWord ++ tailWord_7384279) baseStart_7384279 baseEnd_7384279 := by
    simpa [prefixWord, tailWord_7384279, baseEnd_7384279] using wordTrace_append hprefix tailTrace_7384279
  have hstable : (prefixWord ++ tailWord_7384279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384279).length < 2 ^ (prefixWord ++ tailWord_7384279).sum := by decide
  have hdescent : baseEnd_7384279 < baseStart_7384279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384293 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 6]
def baseStart_7384293 : Nat := 118140960795 + 7384293 * 2 ^ 59
def prefixEnd_7384293 : Nat := 4983230072969 + 3 ^ 40 * 7384293 * 2
def baseEnd_7384293 : Nat := 421299066958998072597529

theorem tailTrace_7384293 : CollatzResearch.WordTrace tailWord_7384293 prefixEnd_7384293 421299066958998072597529 := by
  unfold tailWord_7384293
  simp only [CollatzResearch.WordTrace]
  refine ⟨269327291836975072685277533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179551527891316715123518355 269327291836975072685277533)
  ·
    refine ⟨100997734438865652256979075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269327291836975072685277533 100997734438865652256979075)
    ·
      refine ⟨151496601658298478385468613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100997734438865652256979075 151496601658298478385468613)
      ·
        refine ⟨28405612810930964697275365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151496601658298478385468613 28405612810930964697275365)
        ·
          refine ⟨5326052402049555880739131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28405612810930964697275365 5326052402049555880739131)
          ·
            refine ⟨7989078603074333821108697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326052402049555880739131 7989078603074333821108697)
            ·
              refine ⟨5991808952305750365831523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7989078603074333821108697 5991808952305750365831523)
              ·
                refine ⟨8987713428458625548747285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991808952305750365831523 8987713428458625548747285)
                ·
                  refine ⟨421299066958998072597529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8987713428458625548747285 421299066958998072597529)
                  ·
                    rfl

theorem cell23_7384293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_7384293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384293 prefixEnd_7384293 := by exact prefixLift 7384293
  have htrace : WordTrace (prefixWord ++ tailWord_7384293) baseStart_7384293 baseEnd_7384293 := by
    simpa [prefixWord, tailWord_7384293, baseEnd_7384293] using wordTrace_append hprefix tailTrace_7384293
  have hstable : (prefixWord ++ tailWord_7384293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384293).length < 2 ^ (prefixWord ++ tailWord_7384293).sum := by decide
  have hdescent : baseEnd_7384293 < baseStart_7384293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384349 : List Nat := [1, 4, 2, 3, 1, 1, 3, 8]
def baseStart_7384349 : Nat := 118140960795 + 7384349 * 2 ^ 59
def prefixEnd_7384349 : Nat := 4983230072969 + 3 ^ 40 * 7384349 * 2
def baseEnd_7384349 : Nat := 140434087316579053121389

theorem tailTrace_7384349 : CollatzResearch.WordTrace tailWord_7384349 prefixEnd_7384349 140434087316579053121389 := by
  unfold tailWord_7384349
  simp only [CollatzResearch.WordTrace]
  refine ⟨269329334324772194249316101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179552889549848129499544067 269329334324772194249316101)
  ·
    refine ⟨50499250185894786421746769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269329334324772194249316101 50499250185894786421746769)
    ·
      refine ⟨37874437639421089816310077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50499250185894786421746769 37874437639421089816310077)
      ·
        refine ⟨14202914114782908681116279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37874437639421089816310077 14202914114782908681116279)
        ·
          refine ⟨21304371172174363021674419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14202914114782908681116279 21304371172174363021674419)
          ·
            refine ⟨31956556758261544532511629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21304371172174363021674419 31956556758261544532511629)
            ·
              refine ⟨11983708784348079199691861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31956556758261544532511629 11983708784348079199691861)
              ·
                refine ⟨140434087316579053121389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11983708784348079199691861 140434087316579053121389)
                ·
                  rfl

theorem cell23_7384349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 8].length) (baseStart_7384349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384349 prefixEnd_7384349 := by exact prefixLift 7384349
  have htrace : WordTrace (prefixWord ++ tailWord_7384349) baseStart_7384349 baseEnd_7384349 := by
    simpa [prefixWord, tailWord_7384349, baseEnd_7384349] using wordTrace_append hprefix tailTrace_7384349
  have hstable : (prefixWord ++ tailWord_7384349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384349).length < 2 ^ (prefixWord ++ tailWord_7384349).sum := by decide
  have hdescent : baseEnd_7384349 < baseStart_7384349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384377 : List Nat := [1, 2, 1, 6, 2, 1, 2, 3, 1, 2, 2]
def baseStart_7384377 : Nat := 118140960795 + 7384377 * 2 ^ 59
def prefixEnd_7384377 : Nat := 4983230072969 + 3 ^ 40 * 7384377 * 2
def baseEnd_7384377 : Nat := 3791734735005960324727375

theorem tailTrace_7384377 : CollatzResearch.WordTrace tailWord_7384377 prefixEnd_7384377 3791734735005960324727375 := by
  unfold tailWord_7384377
  simp only [CollatzResearch.WordTrace]
  refine ⟨269330355568670755031335385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179553570379113836687556923 269330355568670755031335385)
  ·
    refine ⟨201997766676503066273501539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269330355568670755031335385 201997766676503066273501539)
    ·
      refine ⟨302996650014754599410252309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201997766676503066273501539 302996650014754599410252309)
      ·
        refine ⟨14202967969441621847355577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 302996650014754599410252309 14202967969441621847355577)
        ·
          refine ⟨10652225977081216385516683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14202967969441621847355577 10652225977081216385516683)
          ·
            refine ⟨15978338965621824578275025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10652225977081216385516683 15978338965621824578275025)
            ·
              refine ⟨11983754224216368433706269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15978338965621824578275025 11983754224216368433706269)
              ·
                refine ⟨4493907834081138162639851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11983754224216368433706269 4493907834081138162639851)
                ·
                  refine ⟨6740861751121707243959777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493907834081138162639851 6740861751121707243959777)
                  ·
                    refine ⟨5055646313341280432969833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6740861751121707243959777 5055646313341280432969833)
                    ·
                      refine ⟨3791734735005960324727375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055646313341280432969833 3791734735005960324727375)
                      ·
                        rfl

theorem cell23_7384377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_7384377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384377 prefixEnd_7384377 := by exact prefixLift 7384377
  have htrace : WordTrace (prefixWord ++ tailWord_7384377) baseStart_7384377 baseEnd_7384377 := by
    simpa [prefixWord, tailWord_7384377, baseEnd_7384377] using wordTrace_append hprefix tailTrace_7384377
  have hstable : (prefixWord ++ tailWord_7384377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384377).length < 2 ^ (prefixWord ++ tailWord_7384377).sum := by decide
  have hdescent : baseEnd_7384377 < baseStart_7384377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384456 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 7]
def baseStart_7384456 : Nat := 118140960795 + 7384456 * 2 ^ 59
def prefixEnd_7384456 : Nat := 4983230072969 + 3 ^ 40 * 7384456 * 2
def baseEnd_7384456 : Nat := 421308366664185057293279

theorem tailTrace_7384456 : CollatzResearch.WordTrace tailWord_7384456 prefixEnd_7384456 421308366664185057293279 := by
  unfold tailWord_7384456
  simp only [CollatzResearch.WordTrace]
  refine ⟨134666618467692275761730611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179555491290256367682307481 134666618467692275761730611)
  ·
    refine ⟨201999927701538413642595917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134666618467692275761730611 201999927701538413642595917)
    ·
      refine ⟨75749972888076905115973469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201999927701538413642595917 75749972888076905115973469)
      ·
        refine ⟨28406239833028839418490051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75749972888076905115973469 28406239833028839418490051)
        ·
          refine ⟨42609359749543259127735077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28406239833028839418490051 42609359749543259127735077)
          ·
            refine ⟨7989254953039361086450327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42609359749543259127735077 7989254953039361086450327)
            ·
              refine ⟨11983882429559041629675491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7989254953039361086450327 11983882429559041629675491)
              ·
                refine ⟨17975823644338562444513237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11983882429559041629675491 17975823644338562444513237)
                ·
                  refine ⟨421308366664185057293279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17975823644338562444513237 421308366664185057293279)
                  ·
                    rfl

theorem cell23_7384456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 7].length) (baseStart_7384456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384456 prefixEnd_7384456 := by exact prefixLift 7384456
  have htrace : WordTrace (prefixWord ++ tailWord_7384456) baseStart_7384456 baseEnd_7384456 := by
    simpa [prefixWord, tailWord_7384456, baseEnd_7384456] using wordTrace_append hprefix tailTrace_7384456
  have hstable : (prefixWord ++ tailWord_7384456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384456).length < 2 ^ (prefixWord ++ tailWord_7384456).sum := by decide
  have hdescent : baseEnd_7384456 < baseStart_7384456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384509 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_7384509 : Nat := 118140960795 + 7384509 * 2 ^ 59
def prefixEnd_7384509 : Nat := 4983230072969 + 3 ^ 40 * 7384509 * 2
def baseEnd_7384509 : Nat := 3791802514452353808276767

theorem tailTrace_7384509 : CollatzResearch.WordTrace tailWord_7384509 prefixEnd_7384509 3791802514452353808276767 := by
  unfold tailWord_7384509
  simp only [CollatzResearch.WordTrace]
  refine ⟨269335170004192541575140581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179556780002795027716760387 269335170004192541575140581)
  ·
    refine ⟨50500344375786101545338859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269335170004192541575140581 50500344375786101545338859)
    ·
      refine ⟨75750516563679152318008289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50500344375786101545338859 75750516563679152318008289)
      ·
        refine ⟨56812887422759364238506217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75750516563679152318008289 56812887422759364238506217)
        ·
          refine ⟨42609665567069523178879663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56812887422759364238506217 42609665567069523178879663)
          ·
            refine ⟨63914498350604284768319495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42609665567069523178879663 63914498350604284768319495)
            ·
              refine ⟨95871747525906427152479243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63914498350604284768319495 95871747525906427152479243)
              ·
                refine ⟨143807621288859640728718865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95871747525906427152479243 143807621288859640728718865)
                ·
                  refine ⟨107855715966644730546539149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143807621288859640728718865 107855715966644730546539149)
                  ·
                    refine ⟨40445893487491773954952181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107855715966644730546539149 40445893487491773954952181)
                    ·
                      refine ⟨3791802514452353808276767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40445893487491773954952181 3791802514452353808276767)
                      ·
                        rfl

theorem cell23_7384509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_7384509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384509 prefixEnd_7384509 := by exact prefixLift 7384509
  have htrace : WordTrace (prefixWord ++ tailWord_7384509) baseStart_7384509 baseEnd_7384509 := by
    simpa [prefixWord, tailWord_7384509, baseEnd_7384509] using wordTrace_append hprefix tailTrace_7384509
  have hstable : (prefixWord ++ tailWord_7384509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384509).length < 2 ^ (prefixWord ++ tailWord_7384509).sum := by decide
  have hdescent : baseEnd_7384509 < baseStart_7384509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384526 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_7384526 : Nat := 118140960795 + 7384526 * 2 ^ 59
def prefixEnd_7384526 : Nat := 4983230072969 + 3 ^ 40 * 7384526 * 2
def baseEnd_7384526 : Nat := 3791811243623480241764189

theorem tailTrace_7384526 : CollatzResearch.WordTrace tailWord_7384526 prefixEnd_7384526 3791811243623480241764189 := by
  unfold tailWord_7384526
  simp only [CollatzResearch.WordTrace]
  refine ⟨33666973755641369184813679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179557193363420635652339621 33666973755641369184813679)
  ·
    refine ⟨50500460633462053777220519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33666973755641369184813679 50500460633462053777220519)
    ·
      refine ⟨75750690950193080665830779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50500460633462053777220519 75750690950193080665830779)
      ·
        refine ⟨113626036425289620998746169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75750690950193080665830779 113626036425289620998746169)
        ·
          refine ⟨85219527318967215749059627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113626036425289620998746169 85219527318967215749059627)
          ·
            refine ⟨127829290978450823623589441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85219527318967215749059627 127829290978450823623589441)
            ·
              refine ⟨95871968233838117717692081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127829290978450823623589441 95871968233838117717692081)
              ·
                refine ⟨71903976175378588288269061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95871968233838117717692081 71903976175378588288269061)
                ·
                  refine ⟨13481995532883485304050449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71903976175378588288269061 13481995532883485304050449)
                  ·
                    refine ⟨10111496649662613978037837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13481995532883485304050449 10111496649662613978037837)
                    ·
                      refine ⟨3791811243623480241764189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10111496649662613978037837 3791811243623480241764189)
                      ·
                        rfl

theorem cell23_7384526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_7384526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384526 prefixEnd_7384526 := by exact prefixLift 7384526
  have htrace : WordTrace (prefixWord ++ tailWord_7384526) baseStart_7384526 baseEnd_7384526 := by
    simpa [prefixWord, tailWord_7384526, baseEnd_7384526] using wordTrace_append hprefix tailTrace_7384526
  have hstable : (prefixWord ++ tailWord_7384526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384526).length < 2 ^ (prefixWord ++ tailWord_7384526).sum := by decide
  have hdescent : baseEnd_7384526 < baseStart_7384526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384539 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 3]
def baseStart_7384539 : Nat := 118140960795 + 7384539 * 2 ^ 59
def prefixEnd_7384539 : Nat := 4983230072969 + 3 ^ 40 * 7384539 * 2
def baseEnd_7384539 : Nat := 3791817918871988690901629

theorem tailTrace_7384539 : CollatzResearch.WordTrace tailWord_7384539 prefixEnd_7384539 3791817918871988690901629 := by
  unfold tailWord_7384539
  simp only [CollatzResearch.WordTrace]
  refine ⟨269336264194083856698732671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179557509462722571132488447 269336264194083856698732671)
  ·
    refine ⟨404004396291125785048099007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269336264194083856698732671 404004396291125785048099007)
    ·
      refine ⟨606006594436688677572148511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404004396291125785048099007 606006594436688677572148511)
      ·
        refine ⟨909009891655033016358222767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606006594436688677572148511 909009891655033016358222767)
        ·
          refine ⟨1363514837482549524537334151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909009891655033016358222767 1363514837482549524537334151)
          ·
            refine ⟨2045272256223824286806001227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363514837482549524537334151 2045272256223824286806001227)
            ·
              refine ⟨3067908384335736430209001841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045272256223824286806001227 3067908384335736430209001841)
              ·
                refine ⟨2300931288251802322656751381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3067908384335736430209001841 2300931288251802322656751381)
                ·
                  refine ⟨107856154136803233874535221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2300931288251802322656751381 107856154136803233874535221)
                  ·
                    refine ⟨10111514450325303175737677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107856154136803233874535221 10111514450325303175737677)
                    ·
                      refine ⟨3791817918871988690901629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10111514450325303175737677 3791817918871988690901629)
                      ·
                        rfl

theorem cell23_7384539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 3].length) (baseStart_7384539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384539 prefixEnd_7384539 := by exact prefixLift 7384539
  have htrace : WordTrace (prefixWord ++ tailWord_7384539) baseStart_7384539 baseEnd_7384539 := by
    simpa [prefixWord, tailWord_7384539, baseEnd_7384539] using wordTrace_append hprefix tailTrace_7384539
  have hstable : (prefixWord ++ tailWord_7384539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384539).length < 2 ^ (prefixWord ++ tailWord_7384539).sum := by decide
  have hdescent : baseEnd_7384539 < baseStart_7384539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384566 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7384566 : Nat := 118140960795 + 7384566 * 2 ^ 59
def prefixEnd_7384566 : Nat := 4983230072969 + 3 ^ 40 * 7384566 * 2
def baseEnd_7384566 : Nat := 3791831782849660085264005

theorem tailTrace_7384566 : CollatzResearch.WordTrace tailWord_7384566 prefixEnd_7384566 3791831782849660085264005 := by
  unfold tailWord_7384566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16833578060311627519372847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179558165976657360206643701 16833578060311627519372847)
  ·
    refine ⟨25250367090467441279059271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16833578060311627519372847 25250367090467441279059271)
    ·
      refine ⟨37875550635701161918588907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25250367090467441279059271 37875550635701161918588907)
      ·
        refine ⟨56813325953551742877883361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37875550635701161918588907 56813325953551742877883361)
        ·
          refine ⟨42609994465163807158412521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56813325953551742877883361 42609994465163807158412521)
          ·
            refine ⟨31957495848872855368809391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42609994465163807158412521 31957495848872855368809391)
            ·
              refine ⟨47936243773309283053214087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31957495848872855368809391 47936243773309283053214087)
              ·
                refine ⟨71904365659963924579821131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47936243773309283053214087 71904365659963924579821131)
                ·
                  refine ⟨107856548489945886869731697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71904365659963924579821131 107856548489945886869731697)
                  ·
                    refine ⟨80892411367459415152298773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107856548489945886869731697 80892411367459415152298773)
                    ·
                      refine ⟨3791831782849660085264005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80892411367459415152298773 3791831782849660085264005)
                      ·
                        rfl

theorem cell23_7384566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7384566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384566 prefixEnd_7384566 := by exact prefixLift 7384566
  have htrace : WordTrace (prefixWord ++ tailWord_7384566) baseStart_7384566 baseEnd_7384566 := by
    simpa [prefixWord, tailWord_7384566, baseEnd_7384566] using wordTrace_append hprefix tailTrace_7384566
  have hstable : (prefixWord ++ tailWord_7384566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384566).length < 2 ^ (prefixWord ++ tailWord_7384566).sum := by decide
  have hdescent : baseEnd_7384566 < baseStart_7384566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384573 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_7384573 : Nat := 118140960795 + 7384573 * 2 ^ 59
def prefixEnd_7384573 : Nat := 4983230072969 + 3 ^ 40 * 7384573 * 2
def baseEnd_7384573 : Nat := 3791835377214241557876473

theorem tailTrace_7384573 : CollatzResearch.WordTrace tailWord_7384573 prefixEnd_7384573 3791835377214241557876473 := by
  unfold tailWord_7384573
  simp only [CollatzResearch.WordTrace]
  refine ⟨269337504275960680505470373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179558336183973787003646915 269337504275960680505470373)
  ·
    refine ⟨50500782051742627594775695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269337504275960680505470373 50500782051742627594775695)
    ·
      refine ⟨75751173077613941392163543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50500782051742627594775695 75751173077613941392163543)
      ·
        refine ⟨113626759616420912088245315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75751173077613941392163543 113626759616420912088245315)
        ·
          refine ⟨170440139424631368132367973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113626759616420912088245315 170440139424631368132367973)
          ·
            refine ⟨31957526142118381524818995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170440139424631368132367973 31957526142118381524818995)
            ·
              refine ⟨47936289213177572287228493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31957526142118381524818995 47936289213177572287228493)
              ·
                refine ⟨17976108454941589607710685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47936289213177572287228493 17976108454941589607710685)
                ·
                  refine ⟨6741040670603096102891507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17976108454941589607710685 6741040670603096102891507)
                  ·
                    refine ⟨10111561005904644154337261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6741040670603096102891507 10111561005904644154337261)
                    ·
                      refine ⟨3791835377214241557876473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10111561005904644154337261 3791835377214241557876473)
                      ·
                        rfl

theorem cell23_7384573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_7384573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384573 prefixEnd_7384573 := by exact prefixLift 7384573
  have htrace : WordTrace (prefixWord ++ tailWord_7384573) baseStart_7384573 baseEnd_7384573 := by
    simpa [prefixWord, tailWord_7384573, baseEnd_7384573] using wordTrace_append hprefix tailTrace_7384573
  have hstable : (prefixWord ++ tailWord_7384573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384573).length < 2 ^ (prefixWord ++ tailWord_7384573).sum := by decide
  have hdescent : baseEnd_7384573 < baseStart_7384573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384579 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 4]
def baseStart_7384579 : Nat := 118140960795 + 7384579 * 2 ^ 59
def prefixEnd_7384579 : Nat := 4983230072969 + 3 ^ 40 * 7384579 * 2
def baseEnd_7384579 : Nat := 3791838458098168534401445

theorem tailTrace_7384579 : CollatzResearch.WordTrace tailWord_7384579 prefixEnd_7384579 3791838458098168534401445 := by
  unfold tailWord_7384579
  simp only [CollatzResearch.WordTrace]
  refine ⟨269337723113938943530188791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179558482075959295686792527 269337723113938943530188791)
  ·
    refine ⟨404006584670908415295283187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269337723113938943530188791 404006584670908415295283187)
    ·
      refine ⟨606009877006362622942924781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404006584670908415295283187 606009877006362622942924781)
      ·
        refine ⟨227253703877385983603596793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606009877006362622942924781 227253703877385983603596793)
        ·
          refine ⟨170440277908039487702697595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227253703877385983603596793 170440277908039487702697595)
          ·
            refine ⟨255660416862059231554046393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170440277908039487702697595 255660416862059231554046393)
            ·
              refine ⟨191745312646544423665534795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255660416862059231554046393 191745312646544423665534795)
              ·
                refine ⟨287617968969816635498302193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191745312646544423665534795 287617968969816635498302193)
                ·
                  refine ⟨215713476727362476623726645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287617968969816635498302193 215713476727362476623726645)
                  ·
                    refine ⟨20223138443190232183474373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 215713476727362476623726645 20223138443190232183474373)
                    ·
                      refine ⟨3791838458098168534401445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20223138443190232183474373 3791838458098168534401445)
                      ·
                        rfl

theorem cell23_7384579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_7384579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384579 prefixEnd_7384579 := by exact prefixLift 7384579
  have htrace : WordTrace (prefixWord ++ tailWord_7384579) baseStart_7384579 baseEnd_7384579 := by
    simpa [prefixWord, tailWord_7384579, baseEnd_7384579] using wordTrace_append hprefix tailTrace_7384579
  have hstable : (prefixWord ++ tailWord_7384579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384579).length < 2 ^ (prefixWord ++ tailWord_7384579).sum := by decide
  have hdescent : baseEnd_7384579 < baseStart_7384579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384580 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 6]
def baseStart_7384580 : Nat := 118140960795 + 7384580 * 2 ^ 59
def prefixEnd_7384580 : Nat := 4983230072969 + 3 ^ 40 * 7384580 * 2
def baseEnd_7384580 : Nat := 421315441286535892276549

theorem tailTrace_7384580 : CollatzResearch.WordTrace tailWord_7384580 prefixEnd_7384580 421315441286535892276549 := by
  unfold tailWord_7384580
  simp only [CollatzResearch.WordTrace]
  refine ⟨134668879793467660350487597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179558506391290213800650129 134668879793467660350487597)
  ·
    refine ⟨50500829922550372631432849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134668879793467660350487597 50500829922550372631432849)
    ·
      refine ⟨37875622441912779473574637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50500829922550372631432849 37875622441912779473574637)
      ·
        refine ⟨14203358415717292302590489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37875622441912779473574637 14203358415717292302590489)
        ·
          refine ⟨10652518811787969226942867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14203358415717292302590489 10652518811787969226942867)
          ·
            refine ⟨15978778217681953840414301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10652518811787969226942867 15978778217681953840414301)
            ·
              refine ⟨5992041831630732690155363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15978778217681953840414301 5992041831630732690155363)
              ·
                refine ⟨8988062747446099035233045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5992041831630732690155363 8988062747446099035233045)
                ·
                  refine ⟨421315441286535892276549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8988062747446099035233045 421315441286535892276549)
                  ·
                    rfl

theorem cell23_7384580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_7384580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384580 prefixEnd_7384580 := by exact prefixLift 7384580
  have htrace : WordTrace (prefixWord ++ tailWord_7384580) baseStart_7384580 baseEnd_7384580 := by
    simpa [prefixWord, tailWord_7384580, baseEnd_7384580] using wordTrace_append hprefix tailTrace_7384580
  have hstable : (prefixWord ++ tailWord_7384580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384580).length < 2 ^ (prefixWord ++ tailWord_7384580).sum := by decide
  have hdescent : baseEnd_7384580 < baseStart_7384580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384583 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 1, 5, 2]
def baseStart_7384583 : Nat := 118140960795 + 7384583 * 2 ^ 59
def prefixEnd_7384583 : Nat := 4983230072969 + 3 ^ 40 * 7384583 * 2
def baseEnd_7384583 : Nat := 3791840512020786518751427

theorem tailTrace_7384583 : CollatzResearch.WordTrace tailWord_7384583 prefixEnd_7384583 3791840512020786518751427 := by
  unfold tailWord_7384583
  simp only [CollatzResearch.WordTrace]
  refine ⟨269337869005924452213334403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179558579337282968142222935 269337869005924452213334403)
  ·
    refine ⟨404006803508886678320001605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269337869005924452213334403 404006803508886678320001605)
    ·
      refine ⟨75751275657916252185000301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404006803508886678320001605 75751275657916252185000301)
      ·
        refine ⟨28406728371718594569375113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75751275657916252185000301 28406728371718594569375113)
        ·
          refine ⟨21305046278788945927031335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28406728371718594569375113 21305046278788945927031335)
          ·
            refine ⟨31957569418183418890547003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21305046278788945927031335 31957569418183418890547003)
            ·
              refine ⟨47936354127275128335820505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31957569418183418890547003 47936354127275128335820505)
              ·
                refine ⟨35952265595456346251865379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47936354127275128335820505 35952265595456346251865379)
                ·
                  refine ⟨53928398393184519377798069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35952265595456346251865379 53928398393184519377798069)
                  ·
                    refine ⟨5055787349361048691668569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53928398393184519377798069 5055787349361048691668569)
                    ·
                      refine ⟨3791840512020786518751427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055787349361048691668569 3791840512020786518751427)
                      ·
                        rfl

theorem cell23_7384583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_7384583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384583 prefixEnd_7384583 := by exact prefixLift 7384583
  have htrace : WordTrace (prefixWord ++ tailWord_7384583) baseStart_7384583 baseEnd_7384583 := by
    simpa [prefixWord, tailWord_7384583, baseEnd_7384583] using wordTrace_append hprefix tailTrace_7384583
  have hstable : (prefixWord ++ tailWord_7384583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384583).length < 2 ^ (prefixWord ++ tailWord_7384583).sum := by decide
  have hdescent : baseEnd_7384583 < baseStart_7384583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384647 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 1, 1, 4]
def baseStart_7384647 : Nat := 118140960795 + 7384647 * 2 ^ 59
def prefixEnd_7384647 : Nat := 4983230072969 + 3 ^ 40 * 7384647 * 2
def baseEnd_7384647 : Nat := 3791873374782674268351133

theorem tailTrace_7384647 : CollatzResearch.WordTrace tailWord_7384647 prefixEnd_7384647 3791873374782674268351133 := by
  unfold tailWord_7384647
  simp only [CollatzResearch.WordTrace]
  refine ⟨269340203277692591143664195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179560135518461727429109463 269340203277692591143664195)
  ·
    refine ⟨404010304916538886715496293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269340203277692591143664195 404010304916538886715496293)
    ·
      refine ⟨75751932171851041259155555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404010304916538886715496293 75751932171851041259155555)
      ·
        refine ⟨113627898257776561888733333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75751932171851041259155555 113627898257776561888733333)
        ·
          refine ⟨5326307730833276338534375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113627898257776561888733333 5326307730833276338534375)
          ·
            refine ⟨7989461596249914507801563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326307730833276338534375 7989461596249914507801563)
            ·
              refine ⟨11984192394374871761702345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7989461596249914507801563 11984192394374871761702345)
              ·
                refine ⟨8988144295781153821276759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11984192394374871761702345 8988144295781153821276759)
                ·
                  refine ⟨13482216443671730731915139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8988144295781153821276759 13482216443671730731915139)
                  ·
                    refine ⟨20223324665507596097872709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13482216443671730731915139 20223324665507596097872709)
                    ·
                      refine ⟨3791873374782674268351133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20223324665507596097872709 3791873374782674268351133)
                      ·
                        rfl

theorem cell23_7384647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_7384647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384647 prefixEnd_7384647 := by exact prefixLift 7384647
  have htrace : WordTrace (prefixWord ++ tailWord_7384647) baseStart_7384647 baseEnd_7384647 := by
    simpa [prefixWord, tailWord_7384647, baseEnd_7384647] using wordTrace_append hprefix tailTrace_7384647
  have hstable : (prefixWord ++ tailWord_7384647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384647).length < 2 ^ (prefixWord ++ tailWord_7384647).sum := by decide
  have hdescent : baseEnd_7384647 < baseStart_7384647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384663 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 3]
def baseStart_7384663 : Nat := 118140960795 + 7384663 * 2 ^ 59
def prefixEnd_7384663 : Nat := 4983230072969 + 3 ^ 40 * 7384663 * 2
def baseEnd_7384663 : Nat := 3791881590473146205751059

theorem tailTrace_7384663 : CollatzResearch.WordTrace tailWord_7384663 prefixEnd_7384663 3791881590473146205751059 := by
  unfold tailWord_7384663
  simp only [CollatzResearch.WordTrace]
  refine ⟨269340786845634625876246643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179560524563756417250831095 269340786845634625876246643)
  ·
    refine ⟨404011180268451938814369965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269340786845634625876246643 404011180268451938814369965)
    ·
      refine ⟨151504192600669477055388737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404011180268451938814369965 151504192600669477055388737)
      ·
        refine ⟨113628144450502107791541553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151504192600669477055388737 113628144450502107791541553)
        ·
          refine ⟨85221108337876580843656165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113628144450502107791541553 85221108337876580843656165)
          ·
            refine ⟨15978957813351858908185531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85221108337876580843656165 15978957813351858908185531)
            ·
              refine ⟨23968436720027788362278297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15978957813351858908185531 23968436720027788362278297)
              ·
                refine ⟨17976327540020841271708723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23968436720027788362278297 17976327540020841271708723)
                ·
                  refine ⟨26964491310031261907563085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17976327540020841271708723 26964491310031261907563085)
                  ·
                    refine ⟨10111684241261723215336157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26964491310031261907563085 10111684241261723215336157)
                    ·
                      refine ⟨3791881590473146205751059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10111684241261723215336157 3791881590473146205751059)
                      ·
                        rfl

theorem cell23_7384663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_7384663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384663 prefixEnd_7384663 := by exact prefixLift 7384663
  have htrace : WordTrace (prefixWord ++ tailWord_7384663) baseStart_7384663 baseEnd_7384663 := by
    simpa [prefixWord, tailWord_7384663, baseEnd_7384663] using wordTrace_append hprefix tailTrace_7384663
  have hstable : (prefixWord ++ tailWord_7384663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384663).length < 2 ^ (prefixWord ++ tailWord_7384663).sum := by decide
  have hdescent : baseEnd_7384663 < baseStart_7384663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384690 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 3, 3, 2]
def baseStart_7384690 : Nat := 118140960795 + 7384690 * 2 ^ 59
def prefixEnd_7384690 : Nat := 4983230072969 + 3 ^ 40 * 7384690 * 2
def baseEnd_7384690 : Nat := 3791895454450817600113435

theorem tailTrace_7384690 : CollatzResearch.WordTrace tailWord_7384690 prefixEnd_7384690 3791895454450817600113435 := by
  unfold tailWord_7384690
  simp only [CollatzResearch.WordTrace]
  refine ⟨67335442904134202371869881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179561181077691206324986349 67335442904134202371869881)
  ·
    refine ⟨50501582178100651778902411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67335442904134202371869881 50501582178100651778902411)
    ·
      refine ⟨75752373267150977668353617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50501582178100651778902411 75752373267150977668353617)
      ·
        refine ⟨56814279950363233251265213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75752373267150977668353617 56814279950363233251265213)
        ·
          refine ⟨21305354981386212469224455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56814279950363233251265213 21305354981386212469224455)
          ·
            refine ⟨31958032472079318703836683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21305354981386212469224455 31958032472079318703836683)
            ·
              refine ⟨47937048708118978055755025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31958032472079318703836683 47937048708118978055755025)
              ·
                refine ⟨35952786531089233541816269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47937048708118978055755025 35952786531089233541816269)
                ·
                  refine ⟨13482294949158462578181101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35952786531089233541816269 13482294949158462578181101)
                  ·
                    refine ⟨5055860605934423466817913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13482294949158462578181101 5055860605934423466817913)
                    ·
                      refine ⟨3791895454450817600113435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055860605934423466817913 3791895454450817600113435)
                      ·
                        rfl

theorem cell23_7384690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_7384690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384690 prefixEnd_7384690 := by exact prefixLift 7384690
  have htrace : WordTrace (prefixWord ++ tailWord_7384690) baseStart_7384690 baseEnd_7384690 := by
    simpa [prefixWord, tailWord_7384690, baseEnd_7384690] using wordTrace_append hprefix tailTrace_7384690
  have hstable : (prefixWord ++ tailWord_7384690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384690).length < 2 ^ (prefixWord ++ tailWord_7384690).sum := by decide
  have hdescent : baseEnd_7384690 < baseStart_7384690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384716 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_7384716 : Nat := 118140960795 + 7384716 * 2 ^ 59
def prefixEnd_7384716 : Nat := 4983230072969 + 3 ^ 40 * 7384716 * 2
def baseEnd_7384716 : Nat := 3791908804947834498388315

theorem tailTrace_7384716 : CollatzResearch.WordTrace tailWord_7384716 prefixEnd_7384716 3791908804947834498388315 := by
  unfold tailWord_7384716
  simp only [CollatzResearch.WordTrace]
  refine ⟨134671359957221307963963001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179561813276295077285284001 134671359957221307963963001)
  ·
    refine ⟨101003519967915980972972251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134671359957221307963963001 101003519967915980972972251)
    ·
      refine ⟨151505279951873971459458377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101003519967915980972972251 151505279951873971459458377)
      ·
        refine ⟨113628959963905478594593783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151505279951873971459458377 113628959963905478594593783)
        ·
          refine ⟨170443439945858217891890675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113628959963905478594593783 170443439945858217891890675)
          ·
            refine ⟨255665159918787326837836013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170443439945858217891890675 255665159918787326837836013)
            ·
              refine ⟨95874434969545247564188505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255665159918787326837836013 95874434969545247564188505)
              ·
                refine ⟨71905826227158935673141379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95874434969545247564188505 71905826227158935673141379)
                ·
                  refine ⟨107858739340738403509712069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71905826227158935673141379 107858739340738403509712069)
                  ·
                    refine ⟨20223513626388450658071013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107858739340738403509712069 20223513626388450658071013)
                    ·
                      refine ⟨3791908804947834498388315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20223513626388450658071013 3791908804947834498388315)
                      ·
                        rfl

theorem cell23_7384716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_7384716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384716 prefixEnd_7384716 := by exact prefixLift 7384716
  have htrace : WordTrace (prefixWord ++ tailWord_7384716) baseStart_7384716 baseEnd_7384716 := by
    simpa [prefixWord, tailWord_7384716, baseEnd_7384716] using wordTrace_append hprefix tailTrace_7384716
  have hstable : (prefixWord ++ tailWord_7384716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384716).length < 2 ^ (prefixWord ++ tailWord_7384716).sum := by decide
  have hdescent : baseEnd_7384716 < baseStart_7384716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384724 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_7384724 : Nat := 118140960795 + 7384724 * 2 ^ 59
def prefixEnd_7384724 : Nat := 4983230072969 + 3 ^ 40 * 7384724 * 2
def baseEnd_7384724 : Nat := 3791912912793070467088279

theorem tailTrace_7384724 : CollatzResearch.WordTrace tailWord_7384724 prefixEnd_7384724 3791912912793070467088279 := by
  unfold tailWord_7384724
  simp only [CollatzResearch.WordTrace]
  refine ⟨134671505849206816647108613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179562007798942422196144817 134671505849206816647108613)
  ·
    refine ⟨25250907346726278121332865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134671505849206816647108613 25250907346726278121332865)
    ·
      refine ⟨18938180510044708590999649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25250907346726278121332865 18938180510044708590999649)
      ·
        refine ⟨14203635382533531443249737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18938180510044708590999649 14203635382533531443249737)
        ·
          refine ⟨10652726536900148582437303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14203635382533531443249737 10652726536900148582437303)
          ·
            refine ⟨15979089805350222873655955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10652726536900148582437303 15979089805350222873655955)
            ·
              refine ⟨23968634708025334310483933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15979089805350222873655955 23968634708025334310483933)
              ·
                refine ⟨8988238015509500366431475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23968634708025334310483933 8988238015509500366431475)
                ·
                  refine ⟨13482357023264250549647213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8988238015509500366431475 13482357023264250549647213)
                  ·
                    refine ⟨5055883883724093956117705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13482357023264250549647213 5055883883724093956117705)
                    ·
                      refine ⟨3791912912793070467088279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055883883724093956117705 3791912912793070467088279)
                      ·
                        rfl

theorem cell23_7384724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_7384724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384724 prefixEnd_7384724 := by exact prefixLift 7384724
  have htrace : WordTrace (prefixWord ++ tailWord_7384724) baseStart_7384724 baseEnd_7384724 := by
    simpa [prefixWord, tailWord_7384724, baseEnd_7384724] using wordTrace_append hprefix tailTrace_7384724
  have hstable : (prefixWord ++ tailWord_7384724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384724).length < 2 ^ (prefixWord ++ tailWord_7384724).sum := by decide
  have hdescent : baseEnd_7384724 < baseStart_7384724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384737 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 4, 2, 2]
def baseStart_7384737 : Nat := 118140960795 + 7384737 * 2 ^ 59
def prefixEnd_7384737 : Nat := 4983230072969 + 3 ^ 40 * 7384737 * 2
def baseEnd_7384737 : Nat := 3791919588041578916225719

theorem tailTrace_7384737 : CollatzResearch.WordTrace tailWord_7384737 prefixEnd_7384737 3791919588041578916225719 := by
  unfold tailWord_7384737
  simp only [CollatzResearch.WordTrace]
  refine ⟨269343485847366536514440465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179562323898244357676293643 269343485847366536514440465)
  ·
    refine ⟨202007614385524902385830349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269343485847366536514440465 202007614385524902385830349)
    ·
      refine ⟨75752855394571838394686381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202007614385524902385830349 75752855394571838394686381)
      ·
        refine ⟨28407320772964439398007393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75752855394571838394686381 28407320772964439398007393)
        ·
          refine ⟨21305490579723329548505545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28407320772964439398007393 21305490579723329548505545)
          ·
            refine ⟨15979117934792497161379159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21305490579723329548505545 15979117934792497161379159)
            ·
              refine ⟨23968676902188745742068739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15979117934792497161379159 23968676902188745742068739)
              ·
                refine ⟨35953015353283118613103109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23968676902188745742068739 35953015353283118613103109)
                ·
                  refine ⟨6741190378740584739956833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35953015353283118613103109 6741190378740584739956833)
                  ·
                    refine ⟨5055892784055438554967625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6741190378740584739956833 5055892784055438554967625)
                    ·
                      refine ⟨3791919588041578916225719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055892784055438554967625 3791919588041578916225719)
                      ·
                        rfl

theorem cell23_7384737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_7384737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384737 prefixEnd_7384737 := by exact prefixLift 7384737
  have htrace : WordTrace (prefixWord ++ tailWord_7384737) baseStart_7384737 baseEnd_7384737 := by
    simpa [prefixWord, tailWord_7384737, baseEnd_7384737] using wordTrace_append hprefix tailTrace_7384737
  have hstable : (prefixWord ++ tailWord_7384737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384737).length < 2 ^ (prefixWord ++ tailWord_7384737).sum := by decide
  have hdescent : baseEnd_7384737 < baseStart_7384737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384763 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 2, 5, 2]
def baseStart_7384763 : Nat := 118140960795 + 7384763 * 2 ^ 59
def prefixEnd_7384763 : Nat := 4983230072969 + 3 ^ 40 * 7384763 * 2
def baseEnd_7384763 : Nat := 3791932938538595814500599

theorem tailTrace_7384763 : CollatzResearch.WordTrace tailWord_7384763 prefixEnd_7384763 3791932938538595814500599 := by
  unfold tailWord_7384763
  simp only [CollatzResearch.WordTrace]
  refine ⟨269344434145272342954886943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179562956096848228636591295 269344434145272342954886943)
  ·
    refine ⟨404016651217908514432330415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269344434145272342954886943 404016651217908514432330415)
    ·
      refine ⟨606024976826862771648495623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404016651217908514432330415 606024976826862771648495623)
      ·
        refine ⟨909037465240294157472743435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606024976826862771648495623 909037465240294157472743435)
        ·
          refine ⟨1363556197860441236209115153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909037465240294157472743435 1363556197860441236209115153)
          ·
            refine ⟨1022667148395330927156836365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363556197860441236209115153 1022667148395330927156836365)
            ·
              refine ⟨383500180648249097683813637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1022667148395330927156836365 383500180648249097683813637)
              ·
                refine ⟨71906283871546705815715057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383500180648249097683813637 71906283871546705815715057)
                ·
                  refine ⟨53929712903660029361786293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71906283871546705815715057 53929712903660029361786293)
                  ·
                    refine ⟨5055910584718127752667465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53929712903660029361786293 5055910584718127752667465)
                    ·
                      refine ⟨3791932938538595814500599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055910584718127752667465 3791932938538595814500599)
                      ·
                        rfl

theorem cell23_7384763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 5, 2].length) (baseStart_7384763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384763 prefixEnd_7384763 := by exact prefixLift 7384763
  have htrace : WordTrace (prefixWord ++ tailWord_7384763) baseStart_7384763 baseEnd_7384763 := by
    simpa [prefixWord, tailWord_7384763, baseEnd_7384763] using wordTrace_append hprefix tailTrace_7384763
  have hstable : (prefixWord ++ tailWord_7384763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384763).length < 2 ^ (prefixWord ++ tailWord_7384763).sum := by decide
  have hdescent : baseEnd_7384763 < baseStart_7384763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384793 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 4]
def baseStart_7384793 : Nat := 118140960795 + 7384793 * 2 ^ 59
def prefixEnd_7384793 : Nat := 4983230072969 + 3 ^ 40 * 7384793 * 2
def baseEnd_7384793 : Nat := 3791948342958230697125461

theorem tailTrace_7384793 : CollatzResearch.WordTrace tailWord_7384793 prefixEnd_7384793 3791948342958230697125461 := by
  unfold tailWord_7384793
  simp only [CollatzResearch.WordTrace]
  refine ⟨269345528335163658078479033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179563685556775772052319355 269345528335163658078479033)
  ·
    refine ⟨202009146251372743558859275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269345528335163658078479033 202009146251372743558859275)
    ·
      refine ⟨303013719377059115338288913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202009146251372743558859275 303013719377059115338288913)
      ·
        refine ⟨227260289532794336503716685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303013719377059115338288913 227260289532794336503716685)
        ·
          refine ⟨85222608574797876188893757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227260289532794336503716685 85222608574797876188893757)
          ·
            refine ⟨31958478215549203570835159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85222608574797876188893757 31958478215549203570835159)
            ·
              refine ⟨47937717323323805356252739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31958478215549203570835159 47937717323323805356252739)
              ·
                refine ⟨71906575984985708034379109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47937717323323805356252739 71906575984985708034379109)
                ·
                  refine ⟨13482482997184820256446083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71906575984985708034379109 13482482997184820256446083)
                  ·
                    refine ⟨20223724495777230384669125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13482482997184820256446083 20223724495777230384669125)
                    ·
                      refine ⟨3791948342958230697125461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20223724495777230384669125 3791948342958230697125461)
                      ·
                        rfl

theorem cell23_7384793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_7384793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384793 prefixEnd_7384793 := by exact prefixLift 7384793
  have htrace : WordTrace (prefixWord ++ tailWord_7384793) baseStart_7384793 baseEnd_7384793 := by
    simpa [prefixWord, tailWord_7384793, baseEnd_7384793] using wordTrace_append hprefix tailTrace_7384793
  have hstable : (prefixWord ++ tailWord_7384793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384793).length < 2 ^ (prefixWord ++ tailWord_7384793).sum := by decide
  have hdescent : baseEnd_7384793 < baseStart_7384793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384810 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_7384810 : Nat := 118140960795 + 7384810 * 2 ^ 59
def prefixEnd_7384810 : Nat := 4983230072969 + 3 ^ 40 * 7384810 * 2
def baseEnd_7384810 : Nat := 3791957072129357130612883

theorem tailTrace_7384810 : CollatzResearch.WordTrace tailWord_7384810 prefixEnd_7384810 3791957072129357130612883 := by
  unfold tailWord_7384810
  simp only [CollatzResearch.WordTrace]
  refine ⟨67336537094025517495461971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179564098917401379987898589 67336537094025517495461971)
  ·
    refine ⟨101004805641038276243192957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67336537094025517495461971 101004805641038276243192957)
    ·
      refine ⟨37876802115389353591197359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101004805641038276243192957 37876802115389353591197359)
      ·
        refine ⟨56815203173084030386796039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37876802115389353591197359 56815203173084030386796039)
        ·
          refine ⟨85222804759626045580194059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56815203173084030386796039 85222804759626045580194059)
          ·
            refine ⟨127834207139439068370291089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85222804759626045580194059 127834207139439068370291089)
            ·
              refine ⟨95875655354579301277718317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127834207139439068370291089 95875655354579301277718317)
              ·
                refine ⟨35953370757967237979144369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95875655354579301277718317 35953370757967237979144369)
                ·
                  refine ⟨26965028068475428484358277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35953370757967237979144369 26965028068475428484358277)
                  ·
                    refine ⟨5055942762839142840817177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26965028068475428484358277 5055942762839142840817177)
                    ·
                      refine ⟨3791957072129357130612883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5055942762839142840817177 3791957072129357130612883)
                      ·
                        rfl

theorem cell23_7384810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_7384810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384810 prefixEnd_7384810 := by exact prefixLift 7384810
  have htrace : WordTrace (prefixWord ++ tailWord_7384810) baseStart_7384810 baseEnd_7384810 := by
    simpa [prefixWord, tailWord_7384810, baseEnd_7384810] using wordTrace_append hprefix tailTrace_7384810
  have hstable : (prefixWord ++ tailWord_7384810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384810).length < 2 ^ (prefixWord ++ tailWord_7384810).sum := by decide
  have hdescent : baseEnd_7384810 < baseStart_7384810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384816 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 10]
def baseStart_7384816 : Nat := 118140960795 + 7384816 * 2 ^ 59
def prefixEnd_7384816 : Nat := 4983230072969 + 3 ^ 40 * 7384816 * 2
def baseEnd_7384816 : Nat := 421328905890364900793095

theorem tailTrace_7384816 : CollatzResearch.WordTrace tailWord_7384816 prefixEnd_7384816 421328905890364900793095 := by
  unfold tailWord_7384816
  simp only [CollatzResearch.WordTrace]
  refine ⟨134673183607040166503283151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179564244809386888671044201 134673183607040166503283151)
  ·
    refine ⟨202009775410560249754924727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134673183607040166503283151 202009775410560249754924727)
    ·
      refine ⟨303014663115840374632387091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202009775410560249754924727 303014663115840374632387091)
      ·
        refine ⟨454521994673760561948580637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303014663115840374632387091 454521994673760561948580637)
        ·
          refine ⟨170445748002660210730717739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454521994673760561948580637 170445748002660210730717739)
          ·
            refine ⟨255668622003990316096076609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170445748002660210730717739 255668622003990316096076609)
            ·
              refine ⟨191751466502992737072057457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255668622003990316096076609 191751466502992737072057457)
              ·
                refine ⟨143813599877244552804043093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191751466502992737072057457 143813599877244552804043093)
                ·
                  refine ⟨421328905890364900793095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 143813599877244552804043093 421328905890364900793095)
                  ·
                    rfl

theorem cell23_7384816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 10].length) (baseStart_7384816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384816 prefixEnd_7384816 := by exact prefixLift 7384816
  have htrace : WordTrace (prefixWord ++ tailWord_7384816) baseStart_7384816 baseEnd_7384816 := by
    simpa [prefixWord, tailWord_7384816, baseEnd_7384816] using wordTrace_append hprefix tailTrace_7384816
  have hstable : (prefixWord ++ tailWord_7384816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384816).length < 2 ^ (prefixWord ++ tailWord_7384816).sum := by decide
  have hdescent : baseEnd_7384816 < baseStart_7384816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384845 : List Nat := [1, 7, 2, 1, 1, 2, 2, 2, 5]
def baseStart_7384845 : Nat := 118140960795 + 7384845 * 2 ^ 59
def prefixEnd_7384845 : Nat := 4983230072969 + 3 ^ 40 * 7384845 * 2
def baseEnd_7384845 : Nat := 421330560439140499297247

theorem tailTrace_7384845 : CollatzResearch.WordTrace tailWord_7384845 prefixEnd_7384845 421330560439140499297247 := by
  unfold tailWord_7384845
  simp only [CollatzResearch.WordTrace]
  refine ⟨269347424930975270959371989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179564949953983513972914659 269347424930975270959371989)
  ·
    refine ⟨6312830271819732913110281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 269347424930975270959371989 6312830271819732913110281)
    ·
      refine ⟨4734622703864799684832711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6312830271819732913110281 4734622703864799684832711)
      ·
        refine ⟨7101934055797199527249067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734622703864799684832711 7101934055797199527249067)
        ·
          refine ⟨10652901083695799290873601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101934055797199527249067 10652901083695799290873601)
          ·
            refine ⟨7989675812771849468155201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10652901083695799290873601 7989675812771849468155201)
            ·
              refine ⟨5992256859578887101116401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7989675812771849468155201 5992256859578887101116401)
              ·
                refine ⟨4494192644684165325837301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5992256859578887101116401 4494192644684165325837301)
                ·
                  refine ⟨421330560439140499297247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4494192644684165325837301 421330560439140499297247)
                  ·
                    rfl

theorem cell23_7384845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_7384845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384845 prefixEnd_7384845 := by exact prefixLift 7384845
  have htrace : WordTrace (prefixWord ++ tailWord_7384845) baseStart_7384845 baseEnd_7384845 := by
    simpa [prefixWord, tailWord_7384845, baseEnd_7384845] using wordTrace_append hprefix tailTrace_7384845
  have hstable : (prefixWord ++ tailWord_7384845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384845).length < 2 ^ (prefixWord ++ tailWord_7384845).sum := by decide
  have hdescent : baseEnd_7384845 < baseStart_7384845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384863 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 5, 5]
def baseStart_7384863 : Nat := 118140960795 + 7384863 * 2 ^ 59
def prefixEnd_7384863 : Nat := 4983230072969 + 3 ^ 40 * 7384863 * 2
def baseEnd_7384863 : Nat := 1263994762201348474416713

theorem tailTrace_7384863 : CollatzResearch.WordTrace tailWord_7384863 prefixEnd_7384863 1263994762201348474416713 := by
  unfold tailWord_7384863
  simp only [CollatzResearch.WordTrace]
  refine ⟨269348081444910060033527243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179565387629940040022351495 269348081444910060033527243)
  ·
    refine ⟨404022122167365090050290865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269348081444910060033527243 404022122167365090050290865)
    ·
      refine ⟨303016591625523817537718149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404022122167365090050290865 303016591625523817537718149)
      ·
        refine ⟨56815610929785715788322153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303016591625523817537718149 56815610929785715788322153)
        ·
          refine ⟨42611708197339286841241615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56815610929785715788322153 42611708197339286841241615)
          ·
            refine ⟨63917562296008930261862423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42611708197339286841241615 63917562296008930261862423)
            ·
              refine ⟨95876343444013395392793635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63917562296008930261862423 95876343444013395392793635)
              ·
                refine ⟨143814515166020093089190453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95876343444013395392793635 143814515166020093089190453)
                ·
                  refine ⟨13482610796814383727111605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143814515166020093089190453 13482610796814383727111605)
                  ·
                    refine ⟨1263994762201348474416713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13482610796814383727111605 1263994762201348474416713)
                    ·
                      rfl

theorem cell23_7384863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_7384863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384863 prefixEnd_7384863 := by exact prefixLift 7384863
  have htrace : WordTrace (prefixWord ++ tailWord_7384863) baseStart_7384863 baseEnd_7384863 := by
    simpa [prefixWord, tailWord_7384863, baseEnd_7384863] using wordTrace_append hprefix tailTrace_7384863
  have hstable : (prefixWord ++ tailWord_7384863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384863).length < 2 ^ (prefixWord ++ tailWord_7384863).sum := by decide
  have hdescent : baseEnd_7384863 < baseStart_7384863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384940 : List Nat := [2, 2, 1, 1, 4, 2, 4, 7]
def baseStart_7384940 : Nat := 118140960795 + 7384940 * 2 ^ 59
def prefixEnd_7384940 : Nat := 4983230072969 + 3 ^ 40 * 7384940 * 2
def baseEnd_7384940 : Nat := 140445326837571911925455

theorem tailTrace_7384940 : CollatzResearch.WordTrace tailWord_7384940 prefixEnd_7384940 140445326837571911925455 := by
  unfold tailWord_7384940
  simp only [CollatzResearch.WordTrace]
  refine ⟨134675444932815551092040137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179567259910420734789386849 134675444932815551092040137)
  ·
    refine ⟨101006583699611663319030103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134675444932815551092040137 101006583699611663319030103)
    ·
      refine ⟨151509875549417494978545155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101006583699611663319030103 151509875549417494978545155)
      ·
        refine ⟨227264813324126242467817733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151509875549417494978545155 227264813324126242467817733)
        ·
          refine ⟨42612152498273670462715825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227264813324126242467817733 42612152498273670462715825)
          ·
            refine ⟨31959114373705252847036869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42612152498273670462715825 31959114373705252847036869)
            ·
              refine ⟨5992333945069734908819413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31959114373705252847036869 5992333945069734908819413)
              ·
                refine ⟨140445326837571911925455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5992333945069734908819413 140445326837571911925455)
                ·
                  rfl

theorem cell23_7384940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 7].length) (baseStart_7384940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384940 prefixEnd_7384940 := by exact prefixLift 7384940
  have htrace : WordTrace (prefixWord ++ tailWord_7384940) baseStart_7384940 baseEnd_7384940 := by
    simpa [prefixWord, tailWord_7384940, baseEnd_7384940] using wordTrace_append hprefix tailTrace_7384940
  have hstable : (prefixWord ++ tailWord_7384940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384940).length < 2 ^ (prefixWord ++ tailWord_7384940).sum := by decide
  have hdescent : baseEnd_7384940 < baseStart_7384940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7384968 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 3, 2, 2]
def baseStart_7384968 : Nat := 118140960795 + 7384968 * 2 ^ 59
def prefixEnd_7384968 : Nat := 4983230072969 + 3 ^ 40 * 7384968 * 2
def baseEnd_7384968 : Nat := 3792038202072767512437157

theorem tailTrace_7384968 : CollatzResearch.WordTrace tailWord_7384968 prefixEnd_7384968 3792038202072767512437157 := by
  unfold tailWord_7384968
  simp only [CollatzResearch.WordTrace]
  refine ⟨134675955554764831483049779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179567940739686441977399705 134675955554764831483049779)
  ·
    refine ⟨202013933332147247224574669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134675955554764831483049779 202013933332147247224574669)
    ·
      refine ⟨75755224999555217709215501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202013933332147247224574669 75755224999555217709215501)
      ·
        refine ⟨28408209374833206640955813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75755224999555217709215501 28408209374833206640955813)
        ·
          refine ⟨5326539257781226245179215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28408209374833206640955813 5326539257781226245179215)
          ·
            refine ⟨7989808886671839367768823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326539257781226245179215 7989808886671839367768823)
            ·
              refine ⟨11984713330007759051653235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7989808886671839367768823 11984713330007759051653235)
              ·
                refine ⟨17977069995011638577479853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11984713330007759051653235 17977069995011638577479853)
                ·
                  refine ⟨6741401248129364466554945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17977069995011638577479853 6741401248129364466554945)
                  ·
                    refine ⟨5056050936097023349916209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6741401248129364466554945 5056050936097023349916209)
                    ·
                      refine ⟨3792038202072767512437157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056050936097023349916209 3792038202072767512437157)
                      ·
                        rfl

theorem cell23_7384968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_7384968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7384968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7384968 prefixEnd_7384968 := by exact prefixLift 7384968
  have htrace : WordTrace (prefixWord ++ tailWord_7384968) baseStart_7384968 baseEnd_7384968 := by
    simpa [prefixWord, tailWord_7384968, baseEnd_7384968] using wordTrace_append hprefix tailTrace_7384968
  have hstable : (prefixWord ++ tailWord_7384968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7384968).length < 2 ^ (prefixWord ++ tailWord_7384968).sum := by decide
  have hdescent : baseEnd_7384968 < baseStart_7384968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7384968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385007 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 1, 4, 2]
def baseStart_7385007 : Nat := 118140960795 + 7385007 * 2 ^ 59
def prefixEnd_7385007 : Nat := 4983230072969 + 3 ^ 40 * 7385007 * 2
def baseEnd_7385007 : Nat := 3792058227818292859849477

theorem tailTrace_7385007 : CollatzResearch.WordTrace tailWord_7385007 prefixEnd_7385007 3792058227818292859849477 := by
  unfold tailWord_7385007
  simp only [CollatzResearch.WordTrace]
  refine ⟨269353333556388372626769275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179568889037592248417846183 269353333556388372626769275)
  ·
    refine ⟨404030000334582558940153913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269353333556388372626769275 404030000334582558940153913)
    ·
      refine ⟨303022500250936919205115435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404030000334582558940153913 303022500250936919205115435)
      ·
        refine ⟨454533750376405378807673153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303022500250936919205115435 454533750376405378807673153)
        ·
          refine ⟨340900312782304034105754865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454533750376405378807673153 340900312782304034105754865)
          ·
            refine ⟨255675234586728025579316149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340900312782304034105754865 255675234586728025579316149)
            ·
              refine ⟨23969553242505752398060889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255675234586728025579316149 23969553242505752398060889)
              ·
                refine ⟨17977164931879314298545667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23969553242505752398060889 17977164931879314298545667)
                ·
                  refine ⟨26965747397818971447818501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17977164931879314298545667 26965747397818971447818501)
                  ·
                    refine ⟨5056077637091057146465969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26965747397818971447818501 5056077637091057146465969)
                    ·
                      refine ⟨3792058227818292859849477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056077637091057146465969 3792058227818292859849477)
                      ·
                        rfl

theorem cell23_7385007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 4, 2].length) (baseStart_7385007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385007 prefixEnd_7385007 := by exact prefixLift 7385007
  have htrace : WordTrace (prefixWord ++ tailWord_7385007) baseStart_7385007 baseEnd_7385007 := by
    simpa [prefixWord, tailWord_7385007, baseEnd_7385007] using wordTrace_append hprefix tailTrace_7385007
  have hstable : (prefixWord ++ tailWord_7385007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385007).length < 2 ^ (prefixWord ++ tailWord_7385007).sum := by decide
  have hdescent : baseEnd_7385007 < baseStart_7385007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385010 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_7385010 : Nat := 118140960795 + 7385010 * 2 ^ 59
def prefixEnd_7385010 : Nat := 4983230072969 + 3 ^ 40 * 7385010 * 2
def baseEnd_7385010 : Nat := 3792059768260256348111963

theorem tailTrace_7385010 : CollatzResearch.WordTrace tailWord_7385010 prefixEnd_7385010 3792059768260256348111963 := by
  unfold tailWord_7385010
  simp only [CollatzResearch.WordTrace]
  refine ⟨67338360743844376034782121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179568961983585002759418989 67338360743844376034782121)
  ·
    refine ⟨50503770557883282026086591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67338360743844376034782121 50503770557883282026086591)
    ·
      refine ⟨75755655836824923039129887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50503770557883282026086591 75755655836824923039129887)
      ·
        refine ⟨113633483755237384558694831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75755655836824923039129887 113633483755237384558694831)
        ·
          refine ⟨170450225632856076838042247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113633483755237384558694831 170450225632856076838042247)
          ·
            refine ⟨255675338449284115257063371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170450225632856076838042247 255675338449284115257063371)
            ·
              refine ⟨383513007673926172885595057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255675338449284115257063371 383513007673926172885595057)
              ·
                refine ⟨287634755755444629664196293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383513007673926172885595057 287634755755444629664196293)
                ·
                  refine ⟨53931516704145868062036805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287634755755444629664196293 53931516704145868062036805)
                  ·
                    refine ⟨10112159382027350261631901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53931516704145868062036805 10112159382027350261631901)
                    ·
                      refine ⟨3792059768260256348111963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10112159382027350261631901 3792059768260256348111963)
                      ·
                        rfl

theorem cell23_7385010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_7385010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385010 prefixEnd_7385010 := by exact prefixLift 7385010
  have htrace : WordTrace (prefixWord ++ tailWord_7385010) baseStart_7385010 baseEnd_7385010 := by
    simpa [prefixWord, tailWord_7385010, baseEnd_7385010] using wordTrace_append hprefix tailTrace_7385010
  have hstable : (prefixWord ++ tailWord_7385010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385010).length < 2 ^ (prefixWord ++ tailWord_7385010).sum := by decide
  have hdescent : baseEnd_7385010 < baseStart_7385010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385040 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 3]
def baseStart_7385040 : Nat := 118140960795 + 7385040 * 2 ^ 59
def prefixEnd_7385040 : Nat := 4983230072969 + 3 ^ 40 * 7385040 * 2
def baseEnd_7385040 : Nat := 3792075172679891230736825

theorem tailTrace_7385040 : CollatzResearch.WordTrace tailWord_7385040 prefixEnd_7385040 3792075172679891230736825 := by
  unfold tailWord_7385040
  simp only [CollatzResearch.WordTrace]
  refine ⟨134677268582634409631360287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179569691443512546175147049 134677268582634409631360287)
  ·
    refine ⟨202015902873951614447040431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134677268582634409631360287 202015902873951614447040431)
    ·
      refine ⟨303023854310927421670560647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202015902873951614447040431 303023854310927421670560647)
      ·
        refine ⟨454535781466391132505840971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303023854310927421670560647 454535781466391132505840971)
        ·
          refine ⟨681803672199586698758761457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454535781466391132505840971 681803672199586698758761457)
          ·
            refine ⟨511352754149690024069071093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681803672199586698758761457 511352754149690024069071093)
            ·
              refine ⟨47939320701533439756475415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 511352754149690024069071093 47939320701533439756475415)
              ·
                refine ⟨71908981052300159634713123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47939320701533439756475415 71908981052300159634713123)
                ·
                  refine ⟨107863471578450239452069685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71908981052300159634713123 107863471578450239452069685)
                  ·
                    refine ⟨10112200460479709948631533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107863471578450239452069685 10112200460479709948631533)
                    ·
                      refine ⟨3792075172679891230736825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10112200460479709948631533 3792075172679891230736825)
                      ·
                        rfl

theorem cell23_7385040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 3].length) (baseStart_7385040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385040 prefixEnd_7385040 := by exact prefixLift 7385040
  have htrace : WordTrace (prefixWord ++ tailWord_7385040) baseStart_7385040 baseEnd_7385040 := by
    simpa [prefixWord, tailWord_7385040, baseEnd_7385040] using wordTrace_append hprefix tailTrace_7385040
  have hstable : (prefixWord ++ tailWord_7385040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385040).length < 2 ^ (prefixWord ++ tailWord_7385040).sum := by decide
  have hdescent : baseEnd_7385040 < baseStart_7385040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385060 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_7385060 : Nat := 118140960795 + 7385060 * 2 ^ 59
def prefixEnd_7385060 : Nat := 4983230072969 + 3 ^ 40 * 7385060 * 2
def baseEnd_7385060 : Nat := 1264028480764327050828911

theorem tailTrace_7385060 : CollatzResearch.WordTrace tailWord_7385060 prefixEnd_7385060 1264028480764327050828911 := by
  unfold tailWord_7385060
  simp only [CollatzResearch.WordTrace]
  refine ⟨134677633312598181339224317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179570177750130908452299089 134677633312598181339224317)
  ·
    refine ⟨50504112492224318002209119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134677633312598181339224317 50504112492224318002209119)
    ·
      refine ⟨75756168738336477003313679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50504112492224318002209119 75756168738336477003313679)
      ·
        refine ⟨113634253107504715504970519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75756168738336477003313679 113634253107504715504970519)
        ·
          refine ⟨170451379661257073257455779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113634253107504715504970519 170451379661257073257455779)
          ·
            refine ⟨255677069491885609886183669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170451379661257073257455779 255677069491885609886183669)
            ·
              refine ⟨23969725264864275926829719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255677069491885609886183669 23969725264864275926829719)
              ·
                refine ⟨35954587897296413890244579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23969725264864275926829719 35954587897296413890244579)
                ·
                  refine ⟨53931881845944620835366869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35954587897296413890244579 53931881845944620835366869)
                  ·
                    refine ⟨1264028480764327050828911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53931881845944620835366869 1264028480764327050828911)
                    ·
                      rfl

theorem cell23_7385060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_7385060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385060 prefixEnd_7385060 := by exact prefixLift 7385060
  have htrace : WordTrace (prefixWord ++ tailWord_7385060) baseStart_7385060 baseEnd_7385060 := by
    simpa [prefixWord, tailWord_7385060, baseEnd_7385060] using wordTrace_append hprefix tailTrace_7385060
  have hstable : (prefixWord ++ tailWord_7385060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385060).length < 2 ^ (prefixWord ++ tailWord_7385060).sum := by decide
  have hdescent : baseEnd_7385060 < baseStart_7385060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385107 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 3, 4]
def baseStart_7385107 : Nat := 118140960795 + 7385107 * 2 ^ 59
def prefixEnd_7385107 : Nat := 4983230072969 + 3 ^ 40 * 7385107 * 2
def baseEnd_7385107 : Nat := 1264036525294580822866339

theorem tailTrace_7385107 : CollatzResearch.WordTrace tailWord_7385107 prefixEnd_7385107 1264036525294580822866339 := by
  unfold tailWord_7385107
  simp only [CollatzResearch.WordTrace]
  refine ⟨269356980856026089705409575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179571320570684059803606383 269356980856026089705409575)
  ·
    refine ⟨404035471284039134558114363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269356980856026089705409575 404035471284039134558114363)
    ·
      refine ⟨606053206926058701837171545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404035471284039134558114363 606053206926058701837171545)
      ·
        refine ⟨454539905194544026377878659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606053206926058701837171545 454539905194544026377878659)
        ·
          refine ⟨681809857791816039566817989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454539905194544026377878659 681809857791816039566817989)
          ·
            refine ⟨127839348335965507418778373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 681809857791816039566817989 127839348335965507418778373)
            ·
              refine ⟨23969877812993532641020945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127839348335965507418778373 23969877812993532641020945)
              ·
                refine ⟨17977408359745149480765709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23969877812993532641020945 17977408359745149480765709)
                ·
                  refine ⟨6741528134904431055287141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17977408359745149480765709 6741528134904431055287141)
                  ·
                    refine ⟨1264036525294580822866339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6741528134904431055287141 1264036525294580822866339)
                    ·
                      rfl

theorem cell23_7385107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 4].length) (baseStart_7385107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385107 prefixEnd_7385107 := by exact prefixLift 7385107
  have htrace : WordTrace (prefixWord ++ tailWord_7385107) baseStart_7385107 baseEnd_7385107 := by
    simpa [prefixWord, tailWord_7385107, baseEnd_7385107] using wordTrace_append hprefix tailTrace_7385107
  have hstable : (prefixWord ++ tailWord_7385107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385107).length < 2 ^ (prefixWord ++ tailWord_7385107).sum := by decide
  have hdescent : baseEnd_7385107 < baseStart_7385107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385134 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_7385134 : Nat := 118140960795 + 7385134 * 2 ^ 59
def prefixEnd_7385134 : Nat := 4983230072969 + 3 ^ 40 * 7385134 * 2
def baseEnd_7385134 : Nat := 3792123439861413862961393

theorem tailTrace_7385134 : CollatzResearch.WordTrace tailWord_7385134 prefixEnd_7385134 3792123439861413862961393 := by
  unfold tailWord_7385134
  simp only [CollatzResearch.WordTrace]
  refine ⟨33669745703366034164580307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179571977084618848877761637 33669745703366034164580307)
  ·
    refine ⟨50504618555049051246870461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33669745703366034164580307 50504618555049051246870461)
    ·
      refine ⟨18939231958143394217576423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50504618555049051246870461 18939231958143394217576423)
      ·
        refine ⟨28408847937215091326364635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18939231958143394217576423 28408847937215091326364635)
        ·
          refine ⟨42613271905822636989546953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28408847937215091326364635 42613271905822636989546953)
          ·
            refine ⟨31959953929366977742160215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42613271905822636989546953 31959953929366977742160215)
            ·
              refine ⟨47939930894050466613240323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31959953929366977742160215 47939930894050466613240323)
              ·
                refine ⟨71909896341075699919860485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47939930894050466613240323 71909896341075699919860485)
                ·
                  refine ⟨13483105563951693734973841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71909896341075699919860485 13483105563951693734973841)
                  ·
                    refine ⟨10112329172963770301230381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13483105563951693734973841 10112329172963770301230381)
                    ·
                      refine ⟨3792123439861413862961393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10112329172963770301230381 3792123439861413862961393)
                      ·
                        rfl

theorem cell23_7385134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_7385134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385134 prefixEnd_7385134 := by exact prefixLift 7385134
  have htrace : WordTrace (prefixWord ++ tailWord_7385134) baseStart_7385134 baseEnd_7385134 := by
    simpa [prefixWord, tailWord_7385134, baseEnd_7385134] using wordTrace_append hprefix tailTrace_7385134
  have hstable : (prefixWord ++ tailWord_7385134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385134).length < 2 ^ (prefixWord ++ tailWord_7385134).sum := by decide
  have hdescent : baseEnd_7385134 < baseStart_7385134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385160 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_7385160 : Nat := 118140960795 + 7385160 * 2 ^ 59
def prefixEnd_7385160 : Nat := 4983230072969 + 3 ^ 40 * 7385160 * 2
def baseEnd_7385160 : Nat := 3792136790358430761236273

theorem tailTrace_7385160 : CollatzResearch.WordTrace tailWord_7385160 prefixEnd_7385160 3792136790358430761236273 := by
  unfold tailWord_7385160
  simp only [CollatzResearch.WordTrace]
  refine ⟨134679456962417039878544467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179572609283222719838059289 134679456962417039878544467)
  ·
    refine ⟨202019185443625559817816701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134679456962417039878544467 202019185443625559817816701)
    ·
      refine ⟨75757194541359584931681263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202019185443625559817816701 75757194541359584931681263)
      ·
        refine ⟨113635791812039377397521895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75757194541359584931681263 113635791812039377397521895)
        ·
          refine ⟨170453687718059066096282843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113635791812039377397521895 170453687718059066096282843)
          ·
            refine ⟨255680531577088599144424265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170453687718059066096282843 255680531577088599144424265)
            ·
              refine ⟨191760398682816449358318199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255680531577088599144424265 191760398682816449358318199)
              ·
                refine ⟨287640598024224674037477299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191760398682816449358318199 287640598024224674037477299)
                ·
                  refine ⟨431460897036337011056215949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287640598024224674037477299 431460897036337011056215949)
                  ·
                    refine ⟨161797836388626379146080981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 431460897036337011056215949 161797836388626379146080981)
                    ·
                      refine ⟨3792136790358430761236273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161797836388626379146080981 3792136790358430761236273)
                      ·
                        rfl

theorem cell23_7385160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_7385160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385160 prefixEnd_7385160 := by exact prefixLift 7385160
  have htrace : WordTrace (prefixWord ++ tailWord_7385160) baseStart_7385160 baseEnd_7385160 := by
    simpa [prefixWord, tailWord_7385160, baseEnd_7385160] using wordTrace_append hprefix tailTrace_7385160
  have hstable : (prefixWord ++ tailWord_7385160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385160).length < 2 ^ (prefixWord ++ tailWord_7385160).sum := by decide
  have hdescent : baseEnd_7385160 < baseStart_7385160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385164 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 3, 1, 3]
def baseStart_7385164 : Nat := 118140960795 + 7385164 * 2 ^ 59
def prefixEnd_7385164 : Nat := 4983230072969 + 3 ^ 40 * 7385164 * 2
def baseEnd_7385164 : Nat := 3792138844281048745586255

theorem tailTrace_7385164 : CollatzResearch.WordTrace tailWord_7385164 prefixEnd_7385164 3792138844281048745586255 := by
  unfold tailWord_7385164
  simp only [CollatzResearch.WordTrace]
  refine ⟨134679529908409794220117273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179572706544546392293489697 134679529908409794220117273)
  ·
    refine ⟨101009647431307345665087955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134679529908409794220117273 101009647431307345665087955)
    ·
      refine ⟨151514471146961018497631933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101009647431307345665087955 151514471146961018497631933)
      ·
        refine ⟨56817926680110381936611975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151514471146961018497631933 56817926680110381936611975)
        ·
          refine ⟨85226890020165572904917963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56817926680110381936611975 85226890020165572904917963)
          ·
            refine ⟨127840335030248359357376945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85226890020165572904917963 127840335030248359357376945)
            ·
              refine ⟨95880251272686269518032709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127840335030248359357376945 95880251272686269518032709)
              ·
                refine ⟨17977547113628675534631133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95880251272686269518032709 17977547113628675534631133)
                ·
                  refine ⟨6741580167610753325486675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17977547113628675534631133 6741580167610753325486675)
                  ·
                    refine ⟨10112370251416129988230013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6741580167610753325486675 10112370251416129988230013)
                    ·
                      refine ⟨3792138844281048745586255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10112370251416129988230013 3792138844281048745586255)
                      ·
                        rfl

theorem cell23_7385164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_7385164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385164 prefixEnd_7385164 := by exact prefixLift 7385164
  have htrace : WordTrace (prefixWord ++ tailWord_7385164) baseStart_7385164 baseEnd_7385164 := by
    simpa [prefixWord, tailWord_7385164, baseEnd_7385164] using wordTrace_append hprefix tailTrace_7385164
  have hstable : (prefixWord ++ tailWord_7385164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385164).length < 2 ^ (prefixWord ++ tailWord_7385164).sum := by decide
  have hdescent : baseEnd_7385164 < baseStart_7385164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385197 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_7385197 : Nat := 118140960795 + 7385197 * 2 ^ 59
def prefixEnd_7385197 : Nat := 4983230072969 + 3 ^ 40 * 7385197 * 2
def baseEnd_7385197 : Nat := 1264051929714215705491201

theorem tailTrace_7385197 : CollatzResearch.WordTrace tailWord_7385197 prefixEnd_7385197 1264051929714215705491201 := by
  unfold tailWord_7385197
  simp only [CollatzResearch.WordTrace]
  refine ⟨269360263425700035076185845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179573508950466690050790563 269360263425700035076185845)
  ·
    refine ⟨25252524696159378288392423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269360263425700035076185845 25252524696159378288392423)
    ·
      refine ⟨37878787044239067432588635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25252524696159378288392423 37878787044239067432588635)
      ·
        refine ⟨56818180566358601148882953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37878787044239067432588635 56818180566358601148882953)
        ·
          refine ⟨42613635424768950861662215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56818180566358601148882953 42613635424768950861662215)
          ·
            refine ⟨63920453137153426292493323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42613635424768950861662215 63920453137153426292493323)
            ·
              refine ⟨95880679705730139438739985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63920453137153426292493323 95880679705730139438739985)
              ·
                refine ⟨71910509779297604579054989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95880679705730139438739985 71910509779297604579054989)
                ·
                  refine ⟨26966441167236601717145621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71910509779297604579054989 26966441167236601717145621)
                  ·
                    refine ⟨1264051929714215705491201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26966441167236601717145621 1264051929714215705491201)
                    ·
                      rfl

theorem cell23_7385197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_7385197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385197 prefixEnd_7385197 := by exact prefixLift 7385197
  have htrace : WordTrace (prefixWord ++ tailWord_7385197) baseStart_7385197 baseEnd_7385197 := by
    simpa [prefixWord, tailWord_7385197, baseEnd_7385197] using wordTrace_append hprefix tailTrace_7385197
  have hstable : (prefixWord ++ tailWord_7385197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385197).length < 2 ^ (prefixWord ++ tailWord_7385197).sum := by decide
  have hdescent : baseEnd_7385197 < baseStart_7385197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385198 : List Nat := [4, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_7385198 : Nat := 118140960795 + 7385198 * 2 ^ 59
def prefixEnd_7385198 : Nat := 4983230072969 + 3 ^ 40 * 7385198 * 2
def baseEnd_7385198 : Nat := 3792156302623301612561099

theorem tailTrace_7385198 : CollatzResearch.WordTrace tailWord_7385198 prefixEnd_7385198 3792156302623301612561099 := by
  unfold tailWord_7385198
  simp only [CollatzResearch.WordTrace]
  refine ⟨33670037487337051530871531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179573533265797608164648165 33670037487337051530871531)
  ·
    refine ⟨50505056231005577296307297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33670037487337051530871531 50505056231005577296307297)
    ·
      refine ⟨37878792173254182972230473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50505056231005577296307297 37878792173254182972230473)
      ·
        refine ⟨28409094129940637229172855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37878792173254182972230473 28409094129940637229172855)
        ·
          refine ⟨42613641194910955843759283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28409094129940637229172855 42613641194910955843759283)
          ·
            refine ⟨63920461792366433765638925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42613641194910955843759283 63920461792366433765638925)
            ·
              refine ⟨23970173172137412662114597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63920461792366433765638925 23970173172137412662114597)
              ·
                refine ⟨4494407469775764874146487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23970173172137412662114597 4494407469775764874146487)
                ·
                  refine ⟨6741611204663647311219731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4494407469775764874146487 6741611204663647311219731)
                  ·
                    refine ⟨10112416806995470966829597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6741611204663647311219731 10112416806995470966829597)
                    ·
                      refine ⟨3792156302623301612561099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10112416806995470966829597 3792156302623301612561099)
                      ·
                        rfl

theorem cell23_7385198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_7385198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385198 prefixEnd_7385198 := by exact prefixLift 7385198
  have htrace : WordTrace (prefixWord ++ tailWord_7385198) baseStart_7385198 baseEnd_7385198 := by
    simpa [prefixWord, tailWord_7385198, baseEnd_7385198] using wordTrace_append hprefix tailTrace_7385198
  have hstable : (prefixWord ++ tailWord_7385198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385198).length < 2 ^ (prefixWord ++ tailWord_7385198).sum := by decide
  have hdescent : baseEnd_7385198 < baseStart_7385198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385221 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 5, 2, 2]
def baseStart_7385221 : Nat := 118140960795 + 7385221 * 2 ^ 59
def prefixEnd_7385221 : Nat := 4983230072969 + 3 ^ 40 * 7385221 * 2
def baseEnd_7385221 : Nat := 3792168112678355022573493

theorem tailTrace_7385221 : CollatzResearch.WordTrace tailWord_7385221 prefixEnd_7385221 3792168112678355022573493 := by
  unfold tailWord_7385221
  simp only [CollatzResearch.WordTrace]
  refine ⟨269361138777613087175059517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179574092518408724783373011 269361138777613087175059517)
  ·
    refine ⟨101010427041604907690647319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269361138777613087175059517 101010427041604907690647319)
    ·
      refine ⟨151515640562407361535970979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101010427041604907690647319 151515640562407361535970979)
      ·
        refine ⟨227273460843611042303956469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151515640562407361535970979 227273460843611042303956469)
        ·
          refine ⟨21306886954088535215995919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227273460843611042303956469 21306886954088535215995919)
          ·
            refine ⟨31960330431132802823993879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21306886954088535215995919 31960330431132802823993879)
            ·
              refine ⟨47940495646699204235990819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31960330431132802823993879 47940495646699204235990819)
              ·
                refine ⟨71910743470048806353986229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47940495646699204235990819 71910743470048806353986229)
                ·
                  refine ⟨6741632200317075595686209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71910743470048806353986229 6741632200317075595686209)
                  ·
                    refine ⟨5056224150237806696764657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6741632200317075595686209 5056224150237806696764657)
                    ·
                      refine ⟨3792168112678355022573493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056224150237806696764657 3792168112678355022573493)
                      ·
                        rfl

theorem cell23_7385221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_7385221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385221 prefixEnd_7385221 := by exact prefixLift 7385221
  have htrace : WordTrace (prefixWord ++ tailWord_7385221) baseStart_7385221 baseEnd_7385221 := by
    simpa [prefixWord, tailWord_7385221, baseEnd_7385221] using wordTrace_append hprefix tailTrace_7385221
  have hstable : (prefixWord ++ tailWord_7385221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385221).length < 2 ^ (prefixWord ++ tailWord_7385221).sum := by decide
  have hdescent : baseEnd_7385221 < baseStart_7385221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385234 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_7385234 : Nat := 118140960795 + 7385234 * 2 ^ 59
def prefixEnd_7385234 : Nat := 4983230072969 + 3 ^ 40 * 7385234 * 2
def baseEnd_7385234 : Nat := 3792174787926863471710933

theorem tailTrace_7385234 : CollatzResearch.WordTrace tailWord_7385234 prefixEnd_7385234 3792174787926863471710933 := by
  unfold tailWord_7385234
  simp only [CollatzResearch.WordTrace]
  refine ⟨67340403231641497598820689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179574408617710660263521837 67340403231641497598820689)
  ·
    refine ⟨50505302423731123199115517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67340403231641497598820689 50505302423731123199115517)
    ·
      refine ⟨18939488408899171199668319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50505302423731123199115517 18939488408899171199668319)
      ·
        refine ⟨28409232613348756799502479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18939488408899171199668319 28409232613348756799502479)
        ·
          refine ⟨42613848920023135199253719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28409232613348756799502479 42613848920023135199253719)
          ·
            refine ⟨63920773380034702798880579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42613848920023135199253719 63920773380034702798880579)
            ·
              refine ⟨95881160070052054198320869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63920773380034702798880579 95881160070052054198320869)
              ·
                refine ⟨17977717513134760162185163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95881160070052054198320869 17977717513134760162185163)
                ·
                  refine ⟨26966576269702140243277745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17977717513134760162185163 26966576269702140243277745)
                  ·
                    refine ⟨20224932202276605182458309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26966576269702140243277745 20224932202276605182458309)
                    ·
                      refine ⟨3792174787926863471710933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20224932202276605182458309 3792174787926863471710933)
                      ·
                        rfl

theorem cell23_7385234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_7385234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385234 prefixEnd_7385234 := by exact prefixLift 7385234
  have htrace : WordTrace (prefixWord ++ tailWord_7385234) baseStart_7385234 baseEnd_7385234 := by
    simpa [prefixWord, tailWord_7385234, baseEnd_7385234] using wordTrace_append hprefix tailTrace_7385234
  have hstable : (prefixWord ++ tailWord_7385234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385234).length < 2 ^ (prefixWord ++ tailWord_7385234).sum := by decide
  have hdescent : baseEnd_7385234 < baseStart_7385234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385255 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_7385255 : Nat := 118140960795 + 7385255 * 2 ^ 59
def prefixEnd_7385255 : Nat := 4983230072969 + 3 ^ 40 * 7385255 * 2
def baseEnd_7385255 : Nat := 3792185571020607889548337

theorem tailTrace_7385255 : CollatzResearch.WordTrace tailWord_7385255 prefixEnd_7385255 3792185571020607889548337 := by
  unfold tailWord_7385255
  simp only [CollatzResearch.WordTrace]
  refine ⟨269362378859489910981797219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179574919239659940654531479 269362378859489910981797219)
  ·
    refine ⟨404043568289234866472695829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269362378859489910981797219 404043568289234866472695829)
    ·
      refine ⟨18939542263557884365907617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 404043568289234866472695829 18939542263557884365907617)
      ·
        refine ⟨14204656697668413274430713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18939542263557884365907617 14204656697668413274430713)
        ·
          refine ⟨10653492523251309955823035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14204656697668413274430713 10653492523251309955823035)
          ·
            refine ⟨15980238784876964933734553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10653492523251309955823035 15980238784876964933734553)
            ·
              refine ⟨11985179088657723700300915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15980238784876964933734553 11985179088657723700300915)
              ·
                refine ⟨17977768632986585550451373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11985179088657723700300915 17977768632986585550451373)
                ·
                  refine ⟨6741663237369969581419265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17977768632986585550451373 6741663237369969581419265)
                  ·
                    refine ⟨5056247428027477186064449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6741663237369969581419265 5056247428027477186064449)
                    ·
                      refine ⟨3792185571020607889548337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056247428027477186064449 3792185571020607889548337)
                      ·
                        rfl

theorem cell23_7385255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_7385255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385255 prefixEnd_7385255 := by exact prefixLift 7385255
  have htrace : WordTrace (prefixWord ++ tailWord_7385255) baseStart_7385255 baseEnd_7385255 := by
    simpa [prefixWord, tailWord_7385255, baseEnd_7385255] using wordTrace_append hprefix tailTrace_7385255
  have hstable : (prefixWord ++ tailWord_7385255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385255).length < 2 ^ (prefixWord ++ tailWord_7385255).sum := by decide
  have hdescent : baseEnd_7385255 < baseStart_7385255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385271 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 1, 3, 3]
def baseStart_7385271 : Nat := 118140960795 + 7385271 * 2 ^ 59
def prefixEnd_7385271 : Nat := 4983230072969 + 3 ^ 40 * 7385271 * 2
def baseEnd_7385271 : Nat := 3792193786711079826948263

theorem tailTrace_7385271 : CollatzResearch.WordTrace tailWord_7385271 prefixEnd_7385271 3792193786711079826948263 := by
  unfold tailWord_7385271
  simp only [CollatzResearch.WordTrace]
  refine ⟨269362962427431945714379667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179575308284954630476253111 269362962427431945714379667)
  ·
    refine ⟨404044443641147918571569501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269362962427431945714379667 404044443641147918571569501)
    ·
      refine ⟨151516666365430469464338563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404044443641147918571569501 151516666365430469464338563)
      ·
        refine ⟨227274999548145704196507845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151516666365430469464338563 227274999548145704196507845)
        ·
          refine ⟨42614062415277319536845221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227274999548145704196507845 42614062415277319536845221)
          ·
            refine ⟨7990136702864497413158479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42614062415277319536845221 7990136702864497413158479)
            ·
              refine ⟨11985205054296746119737719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7990136702864497413158479 11985205054296746119737719)
              ·
                refine ⟨17977807581445119179606579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11985205054296746119737719 17977807581445119179606579)
                ·
                  refine ⟨26966711372167678769409869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17977807581445119179606579 26966711372167678769409869)
                  ·
                    refine ⟨10112516764562879538528701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26966711372167678769409869 10112516764562879538528701)
                    ·
                      refine ⟨3792193786711079826948263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10112516764562879538528701 3792193786711079826948263)
                      ·
                        rfl

theorem cell23_7385271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_7385271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385271 prefixEnd_7385271 := by exact prefixLift 7385271
  have htrace : WordTrace (prefixWord ++ tailWord_7385271) baseStart_7385271 baseEnd_7385271 := by
    simpa [prefixWord, tailWord_7385271, baseEnd_7385271] using wordTrace_append hprefix tailTrace_7385271
  have hstable : (prefixWord ++ tailWord_7385271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385271).length < 2 ^ (prefixWord ++ tailWord_7385271).sum := by decide
  have hdescent : baseEnd_7385271 < baseStart_7385271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385278 : List Nat := [4, 2, 1, 1, 5, 1, 2, 7]
def baseStart_7385278 : Nat := 118140960795 + 7385278 * 2 ^ 59
def prefixEnd_7385278 : Nat := 4983230072969 + 3 ^ 40 * 7385278 * 2
def baseEnd_7385278 : Nat := 140451754854654122205953

theorem tailTrace_7385278 : CollatzResearch.WordTrace tailWord_7385278 prefixEnd_7385278 140451754854654122205953 := by
  unfold tailWord_7385278
  simp only [CollatzResearch.WordTrace]
  refine ⟨33670402217300823238735561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179575478492271057273256325 33670402217300823238735561)
  ·
    refine ⟨25252801662975617429051671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33670402217300823238735561 25252801662975617429051671)
    ·
      refine ⟨37879202494463426143577507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25252801662975617429051671 37879202494463426143577507)
      ·
        refine ⟨56818803741695139215366261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37879202494463426143577507 56818803741695139215366261)
        ·
          refine ⟨5326762850783919301440587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56818803741695139215366261 5326762850783919301440587)
          ·
            refine ⟨7990144276175878952160881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326762850783919301440587 7990144276175878952160881)
            ·
              refine ⟨5992608207131909214120661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7990144276175878952160881 5992608207131909214120661)
              ·
                refine ⟨140451754854654122205953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5992608207131909214120661 140451754854654122205953)
                ·
                  rfl

theorem cell23_7385278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_7385278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385278 prefixEnd_7385278 := by exact prefixLift 7385278
  have htrace : WordTrace (prefixWord ++ tailWord_7385278) baseStart_7385278 baseEnd_7385278 := by
    simpa [prefixWord, tailWord_7385278, baseEnd_7385278] using wordTrace_append hprefix tailTrace_7385278
  have hstable : (prefixWord ++ tailWord_7385278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385278).length < 2 ^ (prefixWord ++ tailWord_7385278).sum := by decide
  have hdescent : baseEnd_7385278 < baseStart_7385278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385284 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_7385284 : Nat := 118140960795 + 7385284 * 2 ^ 59
def prefixEnd_7385284 : Nat := 4983230072969 + 3 ^ 40 * 7385284 * 2
def baseEnd_7385284 : Nat := 3792200461959588276085703

theorem tailTrace_7385284 : CollatzResearch.WordTrace tailWord_7385284 prefixEnd_7385284 3792200461959588276085703 := by
  unfold tailWord_7385284
  simp only [CollatzResearch.WordTrace]
  refine ⟨134681718288192424467301453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179575624384256565956401937 134681718288192424467301453)
  ·
    refine ⟨50505644358072159175238045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134681718288192424467301453 50505644358072159175238045)
    ·
      refine ⟨18939616634277059690714267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50505644358072159175238045 18939616634277059690714267)
      ·
        refine ⟨28409424951415589536071401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18939616634277059690714267 28409424951415589536071401)
        ·
          refine ⟨21307068713561692152053551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28409424951415589536071401 21307068713561692152053551)
          ·
            refine ⟨31960603070342538228080327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21307068713561692152053551 31960603070342538228080327)
            ·
              refine ⟨47940904605513807342120491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31960603070342538228080327 47940904605513807342120491)
              ·
                refine ⟨71911356908270711013180737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47940904605513807342120491 71911356908270711013180737)
                ·
                  refine ⟨53933517681203033259885553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71911356908270711013180737 53933517681203033259885553)
                  ·
                    refine ⟨40450138260902274944914165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53933517681203033259885553 40450138260902274944914165)
                    ·
                      refine ⟨3792200461959588276085703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40450138260902274944914165 3792200461959588276085703)
                      ·
                        rfl

theorem cell23_7385284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_7385284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385284 prefixEnd_7385284 := by exact prefixLift 7385284
  have htrace : WordTrace (prefixWord ++ tailWord_7385284) baseStart_7385284 baseEnd_7385284 := by
    simpa [prefixWord, tailWord_7385284, baseEnd_7385284] using wordTrace_append hprefix tailTrace_7385284
  have hstable : (prefixWord ++ tailWord_7385284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385284).length < 2 ^ (prefixWord ++ tailWord_7385284).sum := by decide
  have hdescent : baseEnd_7385284 < baseStart_7385284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385297 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_7385297 : Nat := 118140960795 + 7385297 * 2 ^ 59
def prefixEnd_7385297 : Nat := 4983230072969 + 3 ^ 40 * 7385297 * 2
def baseEnd_7385297 : Nat := 3792207137208096725223143

theorem tailTrace_7385297 : CollatzResearch.WordTrace tailWord_7385297 prefixEnd_7385297 3792207137208096725223143 := by
  unfold tailWord_7385297
  simp only [CollatzResearch.WordTrace]
  refine ⟨269363910725337752154826145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179575940483558501436550763 269363910725337752154826145)
  ·
    refine ⟨202022933044003314116119609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269363910725337752154826145 202022933044003314116119609)
    ·
      refine ⟨151517199783002485587089707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202022933044003314116119609 151517199783002485587089707)
      ·
        refine ⟨227275799674503728380634561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151517199783002485587089707 227275799674503728380634561)
        ·
          refine ⟨170456849755877796285475921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227275799674503728380634561 170456849755877796285475921)
          ·
            refine ⟨127842637316908347214106941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170456849755877796285475921 127842637316908347214106941)
            ·
              refine ⟨47940988993840630205290103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127842637316908347214106941 47940988993840630205290103)
              ·
                refine ⟨71911483490760945307935155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47940988993840630205290103 71911483490760945307935155)
                ·
                  refine ⟨107867225236141417961902733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71911483490760945307935155 107867225236141417961902733)
                  ·
                    refine ⟨40450209463553031735713525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107867225236141417961902733 40450209463553031735713525)
                    ·
                      refine ⟨3792207137208096725223143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40450209463553031735713525 3792207137208096725223143)
                      ·
                        rfl

theorem cell23_7385297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_7385297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385297 prefixEnd_7385297 := by exact prefixLift 7385297
  have htrace : WordTrace (prefixWord ++ tailWord_7385297) baseStart_7385297 baseEnd_7385297 := by
    simpa [prefixWord, tailWord_7385297, baseEnd_7385297] using wordTrace_append hprefix tailTrace_7385297
  have hstable : (prefixWord ++ tailWord_7385297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385297).length < 2 ^ (prefixWord ++ tailWord_7385297).sum := by decide
  have hdescent : baseEnd_7385297 < baseStart_7385297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385298 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_7385298 : Nat := 118140960795 + 7385298 * 2 ^ 59
def prefixEnd_7385298 : Nat := 4983230072969 + 3 ^ 40 * 7385298 * 2
def baseEnd_7385298 : Nat := 3792207650688751221310639

theorem tailTrace_7385298 : CollatzResearch.WordTrace tailWord_7385298 prefixEnd_7385298 3792207650688751221310639 := by
  unfold tailWord_7385298
  simp only [CollatzResearch.WordTrace]
  refine ⟨67340986799583532331403137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179575964798889419550408365 67340986799583532331403137)
  ·
    refine ⟨50505740099687649248552353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67340986799583532331403137 50505740099687649248552353)
    ·
      refine ⟨37879305074765736936414265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50505740099687649248552353 37879305074765736936414265)
      ·
        refine ⟨28409478806074302702310699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37879305074765736936414265 28409478806074302702310699)
        ·
          refine ⟨42614218209111454053466049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28409478806074302702310699 42614218209111454053466049)
          ·
            refine ⟨31960663656833590540099537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42614218209111454053466049 31960663656833590540099537)
            ·
              refine ⟨23970497742625192905074653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31960663656833590540099537 23970497742625192905074653)
              ·
                refine ⟨8988936653484447339402995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23970497742625192905074653 8988936653484447339402995)
                ·
                  refine ⟨13483404980226671009104493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8988936653484447339402995 13483404980226671009104493)
                  ·
                    refine ⟨5056276867585001628414185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13483404980226671009104493 5056276867585001628414185)
                    ·
                      refine ⟨3792207650688751221310639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056276867585001628414185 3792207650688751221310639)
                      ·
                        rfl

theorem cell23_7385298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_7385298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385298 prefixEnd_7385298 := by exact prefixLift 7385298
  have htrace : WordTrace (prefixWord ++ tailWord_7385298) baseStart_7385298 baseEnd_7385298 := by
    simpa [prefixWord, tailWord_7385298, baseEnd_7385298] using wordTrace_append hprefix tailTrace_7385298
  have hstable : (prefixWord ++ tailWord_7385298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385298).length < 2 ^ (prefixWord ++ tailWord_7385298).sum := by decide
  have hdescent : baseEnd_7385298 < baseStart_7385298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385334 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_7385334 : Nat := 118140960795 + 7385334 * 2 ^ 59
def prefixEnd_7385334 : Nat := 4983230072969 + 3 ^ 40 * 7385334 * 2
def baseEnd_7385334 : Nat := 421358459554701453384497

theorem tailTrace_7385334 : CollatzResearch.WordTrace tailWord_7385334 prefixEnd_7385334 421358459554701453384497 := by
  unfold tailWord_7385334
  simp only [CollatzResearch.WordTrace]
  refine ⟨16835328764137731717120191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179576840150802471649282037 16835328764137731717120191)
  ·
    refine ⟨25252993146206597575680287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16835328764137731717120191 25252993146206597575680287)
    ·
      refine ⟨37879489719309896363520431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25252993146206597575680287 37879489719309896363520431)
      ·
        refine ⟨56819234578964844545280647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37879489719309896363520431 56819234578964844545280647)
        ·
          refine ⟨85228851868447266817920971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56819234578964844545280647 85228851868447266817920971)
          ·
            refine ⟨127843277802670900226881457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85228851868447266817920971 127843277802670900226881457)
            ·
              refine ⟨95882458352003175170161093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127843277802670900226881457 95882458352003175170161093)
              ·
                refine ⟨17977960941000595344405205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95882458352003175170161093 17977960941000595344405205)
                ·
                  refine ⟨421358459554701453384497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17977960941000595344405205 421358459554701453384497)
                  ·
                    rfl

theorem cell23_7385334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_7385334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385334 prefixEnd_7385334 := by exact prefixLift 7385334
  have htrace : WordTrace (prefixWord ++ tailWord_7385334) baseStart_7385334 baseEnd_7385334 := by
    simpa [prefixWord, tailWord_7385334, baseEnd_7385334] using wordTrace_append hprefix tailTrace_7385334
  have hstable : (prefixWord ++ tailWord_7385334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385334).length < 2 ^ (prefixWord ++ tailWord_7385334).sum := by decide
  have hdescent : baseEnd_7385334 < baseStart_7385334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385401 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7385401 : Nat := 118140960795 + 7385401 * 2 ^ 59
def prefixEnd_7385401 : Nat := 4983230072969 + 3 ^ 40 * 7385401 * 2
def baseEnd_7385401 : Nat := 3792260539196164318322665

theorem tailTrace_7385401 : CollatzResearch.WordTrace tailWord_7385401 prefixEnd_7385401 3792260539196164318322665 := by
  unfold tailWord_7385401
  simp only [CollatzResearch.WordTrace]
  refine ⟨269367703916960977916612057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179578469277973985277741371 269367703916960977916612057)
  ·
    refine ⟨202025777937720733437459043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269367703916960977916612057 202025777937720733437459043)
    ·
      refine ⟨303038666906581100156188565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202025777937720733437459043 303038666906581100156188565)
      ·
        refine ⟨14204937511245989069821339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 303038666906581100156188565 14204937511245989069821339)
        ·
          refine ⟨21307406266868983604732009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14204937511245989069821339 21307406266868983604732009)
          ·
            refine ⟨15980554700151737703549007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21307406266868983604732009 15980554700151737703549007)
            ·
              refine ⟨23970832050227606555323511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15980554700151737703549007 23970832050227606555323511)
              ·
                refine ⟨35956248075341409832985267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23970832050227606555323511 35956248075341409832985267)
                ·
                  refine ⟨53934372113012114749477901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35956248075341409832985267 53934372113012114749477901)
                  ·
                    refine ⟨20225389542379543031054213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53934372113012114749477901 20225389542379543031054213)
                    ·
                      refine ⟨3792260539196164318322665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20225389542379543031054213 3792260539196164318322665)
                      ·
                        rfl

theorem cell23_7385401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7385401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385401 prefixEnd_7385401 := by exact prefixLift 7385401
  have htrace : WordTrace (prefixWord ++ tailWord_7385401) baseStart_7385401 baseEnd_7385401 := by
    simpa [prefixWord, tailWord_7385401, baseEnd_7385401] using wordTrace_append hprefix tailTrace_7385401
  have hstable : (prefixWord ++ tailWord_7385401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385401).length < 2 ^ (prefixWord ++ tailWord_7385401).sum := by decide
  have hdescent : baseEnd_7385401 < baseStart_7385401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385424 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 8]
def baseStart_7385424 : Nat := 118140960795 + 7385424 * 2 ^ 59
def prefixEnd_7385424 : Nat := 4983230072969 + 3 ^ 40 * 7385424 * 2
def baseEnd_7385424 : Nat := 421363594361246414259451

theorem tailTrace_7385424 : CollatzResearch.WordTrace tailWord_7385424 prefixEnd_7385424 421363594361246414259451 := by
  unfold tailWord_7385424
  simp only [CollatzResearch.WordTrace]
  refine ⟨134684271397938826422349663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179579028530585101896466217 134684271397938826422349663)
  ·
    refine ⟨202026407096908239633524495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134684271397938826422349663 202026407096908239633524495)
    ·
      refine ⟨303039610645362359450286743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202026407096908239633524495 303039610645362359450286743)
      ·
        refine ⟨454559415968043539175430115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303039610645362359450286743 454559415968043539175430115)
        ·
          refine ⟨681839123952065308763145173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454559415968043539175430115 681839123952065308763145173)
          ·
            refine ⟨15980604467626530674136215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 681839123952065308763145173 15980604467626530674136215)
            ·
              refine ⟨23970906701439796011204323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15980604467626530674136215 23970906701439796011204323)
              ·
                refine ⟨35956360052159694016806485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23970906701439796011204323 35956360052159694016806485)
                ·
                  refine ⟨421363594361246414259451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35956360052159694016806485 421363594361246414259451)
                  ·
                    rfl

theorem cell23_7385424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 8].length) (baseStart_7385424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385424 prefixEnd_7385424 := by exact prefixLift 7385424
  have htrace : WordTrace (prefixWord ++ tailWord_7385424) baseStart_7385424 baseEnd_7385424 := by
    simpa [prefixWord, tailWord_7385424, baseEnd_7385424] using wordTrace_append hprefix tailTrace_7385424
  have hstable : (prefixWord ++ tailWord_7385424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385424).length < 2 ^ (prefixWord ++ tailWord_7385424).sum := by decide
  have hdescent : baseEnd_7385424 < baseStart_7385424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385428 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_7385428 : Nat := 118140960795 + 7385428 * 2 ^ 59
def prefixEnd_7385428 : Nat := 4983230072969 + 3 ^ 40 * 7385428 * 2
def baseEnd_7385428 : Nat := 1264091467724611904228347

theorem tailTrace_7385428 : CollatzResearch.WordTrace tailWord_7385428 prefixEnd_7385428 1264091467724611904228347 := by
  unfold tailWord_7385428
  simp only [CollatzResearch.WordTrace]
  refine ⟨134684344343931580763922469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179579125791908774351896625 134684344343931580763922469)
  ·
    refine ⟨25253314564487171393235463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134684344343931580763922469 25253314564487171393235463)
    ·
      refine ⟨37879971846730757089853195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25253314564487171393235463 37879971846730757089853195)
      ·
        refine ⟨56819957770096135634779793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37879971846730757089853195 56819957770096135634779793)
        ·
          refine ⟨42614968327572101726084845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56819957770096135634779793 42614968327572101726084845)
          ·
            refine ⟨15980613122839538147281817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42614968327572101726084845 15980613122839538147281817)
            ·
              refine ⟨11985459842129653610461363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15980613122839538147281817 11985459842129653610461363)
              ·
                refine ⟨17978189763194480415692045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11985459842129653610461363 17978189763194480415692045)
                ·
                  refine ⟨6741821161197930155884517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17978189763194480415692045 6741821161197930155884517)
                  ·
                    refine ⟨1264091467724611904228347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6741821161197930155884517 1264091467724611904228347)
                    ·
                      rfl

theorem cell23_7385428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_7385428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385428 prefixEnd_7385428 := by exact prefixLift 7385428
  have htrace : WordTrace (prefixWord ++ tailWord_7385428) baseStart_7385428 baseEnd_7385428 := by
    simpa [prefixWord, tailWord_7385428, baseEnd_7385428] using wordTrace_append hprefix tailTrace_7385428
  have hstable : (prefixWord ++ tailWord_7385428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385428).length < 2 ^ (prefixWord ++ tailWord_7385428).sum := by decide
  have hdescent : baseEnd_7385428 < baseStart_7385428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385444 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_7385444 : Nat := 118140960795 + 7385444 * 2 ^ 59
def prefixEnd_7385444 : Nat := 4983230072969 + 3 ^ 40 * 7385444 * 2
def baseEnd_7385444 : Nat := 3792282618864307650084967

theorem tailTrace_7385444 : CollatzResearch.WordTrace tailWord_7385444 prefixEnd_7385444 3792282618864307650084967 := by
  unfold tailWord_7385444
  simp only [CollatzResearch.WordTrace]
  refine ⟨134684636127902598130213693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179579514837203464173618257 134684636127902598130213693)
  ·
    refine ⟨50506738547963474298830135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134684636127902598130213693 50506738547963474298830135)
    ·
      refine ⟨75760107821945211448245203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50506738547963474298830135 75760107821945211448245203)
      ·
        refine ⟨113640161732917817172367805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75760107821945211448245203 113640161732917817172367805)
        ·
          refine ⟨42615060649844181439637927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113640161732917817172367805 42615060649844181439637927)
          ·
            refine ⟨63922590974766272159456891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42615060649844181439637927 63922590974766272159456891)
            ·
              refine ⟨95883886462149408239185337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63922590974766272159456891 95883886462149408239185337)
              ·
                refine ⟨71912914846612056179389003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95883886462149408239185337 71912914846612056179389003)
                ·
                  refine ⟨107869372269918084269083505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71912914846612056179389003 107869372269918084269083505)
                  ·
                    refine ⟨80902029202438563201812629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107869372269918084269083505 80902029202438563201812629)
                    ·
                      refine ⟨3792282618864307650084967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80902029202438563201812629 3792282618864307650084967)
                      ·
                        rfl

theorem cell23_7385444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_7385444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385444 prefixEnd_7385444 := by exact prefixLift 7385444
  have htrace : WordTrace (prefixWord ++ tailWord_7385444) baseStart_7385444 baseEnd_7385444 := by
    simpa [prefixWord, tailWord_7385444, baseEnd_7385444] using wordTrace_append hprefix tailTrace_7385444
  have hstable : (prefixWord ++ tailWord_7385444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385444).length < 2 ^ (prefixWord ++ tailWord_7385444).sum := by decide
  have hdescent : baseEnd_7385444 < baseStart_7385444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385492 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 6]
def baseStart_7385492 : Nat := 118140960795 + 7385492 * 2 ^ 59
def prefixEnd_7385492 : Nat := 4983230072969 + 3 ^ 40 * 7385492 * 2
def baseEnd_7385492 : Nat := 421367473992858162476083

theorem tailTrace_7385492 : CollatzResearch.WordTrace tailWord_7385492 prefixEnd_7385492 421367473992858162476083 := by
  unfold tailWord_7385492
  simp only [CollatzResearch.WordTrace]
  refine ⟨134685511479815650229087365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179580681973087533638783153 134685511479815650229087365)
  ·
    refine ⟨25253533402465434417953881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134685511479815650229087365 25253533402465434417953881)
    ·
      refine ⟨18940150051849075813465411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25253533402465434417953881 18940150051849075813465411)
      ·
        refine ⟨28410225077773613720198117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18940150051849075813465411 28410225077773613720198117)
        ·
          refine ⟨5326917202082552572537147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28410225077773613720198117 5326917202082552572537147)
          ·
            refine ⟨7990375803123828858805721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326917202082552572537147 7990375803123828858805721)
            ·
              refine ⟨5992781852342871644104291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7990375803123828858805721 5992781852342871644104291)
              ·
                refine ⟨8989172778514307466156437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5992781852342871644104291 8989172778514307466156437)
                ·
                  refine ⟨421367473992858162476083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8989172778514307466156437 421367473992858162476083)
                  ·
                    rfl

theorem cell23_7385492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_7385492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385492 prefixEnd_7385492 := by exact prefixLift 7385492
  have htrace : WordTrace (prefixWord ++ tailWord_7385492) baseStart_7385492 baseEnd_7385492 := by
    simpa [prefixWord, tailWord_7385492, baseEnd_7385492] using wordTrace_append hprefix tailTrace_7385492
  have hstable : (prefixWord ++ tailWord_7385492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385492).length < 2 ^ (prefixWord ++ tailWord_7385492).sum := by decide
  have hdescent : baseEnd_7385492 < baseStart_7385492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385508 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_7385508 : Nat := 118140960795 + 7385508 * 2 ^ 59
def prefixEnd_7385508 : Nat := 4983230072969 + 3 ^ 40 * 7385508 * 2
def baseEnd_7385508 : Nat := 3792315481626195399684673

theorem tailTrace_7385508 : CollatzResearch.WordTrace tailWord_7385508 prefixEnd_7385508 3792315481626195399684673 := by
  unfold tailWord_7385508
  simp only [CollatzResearch.WordTrace]
  refine ⟨134685803263786667595378589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179581071018382223460504785 134685803263786667595378589)
  ·
    refine ⟨50507176223920000348266971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134685803263786667595378589 50507176223920000348266971)
    ·
      refine ⟨75760764335880000522400457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50507176223920000348266971 75760764335880000522400457)
      ·
        refine ⟨56820573251910000391800343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75760764335880000522400457 56820573251910000391800343)
        ·
          refine ⟨85230859877865000587700515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56820573251910000391800343 85230859877865000587700515)
          ·
            refine ⟨127846289816797500881550773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85230859877865000587700515 127846289816797500881550773)
            ·
              refine ⟨11985589670324765707645385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127846289816797500881550773 11985589670324765707645385)
              ·
                refine ⟨8989192252743574280734039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11985589670324765707645385 8989192252743574280734039)
                ·
                  refine ⟨13483788379115361421101059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8989192252743574280734039 13483788379115361421101059)
                  ·
                    refine ⟨20225682568673042131651589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13483788379115361421101059 20225682568673042131651589)
                    ·
                      refine ⟨3792315481626195399684673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20225682568673042131651589 3792315481626195399684673)
                      ·
                        rfl

theorem cell23_7385508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_7385508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385508 prefixEnd_7385508 := by exact prefixLift 7385508
  have htrace : WordTrace (prefixWord ++ tailWord_7385508) baseStart_7385508 baseEnd_7385508 := by
    simpa [prefixWord, tailWord_7385508, baseEnd_7385508] using wordTrace_append hprefix tailTrace_7385508
  have hstable : (prefixWord ++ tailWord_7385508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385508).length < 2 ^ (prefixWord ++ tailWord_7385508).sum := by decide
  have hdescent : baseEnd_7385508 < baseStart_7385508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385512 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_7385512 : Nat := 118140960795 + 7385512 * 2 ^ 59
def prefixEnd_7385512 : Nat := 4983230072969 + 3 ^ 40 * 7385512 * 2
def baseEnd_7385512 : Nat := 3792317535548813384034655

theorem tailTrace_7385512 : CollatzResearch.WordTrace tailWord_7385512 prefixEnd_7385512 3792317535548813384034655 := by
  unfold tailWord_7385512
  simp only [CollatzResearch.WordTrace]
  refine ⟨134685876209779421936951395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179581168279705895915935193 134685876209779421936951395)
  ·
    refine ⟨202028814314669132905427093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134685876209779421936951395 202028814314669132905427093)
    ·
      refine ⟨9470100671000115604941895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202028814314669132905427093 9470100671000115604941895)
      ·
        refine ⟨14205151006500173407412843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9470100671000115604941895 14205151006500173407412843)
        ·
          refine ⟨21307726509750260111119265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14205151006500173407412843 21307726509750260111119265)
          ·
            refine ⟨15980794882312695083339449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21307726509750260111119265 15980794882312695083339449)
            ·
              refine ⟨11985596161734521312504587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15980794882312695083339449 11985596161734521312504587)
              ·
                refine ⟨17978394242601781968756881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11985596161734521312504587 17978394242601781968756881)
                ·
                  refine ⟨13483795681951336476567661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17978394242601781968756881 13483795681951336476567661)
                  ·
                    refine ⟨5056423380731751178712873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13483795681951336476567661 5056423380731751178712873)
                    ·
                      refine ⟨3792317535548813384034655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056423380731751178712873 3792317535548813384034655)
                      ·
                        rfl

theorem cell23_7385512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_7385512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385512 prefixEnd_7385512 := by exact prefixLift 7385512
  have htrace : WordTrace (prefixWord ++ tailWord_7385512) baseStart_7385512 baseEnd_7385512 := by
    simpa [prefixWord, tailWord_7385512, baseEnd_7385512] using wordTrace_append hprefix tailTrace_7385512
  have hstable : (prefixWord ++ tailWord_7385512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385512).length < 2 ^ (prefixWord ++ tailWord_7385512).sum := by decide
  have hdescent : baseEnd_7385512 < baseStart_7385512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385521 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7385521 : Nat := 118140960795 + 7385521 * 2 ^ 59
def prefixEnd_7385521 : Nat := 4983230072969 + 3 ^ 40 * 7385521 * 2
def baseEnd_7385521 : Nat := 3792322156874703848822113

theorem tailTrace_7385521 : CollatzResearch.WordTrace tailWord_7385521 prefixEnd_7385521 3792322156874703848822113 := by
  unfold tailWord_7385521
  simp only [CollatzResearch.WordTrace]
  refine ⟨269372080676526238410980417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179581387117684158940653611 269372080676526238410980417)
  ·
    refine ⟨202029060507394678808235313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269372080676526238410980417 202029060507394678808235313)
    ·
      refine ⟨151521795380546009106176485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202029060507394678808235313 151521795380546009106176485)
      ·
        refine ⟨28410336633852376707408091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151521795380546009106176485 28410336633852376707408091)
        ·
          refine ⟨42615504950778565061112137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28410336633852376707408091 42615504950778565061112137)
          ·
            refine ⟨31961628713083923795834103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42615504950778565061112137 31961628713083923795834103)
            ·
              refine ⟨47942443069625885693751155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31961628713083923795834103 47942443069625885693751155)
              ·
                refine ⟨71913664604438828540626733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47942443069625885693751155 71913664604438828540626733)
                ·
                  refine ⟨26967624226664560702735025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71913664604438828540626733 26967624226664560702735025)
                  ·
                    refine ⟨20225718169998420527051269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26967624226664560702735025 20225718169998420527051269)
                    ·
                      refine ⟨3792322156874703848822113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20225718169998420527051269 3792322156874703848822113)
                      ·
                        rfl

theorem cell23_7385521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7385521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385521 prefixEnd_7385521 := by exact prefixLift 7385521
  have htrace : WordTrace (prefixWord ++ tailWord_7385521) baseStart_7385521 baseEnd_7385521 := by
    simpa [prefixWord, tailWord_7385521, baseEnd_7385521] using wordTrace_append hprefix tailTrace_7385521
  have hstable : (prefixWord ++ tailWord_7385521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385521).length < 2 ^ (prefixWord ++ tailWord_7385521).sum := by decide
  have hdescent : baseEnd_7385521 < baseStart_7385521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385548 : List Nat := [2, 2, 1, 4, 3, 2, 1, 8]
def baseStart_7385548 : Nat := 118140960795 + 7385548 * 2 ^ 59
def prefixEnd_7385548 : Nat := 4983230072969 + 3 ^ 40 * 7385548 * 2
def baseEnd_7385548 : Nat := 140456889661199083080907

theorem tailTrace_7385548 : CollatzResearch.WordTrace tailWord_7385548 prefixEnd_7385548 140456889661199083080907 := by
  unfold tailWord_7385548
  simp only [CollatzResearch.WordTrace]
  refine ⟨134686532723714211011106649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179582043631618948014808865 134686532723714211011106649)
  ·
    refine ⟨101014899542785658258329987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134686532723714211011106649 101014899542785658258329987)
    ·
      refine ⟨151522349314178487387494981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101014899542785658258329987 151522349314178487387494981)
      ·
        refine ⟨28410440496408466385155309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151522349314178487387494981 28410440496408466385155309)
        ·
          refine ⟨10653915186153174894433241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28410440496408466385155309 10653915186153174894433241)
          ·
            refine ⟨7990436389614881170824931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10653915186153174894433241 7990436389614881170824931)
            ·
              refine ⟨11985654584422321756237397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7990436389614881170824931 11985654584422321756237397)
              ·
                refine ⟨140456889661199083080907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11985654584422321756237397 140456889661199083080907)
                ·
                  rfl

theorem cell23_7385548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 8].length) (baseStart_7385548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385548 prefixEnd_7385548 := by exact prefixLift 7385548
  have htrace : WordTrace (prefixWord ++ tailWord_7385548) baseStart_7385548 baseEnd_7385548 := by
    simpa [prefixWord, tailWord_7385548, baseEnd_7385548] using wordTrace_append hprefix tailTrace_7385548
  have hstable : (prefixWord ++ tailWord_7385548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385548).length < 2 ^ (prefixWord ++ tailWord_7385548).sum := by decide
  have hdescent : baseEnd_7385548 < baseStart_7385548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385568 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 3, 3, 2]
def baseStart_7385568 : Nat := 118140960795 + 7385568 * 2 ^ 59
def prefixEnd_7385568 : Nat := 4983230072969 + 3 ^ 40 * 7385568 * 2
def baseEnd_7385568 : Nat := 3792346290465465164934397

theorem tailTrace_7385568 : CollatzResearch.WordTrace tailWord_7385568 prefixEnd_7385568 3792346290465465164934397 := by
  unfold tailWord_7385568
  simp only [CollatzResearch.WordTrace]
  refine ⟨134686897453677982718970679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179582529938237310291960905 134686897453677982718970679)
  ·
    refine ⟨202030346180516974078456019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134686897453677982718970679 202030346180516974078456019)
    ·
      refine ⟨303045519270775461117684029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202030346180516974078456019 303045519270775461117684029)
      ·
        refine ⟨113642069726540797919131511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303045519270775461117684029 113642069726540797919131511)
        ·
          refine ⟨170463104589811196878697267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113642069726540797919131511 170463104589811196878697267)
          ·
            refine ⟨255694656884716795318045901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170463104589811196878697267 255694656884716795318045901)
            ·
              refine ⟨95885496331768798244267213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255694656884716795318045901 95885496331768798244267213)
              ·
                refine ⟨35957061124413299341600205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95885496331768798244267213 35957061124413299341600205)
                ·
                  refine ⟨13483897921654987253100077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35957061124413299341600205 13483897921654987253100077)
                  ·
                    refine ⟨5056461720620620219912529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13483897921654987253100077 5056461720620620219912529)
                    ·
                      refine ⟨3792346290465465164934397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056461720620620219912529 3792346290465465164934397)
                      ·
                        rfl

theorem cell23_7385568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_7385568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385568 prefixEnd_7385568 := by exact prefixLift 7385568
  have htrace : WordTrace (prefixWord ++ tailWord_7385568) baseStart_7385568 baseEnd_7385568 := by
    simpa [prefixWord, tailWord_7385568, baseEnd_7385568] using wordTrace_append hprefix tailTrace_7385568
  have hstable : (prefixWord ++ tailWord_7385568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385568).length < 2 ^ (prefixWord ++ tailWord_7385568).sum := by decide
  have hdescent : baseEnd_7385568 < baseStart_7385568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385585 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 1, 3, 2]
def baseStart_7385585 : Nat := 118140960795 + 7385585 * 2 ^ 59
def prefixEnd_7385585 : Nat := 4983230072969 + 3 ^ 40 * 7385585 * 2
def baseEnd_7385585 : Nat := 3792355019636591598421819

theorem tailTrace_7385585 : CollatzResearch.WordTrace tailWord_7385585 prefixEnd_7385585 3792355019636591598421819 := by
  unfold tailWord_7385585
  simp only [CollatzResearch.WordTrace]
  refine ⟨269374414948294377341310209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179582943298862918227540139 269374414948294377341310209)
  ·
    refine ⟨202030811211220783005982657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269374414948294377341310209 202030811211220783005982657)
    ·
      refine ⟨151523108408415587254486993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202030811211220783005982657 151523108408415587254486993)
      ·
        refine ⟨113642331306311690440865245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151523108408415587254486993 113642331306311690440865245)
        ·
          refine ⟨42615874239866883915324467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113642331306311690440865245 42615874239866883915324467)
          ·
            refine ⟨63923811359800325872986701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42615874239866883915324467 63923811359800325872986701)
            ·
              refine ⟨23971429259925122202370013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63923811359800325872986701 23971429259925122202370013)
              ·
                refine ⟨8989285972471920825888755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23971429259925122202370013 8989285972471920825888755)
                ·
                  refine ⟨13483928958707881238833133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8989285972471920825888755 13483928958707881238833133)
                  ·
                    refine ⟨5056473359515455464562425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13483928958707881238833133 5056473359515455464562425)
                    ·
                      refine ⟨3792355019636591598421819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056473359515455464562425 3792355019636591598421819)
                      ·
                        rfl

theorem cell23_7385585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_7385585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385585 prefixEnd_7385585 := by exact prefixLift 7385585
  have htrace : WordTrace (prefixWord ++ tailWord_7385585) baseStart_7385585 baseEnd_7385585 := by
    simpa [prefixWord, tailWord_7385585, baseEnd_7385585] using wordTrace_append hprefix tailTrace_7385585
  have hstable : (prefixWord ++ tailWord_7385585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385585).length < 2 ^ (prefixWord ++ tailWord_7385585).sum := by decide
  have hdescent : baseEnd_7385585 < baseStart_7385585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385621 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 7]
def baseStart_7385621 : Nat := 118140960795 + 7385621 * 2 ^ 59
def prefixEnd_7385621 : Nat := 4983230072969 + 3 ^ 40 * 7385621 * 2
def baseEnd_7385621 : Nat := 421374833882239273063517

theorem tailTrace_7385621 : CollatzResearch.WordTrace tailWord_7385621 prefixEnd_7385621 421374833882239273063517 := by
  unfold tailWord_7385621
  simp only [CollatzResearch.WordTrace]
  refine ⟨269375727976163955489620717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179583818650775970326413811 269375727976163955489620717)
  ·
    refine ⟨101015897991061483308607769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269375727976163955489620717 101015897991061483308607769)
    ·
      refine ⟨75761923493296112481455827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101015897991061483308607769 75761923493296112481455827)
      ·
        refine ⟨113642885239944168722183741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75761923493296112481455827 113642885239944168722183741)
        ·
          refine ⟨42616081964979063270818903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113642885239944168722183741 42616081964979063270818903)
          ·
            refine ⟨63924122947468594906228355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42616081964979063270818903 63924122947468594906228355)
            ·
              refine ⟨95886184421202892359342533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63924122947468594906228355 95886184421202892359342533)
              ·
                refine ⟨17978659578975542317376725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95886184421202892359342533 17978659578975542317376725)
                ·
                  refine ⟨421374833882239273063517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17978659578975542317376725 421374833882239273063517)
                  ·
                    rfl

theorem cell23_7385621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_7385621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385621 prefixEnd_7385621 := by exact prefixLift 7385621
  have htrace : WordTrace (prefixWord ++ tailWord_7385621) baseStart_7385621 baseEnd_7385621 := by
    simpa [prefixWord, tailWord_7385621, baseEnd_7385621] using wordTrace_append hprefix tailTrace_7385621
  have hstable : (prefixWord ++ tailWord_7385621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385621).length < 2 ^ (prefixWord ++ tailWord_7385621).sum := by decide
  have hdescent : baseEnd_7385621 < baseStart_7385621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385655 : List Nat := [1, 1, 3, 1, 2, 3, 5, 2, 5]
def baseStart_7385655 : Nat := 118140960795 + 7385655 * 2 ^ 59
def prefixEnd_7385655 : Nat := 4983230072969 + 3 ^ 40 * 7385655 * 2
def baseEnd_7385655 : Nat := 421376773698045147171833

theorem tailTrace_7385655 : CollatzResearch.WordTrace tailWord_7385655 prefixEnd_7385655 421376773698045147171833 := by
  unfold tailWord_7385655
  simp only [CollatzResearch.WordTrace]
  refine ⟨269376968058040779296358419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179584645372027186197572279 269376968058040779296358419)
  ·
    refine ⟨404065452087061168944537629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269376968058040779296358419 404065452087061168944537629)
    ·
      refine ⟨151524544532647938354201611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404065452087061168944537629 151524544532647938354201611)
      ·
        refine ⟨227286816798971907531302417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151524544532647938354201611 227286816798971907531302417)
        ·
          refine ⟨170465112599228930648476813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227286816798971907531302417 170465112599228930648476813)
          ·
            refine ⟨63924417224710848993178805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170465112599228930648476813 63924417224710848993178805)
            ·
              refine ⟨5992914114816642093110513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63924417224710848993178805 5992914114816642093110513)
              ·
                refine ⟨4494685586112481569832885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5992914114816642093110513 4494685586112481569832885)
                ·
                  refine ⟨421376773698045147171833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4494685586112481569832885 421376773698045147171833)
                  ·
                    rfl

theorem cell23_7385655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 5].length) (baseStart_7385655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385655 prefixEnd_7385655 := by exact prefixLift 7385655
  have htrace : WordTrace (prefixWord ++ tailWord_7385655) baseStart_7385655 baseEnd_7385655 := by
    simpa [prefixWord, tailWord_7385655, baseEnd_7385655] using wordTrace_append hprefix tailTrace_7385655
  have hstable : (prefixWord ++ tailWord_7385655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385655).length < 2 ^ (prefixWord ++ tailWord_7385655).sum := by decide
  have hdescent : baseEnd_7385655 < baseStart_7385655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385688 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_7385688 : Nat := 118140960795 + 7385688 * 2 ^ 59
def prefixEnd_7385688 : Nat := 4983230072969 + 3 ^ 40 * 7385688 * 2
def baseEnd_7385688 : Nat := 3792407908144004695433845

theorem tailTrace_7385688 : CollatzResearch.WordTrace tailWord_7385688 prefixEnd_7385688 3792407908144004695433845 := by
  unfold tailWord_7385688
  simp only [CollatzResearch.WordTrace]
  refine ⟨134689085833460612966154859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179585447777947483954873145 134689085833460612966154859)
  ·
    refine ⟨202033628750190919449232289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134689085833460612966154859 202033628750190919449232289)
    ·
      refine ⟨151525221562643189586924217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202033628750190919449232289 151525221562643189586924217)
      ·
        refine ⟨113643916171982392190193163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151525221562643189586924217 113643916171982392190193163)
        ·
          refine ⟨170465874257973588285289745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113643916171982392190193163 170465874257973588285289745)
          ·
            refine ⟨127849405693480191213967309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170465874257973588285289745 127849405693480191213967309)
            ·
              refine ⟨47943527135055071705237741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127849405693480191213967309 47943527135055071705237741)
              ·
                refine ⟨17978822675645651889464153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47943527135055071705237741 17978822675645651889464153)
                ·
                  refine ⟨13484117006734238917098115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17978822675645651889464153 13484117006734238917098115)
                  ·
                    refine ⟨20226175510101358375647173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13484117006734238917098115 20226175510101358375647173)
                    ·
                      refine ⟨3792407908144004695433845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20226175510101358375647173 3792407908144004695433845)
                      ·
                        rfl

theorem cell23_7385688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_7385688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385688 prefixEnd_7385688 := by exact prefixLift 7385688
  have htrace : WordTrace (prefixWord ++ tailWord_7385688) baseStart_7385688 baseEnd_7385688 := by
    simpa [prefixWord, tailWord_7385688, baseEnd_7385688] using wordTrace_append hprefix tailTrace_7385688
  have hstable : (prefixWord ++ tailWord_7385688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385688).length < 2 ^ (prefixWord ++ tailWord_7385688).sum := by decide
  have hdescent : baseEnd_7385688 < baseStart_7385688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385711 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 8]
def baseStart_7385711 : Nat := 118140960795 + 7385711 * 2 ^ 59
def prefixEnd_7385711 : Nat := 4983230072969 + 3 ^ 40 * 7385711 * 2
def baseEnd_7385711 : Nat := 421379968688784233938471

theorem tailTrace_7385711 : CollatzResearch.WordTrace tailWord_7385711 prefixEnd_7385711 421379968688784233938471 := by
  unfold tailWord_7385711
  simp only [CollatzResearch.WordTrace]
  refine ⟨269379010545837900860396987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179586007030558600573597991 269379010545837900860396987)
  ·
    refine ⟨404068515818756851290595481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269379010545837900860396987 404068515818756851290595481)
    ·
      refine ⟨303051386864067638467946611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404068515818756851290595481 303051386864067638467946611)
      ·
        refine ⟨454577080296101457701919917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303051386864067638467946611 454577080296101457701919917)
        ·
          refine ⟨170466405111038046638219969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454577080296101457701919917 170466405111038046638219969)
          ·
            refine ⟨127849803833278534978664977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170466405111038046638219969 127849803833278534978664977)
            ·
              refine ⟨95887352874958901233998733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127849803833278534978664977 95887352874958901233998733)
              ·
                refine ⟨35957757328109587962749525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95887352874958901233998733 35957757328109587962749525)
                ·
                  refine ⟨421379968688784233938471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35957757328109587962749525 421379968688784233938471)
                  ·
                    rfl

theorem cell23_7385711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 8].length) (baseStart_7385711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385711 prefixEnd_7385711 := by exact prefixLift 7385711
  have htrace : WordTrace (prefixWord ++ tailWord_7385711) baseStart_7385711 baseEnd_7385711 := by
    simpa [prefixWord, tailWord_7385711, baseEnd_7385711] using wordTrace_append hprefix tailTrace_7385711
  have hstable : (prefixWord ++ tailWord_7385711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385711).length < 2 ^ (prefixWord ++ tailWord_7385711).sum := by decide
  have hdescent : baseEnd_7385711 < baseStart_7385711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385728 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 6]
def baseStart_7385728 : Nat := 118140960795 + 7385728 * 2 ^ 59
def prefixEnd_7385728 : Nat := 4983230072969 + 3 ^ 40 * 7385728 * 2
def baseEnd_7385728 : Nat := 421380938596687170992629

theorem tailTrace_7385728 : CollatzResearch.WordTrace tailWord_7385728 prefixEnd_7385728 421380938596687170992629 := by
  unfold tailWord_7385728
  simp only [CollatzResearch.WordTrace]
  refine ⟨134689815293388156381882919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179586420391184208509177225 134689815293388156381882919)
  ·
    refine ⟨202034722940082234572824379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134689815293388156381882919 202034722940082234572824379)
    ·
      refine ⟨303052084410123351859236569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202034722940082234572824379 303052084410123351859236569)
      ·
        refine ⟨227289063307592513894427427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303052084410123351859236569 227289063307592513894427427)
        ·
          refine ⟨340933594961388770841641141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227289063307592513894427427 340933594961388770841641141)
          ·
            refine ⟨31962524527630197266403857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 340933594961388770841641141 31962524527630197266403857)
            ·
              refine ⟨23971893395722647949802893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31962524527630197266403857 23971893395722647949802893)
              ·
                refine ⟨8989460023395992981176085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23971893395722647949802893 8989460023395992981176085)
                ·
                  refine ⟨421380938596687170992629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8989460023395992981176085 421380938596687170992629)
                  ·
                    rfl

theorem cell23_7385728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 6].length) (baseStart_7385728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385728 prefixEnd_7385728 := by exact prefixLift 7385728
  have htrace : WordTrace (prefixWord ++ tailWord_7385728) baseStart_7385728 baseEnd_7385728 := by
    simpa [prefixWord, tailWord_7385728, baseEnd_7385728] using wordTrace_append hprefix tailTrace_7385728
  have hstable : (prefixWord ++ tailWord_7385728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385728).length < 2 ^ (prefixWord ++ tailWord_7385728).sum := by decide
  have hdescent : baseEnd_7385728 < baseStart_7385728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385765 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 4, 3, 2]
def baseStart_7385765 : Nat := 118140960795 + 7385765 * 2 ^ 59
def prefixEnd_7385765 : Nat := 4983230072969 + 3 ^ 40 * 7385765 * 2
def baseEnd_7385765 : Nat := 3792447446154400894170991

theorem tailTrace_7385765 : CollatzResearch.WordTrace tailWord_7385765 prefixEnd_7385765 3792447446154400894170991 := by
  unfold tailWord_7385765
  simp only [CollatzResearch.WordTrace]
  refine ⟨269380980087642268082862749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179587320058428178721908499 269380980087642268082862749)
  ·
    refine ⟨101017867532865850531073531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269380980087642268082862749 101017867532865850531073531)
    ·
      refine ⟨151526801299298775796610297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101017867532865850531073531 151526801299298775796610297)
      ·
        refine ⟨113645100974474081847457723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151526801299298775796610297 113645100974474081847457723)
        ·
          refine ⟨170467651461711122771186585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113645100974474081847457723 170467651461711122771186585)
          ·
            refine ⟨127850738596283342078389939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170467651461711122771186585 127850738596283342078389939)
            ·
              refine ⟨191776107894425013117584909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127850738596283342078389939 191776107894425013117584909)
              ·
                refine ⟨71916040460409379919094341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191776107894425013117584909 71916040460409379919094341)
                ·
                  refine ⟨13484257586326758734830189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71916040460409379919094341 13484257586326758734830189)
                  ·
                    refine ⟨5056596594872534525561321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13484257586326758734830189 5056596594872534525561321)
                    ·
                      refine ⟨3792447446154400894170991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056596594872534525561321 3792447446154400894170991)
                      ·
                        rfl

theorem cell23_7385765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_7385765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385765 prefixEnd_7385765 := by exact prefixLift 7385765
  have htrace : WordTrace (prefixWord ++ tailWord_7385765) baseStart_7385765 baseEnd_7385765 := by
    simpa [prefixWord, tailWord_7385765, baseEnd_7385765] using wordTrace_append hprefix tailTrace_7385765
  have hstable : (prefixWord ++ tailWord_7385765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385765).length < 2 ^ (prefixWord ++ tailWord_7385765).sum := by decide
  have hdescent : baseEnd_7385765 < baseStart_7385765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385806 : List Nat := [4, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3]
def baseStart_7385806 : Nat := 118140960795 + 7385806 * 2 ^ 59
def prefixEnd_7385806 : Nat := 4983230072969 + 3 ^ 40 * 7385806 * 2
def baseEnd_7385806 : Nat := 3792468498861235233758303

theorem tailTrace_7385806 : CollatzResearch.WordTrace tailWord_7385806 prefixEnd_7385806 3792468498861235233758303 := by
  unfold tailWord_7385806
  simp only [CollatzResearch.WordTrace]
  refine ⟨33672809435061716510638159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179588316986995821390070181 33672809435061716510638159)
  ·
    refine ⟨50509214152592574765957239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33672809435061716510638159 50509214152592574765957239)
    ·
      refine ⟨75763821228888862148935859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50509214152592574765957239 75763821228888862148935859)
      ·
        refine ⟨113645731843333293223403789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75763821228888862148935859 113645731843333293223403789)
        ·
          refine ⟨42617149441249984958776421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113645731843333293223403789 42617149441249984958776421)
          ·
            refine ⟨7990715520234372179770579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42617149441249984958776421 7990715520234372179770579)
            ·
              refine ⟨11986073280351558269655869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7990715520234372179770579 11986073280351558269655869)
              ·
                refine ⟨4494777480131834351120951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11986073280351558269655869 4494777480131834351120951)
                ·
                  refine ⟨6742166220197751526681427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4494777480131834351120951 6742166220197751526681427)
                  ·
                    refine ⟨10113249330296627290022141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6742166220197751526681427 10113249330296627290022141)
                    ·
                      refine ⟨3792468498861235233758303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10113249330296627290022141 3792468498861235233758303)
                      ·
                        rfl

theorem cell23_7385806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_7385806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385806 prefixEnd_7385806 := by exact prefixLift 7385806
  have htrace : WordTrace (prefixWord ++ tailWord_7385806) baseStart_7385806 baseEnd_7385806 := by
    simpa [prefixWord, tailWord_7385806, baseEnd_7385806] using wordTrace_append hprefix tailTrace_7385806
  have hstable : (prefixWord ++ tailWord_7385806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385806).length < 2 ^ (prefixWord ++ tailWord_7385806).sum := by decide
  have hdescent : baseEnd_7385806 < baseStart_7385806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385815 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 5]
def baseStart_7385815 : Nat := 118140960795 + 7385815 * 2 ^ 59
def prefixEnd_7385815 : Nat := 4983230072969 + 3 ^ 40 * 7385815 * 2
def baseEnd_7385815 : Nat := 3792473120187125698545761

theorem tailTrace_7385815 : CollatzResearch.WordTrace tailWord_7385815 prefixEnd_7385815 3792473120187125698545761 := by
  unfold tailWord_7385815
  simp only [CollatzResearch.WordTrace]
  refine ⟨269382803737461126622182899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179588535824974084414788599 269382803737461126622182899)
  ·
    refine ⟨404074205606191689933274349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269382803737461126622182899 404074205606191689933274349)
    ·
      refine ⟨151527827102321883724977881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404074205606191689933274349 151527827102321883724977881)
      ·
        refine ⟨113645870326741412793733411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151527827102321883724977881 113645870326741412793733411)
        ·
          refine ⟨170468805490112119190600117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113645870326741412793733411 170468805490112119190600117)
          ·
            refine ⟨15981450514698011174118761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170468805490112119190600117 15981450514698011174118761)
            ·
              refine ⟨11986087886023508380589071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15981450514698011174118761 11986087886023508380589071)
              ·
                refine ⟨17979131829035262570883607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11986087886023508380589071 17979131829035262570883607)
                ·
                  refine ⟨26968697743552893856325411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17979131829035262570883607 26968697743552893856325411)
                  ·
                    refine ⟨40453046615329340784488117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26968697743552893856325411 40453046615329340784488117)
                    ·
                      refine ⟨3792473120187125698545761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40453046615329340784488117 3792473120187125698545761)
                      ·
                        rfl

theorem cell23_7385815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_7385815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385815 prefixEnd_7385815 := by exact prefixLift 7385815
  have htrace : WordTrace (prefixWord ++ tailWord_7385815) baseStart_7385815 baseEnd_7385815 := by
    simpa [prefixWord, tailWord_7385815, baseEnd_7385815] using wordTrace_append hprefix tailTrace_7385815
  have hstable : (prefixWord ++ tailWord_7385815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385815).length < 2 ^ (prefixWord ++ tailWord_7385815).sum := by decide
  have hdescent : baseEnd_7385815 < baseStart_7385815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385829 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 3, 2, 2]
def baseStart_7385829 : Nat := 118140960795 + 7385829 * 2 ^ 59
def prefixEnd_7385829 : Nat := 4983230072969 + 3 ^ 40 * 7385829 * 2
def baseEnd_7385829 : Nat := 3792480308916288643770697

theorem tailTrace_7385829 : CollatzResearch.WordTrace tailWord_7385829 prefixEnd_7385829 3792480308916288643770697 := by
  unfold tailWord_7385829
  simp only [CollatzResearch.WordTrace]
  refine ⟨269383314359410407013192541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179588876239606938008795027 269383314359410407013192541)
  ·
    refine ⟨101018742884778902629947203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269383314359410407013192541 101018742884778902629947203)
    ·
      refine ⟨151528114327168353944920805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101018742884778902629947203 151528114327168353944920805)
      ·
        refine ⟨28411521436344066364672651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151528114327168353944920805 28411521436344066364672651)
        ·
          refine ⟨42617282154516099547008977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28411521436344066364672651 42617282154516099547008977)
          ·
            refine ⟨31962961615887074660256733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42617282154516099547008977 31962961615887074660256733)
            ·
              refine ⟨11986110605957652997596275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31962961615887074660256733 11986110605957652997596275)
              ·
                refine ⟨17979165908936479496394413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11986110605957652997596275 17979165908936479496394413)
                ·
                  refine ⟨6742187215851179811147905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17979165908936479496394413 6742187215851179811147905)
                  ·
                    refine ⟨5056640411888384858360929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6742187215851179811147905 5056640411888384858360929)
                    ·
                      refine ⟨3792480308916288643770697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056640411888384858360929 3792480308916288643770697)
                      ·
                        rfl

theorem cell23_7385829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_7385829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385829 prefixEnd_7385829 := by exact prefixLift 7385829
  have htrace : WordTrace (prefixWord ++ tailWord_7385829) baseStart_7385829 baseEnd_7385829 := by
    simpa [prefixWord, tailWord_7385829, baseEnd_7385829] using wordTrace_append hprefix tailTrace_7385829
  have hstable : (prefixWord ++ tailWord_7385829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385829).length < 2 ^ (prefixWord ++ tailWord_7385829).sum := by decide
  have hdescent : baseEnd_7385829 < baseStart_7385829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385839 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 2, 4]
def baseStart_7385839 : Nat := 118140960795 + 7385839 * 2 ^ 59
def prefixEnd_7385839 : Nat := 4983230072969 + 3 ^ 40 * 7385839 * 2
def baseEnd_7385839 : Nat := 1264161814574277868215217

theorem tailTrace_7385839 : CollatzResearch.WordTrace tailWord_7385839 prefixEnd_7385839 1264161814574277868215217 := by
  unfold tailWord_7385839
  simp only [CollatzResearch.WordTrace]
  refine ⟨269383679089374178721056571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179589119392916119147371047 269383679089374178721056571)
  ·
    refine ⟨404075518634061268081584857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269383679089374178721056571 404075518634061268081584857)
    ·
      refine ⟨303056638975545951061188643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404075518634061268081584857 303056638975545951061188643)
      ·
        refine ⟨454584958463318926591782965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303056638975545951061188643 454584958463318926591782965)
        ·
          refine ⟨42617339855936149367979653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 454584958463318926591782965 42617339855936149367979653)
          ·
            refine ⟨7990751222988028006496185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42617339855936149367979653 7990751222988028006496185)
            ·
              refine ⟨5993063417241021004872139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7990751222988028006496185 5993063417241021004872139)
              ·
                refine ⟨8989595125861531507308209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5993063417241021004872139 8989595125861531507308209)
                ·
                  refine ⟨6742196344396148630481157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8989595125861531507308209 6742196344396148630481157)
                  ·
                    refine ⟨1264161814574277868215217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6742196344396148630481157 1264161814574277868215217)
                    ·
                      rfl

theorem cell23_7385839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 2, 4].length) (baseStart_7385839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385839 prefixEnd_7385839 := by exact prefixLift 7385839
  have htrace : WordTrace (prefixWord ++ tailWord_7385839) baseStart_7385839 baseEnd_7385839 := by
    simpa [prefixWord, tailWord_7385839, baseEnd_7385839] using wordTrace_append hprefix tailTrace_7385839
  have hstable : (prefixWord ++ tailWord_7385839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385839).length < 2 ^ (prefixWord ++ tailWord_7385839).sum := by decide
  have hdescent : baseEnd_7385839 < baseStart_7385839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385905 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 2, 4, 3]
def baseStart_7385905 : Nat := 118140960795 + 7385905 * 2 ^ 59
def prefixEnd_7385905 : Nat := 4983230072969 + 3 ^ 40 * 7385905 * 2
def baseEnd_7385905 : Nat := 3792519333446030346420347

theorem tailTrace_7385905 : CollatzResearch.WordTrace tailWord_7385905 prefixEnd_7385905 3792519333446030346420347 := by
  unfold tailWord_7385905
  simp only [CollatzResearch.WordTrace]
  refine ⟨269386086307135071992959169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179590724204756714661972779 269386086307135071992959169)
  ·
    refine ⟨202039564730351303994719377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269386086307135071992959169 202039564730351303994719377)
    ·
      refine ⟨151529673547763477996039533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202039564730351303994719377 151529673547763477996039533)
      ·
        refine ⟨56823627580411304248514825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151529673547763477996039533 56823627580411304248514825)
        ·
          refine ⟨42617720685308478186386119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56823627580411304248514825 42617720685308478186386119)
          ·
            refine ⟨63926581027962717279579179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42617720685308478186386119 63926581027962717279579179)
            ·
              refine ⟨95889871541944075919368769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63926581027962717279579179 95889871541944075919368769)
              ·
                refine ⟨71917403656458056939526577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95889871541944075919368769 71917403656458056939526577)
                ·
                  refine ⟨53938052742343542704644933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71917403656458056939526577 53938052742343542704644933)
                  ·
                    refine ⟨10113384889189414257120925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53938052742343542704644933 10113384889189414257120925)
                    ·
                      refine ⟨3792519333446030346420347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10113384889189414257120925 3792519333446030346420347)
                      ·
                        rfl

theorem cell23_7385905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_7385905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385905 prefixEnd_7385905 := by exact prefixLift 7385905
  have htrace : WordTrace (prefixWord ++ tailWord_7385905) baseStart_7385905 baseEnd_7385905 := by
    simpa [prefixWord, tailWord_7385905, baseEnd_7385905] using wordTrace_append hprefix tailTrace_7385905
  have hstable : (prefixWord ++ tailWord_7385905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385905).length < 2 ^ (prefixWord ++ tailWord_7385905).sum := by decide
  have hdescent : baseEnd_7385905 < baseStart_7385905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385955 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 1, 7]
def baseStart_7385955 : Nat := 118140960795 + 7385955 * 2 ^ 59
def prefixEnd_7385955 : Nat := 4983230072969 + 3 ^ 40 * 7385955 * 2
def baseEnd_7385955 : Nat := 1264181669159585050265039

theorem tailTrace_7385955 : CollatzResearch.WordTrace tailWord_7385955 prefixEnd_7385955 1264181669159585050265039 := by
  unfold tailWord_7385955
  simp only [CollatzResearch.WordTrace]
  refine ⟨269387909956953930532279319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179591939971302620354852879 269387909956953930532279319)
  ·
    refine ⟨404081864935430895798418979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269387909956953930532279319 404081864935430895798418979)
    ·
      refine ⟨606122797403146343697628469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404081864935430895798418979 606122797403146343697628469)
      ·
        refine ⟨56824012256544969721652669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 606122797403146343697628469 56824012256544969721652669)
        ·
          refine ⟨21309004596204363645619751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56824012256544969721652669 21309004596204363645619751)
          ·
            refine ⟨31963506894306545468429627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21309004596204363645619751 31963506894306545468429627)
            ·
              refine ⟨47945260341459818202644441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31963506894306545468429627 47945260341459818202644441)
              ·
                refine ⟨35958945256094863651983331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47945260341459818202644441 35958945256094863651983331)
                ·
                  refine ⟨53938417884142295477974997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35958945256094863651983331 53938417884142295477974997)
                  ·
                    refine ⟨1264181669159585050265039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53938417884142295477974997 1264181669159585050265039)
                    ·
                      rfl

theorem cell23_7385955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 7].length) (baseStart_7385955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385955 prefixEnd_7385955 := by exact prefixLift 7385955
  have htrace : WordTrace (prefixWord ++ tailWord_7385955) baseStart_7385955 baseEnd_7385955 := by
    simpa [prefixWord, tailWord_7385955, baseEnd_7385955] using wordTrace_append hprefix tailTrace_7385955
  have hstable : (prefixWord ++ tailWord_7385955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385955).length < 2 ^ (prefixWord ++ tailWord_7385955).sum := by decide
  have hdescent : baseEnd_7385955 < baseStart_7385955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385965 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_7385965 : Nat := 118140960795 + 7385965 * 2 ^ 59
def prefixEnd_7385965 : Nat := 4983230072969 + 3 ^ 40 * 7385965 * 2
def baseEnd_7385965 : Nat := 3792550142285300111670071

theorem tailTrace_7385965 : CollatzResearch.WordTrace tailWord_7385965 prefixEnd_7385965 3792550142285300111670071 := by
  unfold tailWord_7385965
  simp only [CollatzResearch.WordTrace]
  refine ⟨269388274686917702240143349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179592183124611801493428899 269388274686917702240143349)
  ·
    refine ⟨25255150751898534585013439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269388274686917702240143349 25255150751898534585013439)
    ·
      refine ⟨37882726127847801877520159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25255150751898534585013439 37882726127847801877520159)
      ·
        refine ⟨56824089191771702816280239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37882726127847801877520159 56824089191771702816280239)
        ·
          refine ⟨85236133787657554224420359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56824089191771702816280239 85236133787657554224420359)
          ·
            refine ⟨127854200681486331336630539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85236133787657554224420359 127854200681486331336630539)
            ·
              refine ⟨191781301022229497004945809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127854200681486331336630539 191781301022229497004945809)
              ·
                refine ⟨143835975766672122753709357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191781301022229497004945809 143835975766672122753709357)
                ·
                  refine ⟨53938490912502046032641009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143835975766672122753709357 53938490912502046032641009)
                  ·
                    refine ⟨40453868184376534524480757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53938490912502046032641009 40453868184376534524480757)
                    ·
                      refine ⟨3792550142285300111670071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40453868184376534524480757 3792550142285300111670071)
                      ·
                        rfl

theorem cell23_7385965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_7385965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385965 prefixEnd_7385965 := by exact prefixLift 7385965
  have htrace : WordTrace (prefixWord ++ tailWord_7385965) baseStart_7385965 baseEnd_7385965 := by
    simpa [prefixWord, tailWord_7385965, baseEnd_7385965] using wordTrace_append hprefix tailTrace_7385965
  have hstable : (prefixWord ++ tailWord_7385965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385965).length < 2 ^ (prefixWord ++ tailWord_7385965).sum := by decide
  have hdescent : baseEnd_7385965 < baseStart_7385965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385975 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_7385975 : Nat := 118140960795 + 7385975 * 2 ^ 59
def prefixEnd_7385975 : Nat := 4983230072969 + 3 ^ 40 * 7385975 * 2
def baseEnd_7385975 : Nat := 3792555277091845072545025

theorem tailTrace_7385975 : CollatzResearch.WordTrace tailWord_7385975 prefixEnd_7385975 3792555277091845072545025 := by
  unfold tailWord_7385975
  simp only [CollatzResearch.WordTrace]
  refine ⟨269388639416881473948007379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179592426277920982632004919 269388639416881473948007379)
  ·
    refine ⟨404082959125322210922011069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269388639416881473948007379 404082959125322210922011069)
    ·
      refine ⟨151531109671995829095754151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404082959125322210922011069 151531109671995829095754151)
      ·
        refine ⟨227296664507993743643631227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151531109671995829095754151 227296664507993743643631227)
        ·
          refine ⟨340944996761990615465446841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227296664507993743643631227 340944996761990615465446841)
          ·
            refine ⟨255708747571492961599085131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340944996761990615465446841 255708747571492961599085131)
            ·
              refine ⟨383563121357239442398627697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255708747571492961599085131 383563121357239442398627697)
              ·
                refine ⟨287672341017929581798970773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383563121357239442398627697 287672341017929581798970773)
                ·
                  refine ⟨13484640985215449146826755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 287672341017929581798970773 13484640985215449146826755)
                  ·
                    refine ⟨20226961477823173720240133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13484640985215449146826755 20226961477823173720240133)
                    ·
                      refine ⟨3792555277091845072545025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20226961477823173720240133 3792555277091845072545025)
                      ·
                        rfl

theorem cell23_7385975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_7385975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385975 prefixEnd_7385975 := by exact prefixLift 7385975
  have htrace : WordTrace (prefixWord ++ tailWord_7385975) baseStart_7385975 baseEnd_7385975 := by
    simpa [prefixWord, tailWord_7385975, baseEnd_7385975] using wordTrace_append hprefix tailTrace_7385975
  have hstable : (prefixWord ++ tailWord_7385975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385975).length < 2 ^ (prefixWord ++ tailWord_7385975).sum := by decide
  have hdescent : baseEnd_7385975 < baseStart_7385975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7385992 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_7385992 : Nat := 118140960795 + 7385992 * 2 ^ 59
def prefixEnd_7385992 : Nat := 4983230072969 + 3 ^ 40 * 7385992 * 2
def baseEnd_7385992 : Nat := 3792564006262971506032447

theorem tailTrace_7385992 : CollatzResearch.WordTrace tailWord_7385992 prefixEnd_7385992 3792564006262971506032447 := by
  unfold tailWord_7385992
  simp only [CollatzResearch.WordTrace]
  refine ⟨134694629728909942925688115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179592839638546590567584153 134694629728909942925688115)
  ·
    refine ⟨202041944593364914388532173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134694629728909942925688115 202041944593364914388532173)
    ·
      refine ⟨75765729222511842895699565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202041944593364914388532173 75765729222511842895699565)
      ·
        refine ⟨28412148458441941085887337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75765729222511842895699565 28412148458441941085887337)
        ·
          refine ⟨21309111343831455814415503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28412148458441941085887337 21309111343831455814415503)
          ·
            refine ⟨31963667015747183721623255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21309111343831455814415503 31963667015747183721623255)
            ·
              refine ⟨47945500523620775582434883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31963667015747183721623255 47945500523620775582434883)
              ·
                refine ⟨71918250785431163373652325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47945500523620775582434883 71918250785431163373652325)
                ·
                  refine ⟨13484672022268343132559811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71918250785431163373652325 13484672022268343132559811)
                  ·
                    refine ⟨20227008033402514698839717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13484672022268343132559811 20227008033402514698839717)
                    ·
                      refine ⟨3792564006262971506032447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20227008033402514698839717 3792564006262971506032447)
                      ·
                        rfl

theorem cell23_7385992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_7385992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7385992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7385992 prefixEnd_7385992 := by exact prefixLift 7385992
  have htrace : WordTrace (prefixWord ++ tailWord_7385992) baseStart_7385992 baseEnd_7385992 := by
    simpa [prefixWord, tailWord_7385992, baseEnd_7385992] using wordTrace_append hprefix tailTrace_7385992
  have hstable : (prefixWord ++ tailWord_7385992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7385992).length < 2 ^ (prefixWord ++ tailWord_7385992).sum := by decide
  have hdescent : baseEnd_7385992 < baseStart_7385992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7385992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386062 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_7386062 : Nat := 118140960795 + 7386062 * 2 ^ 59
def prefixEnd_7386062 : Nat := 4983230072969 + 3 ^ 40 * 7386062 * 2
def baseEnd_7386062 : Nat := 1264199983302928744052375

theorem tailTrace_7386062 : CollatzResearch.WordTrace tailWord_7386062 prefixEnd_7386062 1264199983302928744052375 := by
  unfold tailWord_7386062
  simp only [CollatzResearch.WordTrace]
  refine ⟨33673976570945785975803055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179594541711710858537616293 33673976570945785975803055)
  ·
    refine ⟨50510964856418678963704583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33673976570945785975803055 50510964856418678963704583)
    ·
      refine ⟨75766447284628018445556875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50510964856418678963704583 75766447284628018445556875)
      ·
        refine ⟨113649670926942027668335313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75766447284628018445556875 113649670926942027668335313)
        ·
          refine ⟨85237253195206520751251485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113649670926942027668335313 85237253195206520751251485)
          ·
            refine ⟨31963969948202445281719307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85237253195206520751251485 31963969948202445281719307)
            ·
              refine ⟨47945954922303667922578961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31963969948202445281719307 47945954922303667922578961)
              ·
                refine ⟨35959466191727750941934221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47945954922303667922578961 35959466191727750941934221)
                ·
                  refine ⟨13484799821897906603225333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35959466191727750941934221 13484799821897906603225333)
                  ·
                    refine ⟨1264199983302928744052375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13484799821897906603225333 1264199983302928744052375)
                    ·
                      rfl

theorem cell23_7386062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_7386062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386062 prefixEnd_7386062 := by exact prefixLift 7386062
  have htrace : WordTrace (prefixWord ++ tailWord_7386062) baseStart_7386062 baseEnd_7386062 := by
    simpa [prefixWord, tailWord_7386062, baseEnd_7386062] using wordTrace_append hprefix tailTrace_7386062
  have hstable : (prefixWord ++ tailWord_7386062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386062).length < 2 ^ (prefixWord ++ tailWord_7386062).sum := by decide
  have hdescent : baseEnd_7386062 < baseStart_7386062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386105 : List Nat := [1, 2, 1, 3, 1, 3, 12]
def baseStart_7386105 : Nat := 118140960795 + 7386105 * 2 ^ 59
def prefixEnd_7386105 : Nat := 4983230072969 + 3 ^ 40 * 7386105 * 2
def baseEnd_7386105 : Nat := 46822494192307772394067

theorem tailTrace_7386105 : CollatzResearch.WordTrace tailWord_7386105 prefixEnd_7386105 46822494192307772394067 := by
  unfold tailWord_7386105
  simp only [CollatzResearch.WordTrace]
  refine ⟨269393380906410506150239769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179595587270940337433493179 269393380906410506150239769)
  ·
    refine ⟨202045035679807879612679827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269393380906410506150239769 202045035679807879612679827)
    ·
      refine ⟨303067553519711819419019741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202045035679807879612679827 303067553519711819419019741)
      ·
        refine ⟨113650332569891932282132403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303067553519711819419019741 113650332569891932282132403)
        ·
          refine ⟨170475498854837898423198605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113650332569891932282132403 170475498854837898423198605)
          ·
            refine ⟨63928312070564211908699477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170475498854837898423198605 63928312070564211908699477)
            ·
              refine ⟨46822494192307772394067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 63928312070564211908699477 46822494192307772394067)
              ·
                rfl

theorem cell23_7386105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 12].length) (baseStart_7386105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386105 prefixEnd_7386105 := by exact prefixLift 7386105
  have htrace : WordTrace (prefixWord ++ tailWord_7386105) baseStart_7386105 baseEnd_7386105 := by
    simpa [prefixWord, tailWord_7386105, baseEnd_7386105] using wordTrace_append hprefix tailTrace_7386105
  have hstable : (prefixWord ++ tailWord_7386105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386105).length < 2 ^ (prefixWord ++ tailWord_7386105).sum := by decide
  have hdescent : baseEnd_7386105 < baseStart_7386105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386115 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 7]
def baseStart_7386115 : Nat := 118140960795 + 7386115 * 2 ^ 59
def prefixEnd_7386115 : Nat := 4983230072969 + 3 ^ 40 * 7386115 * 2
def baseEnd_7386115 : Nat := 3792627164383474524794381

theorem tailTrace_7386115 : CollatzResearch.WordTrace tailWord_7386115 prefixEnd_7386115 3792627164383474524794381 := by
  unfold tailWord_7386115
  simp only [CollatzResearch.WordTrace]
  refine ⟨269393745636374277858103799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179595830424249518572069199 269393745636374277858103799)
  ·
    refine ⟨404090618454561416787155699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269393745636374277858103799 404090618454561416787155699)
    ·
      refine ⟨606135927681842125180733549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404090618454561416787155699 606135927681842125180733549)
      ·
        refine ⟨227300972880690796942775081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606135927681842125180733549 227300972880690796942775081)
        ·
          refine ⟨170475729660518097707081311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227300972880690796942775081 170475729660518097707081311)
          ·
            refine ⟨255713594490777146560621967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170475729660518097707081311 255713594490777146560621967)
            ·
              refine ⟨383570391736165719840932951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255713594490777146560621967 383570391736165719840932951)
              ·
                refine ⟨575355587604248579761399427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383570391736165719840932951 575355587604248579761399427)
                ·
                  refine ⟨863033381406372869642099141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575355587604248579761399427 863033381406372869642099141)
                  ·
                    refine ⟨161818759013694913057893589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 863033381406372869642099141 161818759013694913057893589)
                    ·
                      refine ⟨3792627164383474524794381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161818759013694913057893589 3792627164383474524794381)
                      ·
                        rfl

theorem cell23_7386115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_7386115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386115 prefixEnd_7386115 := by exact prefixLift 7386115
  have htrace : WordTrace (prefixWord ++ tailWord_7386115) baseStart_7386115 baseEnd_7386115 := by
    simpa [prefixWord, tailWord_7386115, baseEnd_7386115] using wordTrace_append hprefix tailTrace_7386115
  have hstable : (prefixWord ++ tailWord_7386115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386115).length < 2 ^ (prefixWord ++ tailWord_7386115).sum := by decide
  have hdescent : baseEnd_7386115 < baseStart_7386115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386130 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7386130 : Nat := 118140960795 + 7386130 * 2 ^ 59
def prefixEnd_7386130 : Nat := 4983230072969 + 3 ^ 40 * 7386130 * 2
def baseEnd_7386130 : Nat := 1264211622197763988702271

theorem tailTrace_7386130 : CollatzResearch.WordTrace tailWord_7386130 prefixEnd_7386130 1264211622197763988702271 := by
  unfold tailWord_7386130
  simp only [CollatzResearch.WordTrace]
  refine ⟨67348573182829983854974961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179596195154213290279933229 67348573182829983854974961)
  ·
    refine ⟨50511429887122487891231221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67348573182829983854974961 50511429887122487891231221)
    ·
      refine ⟨4735446551917733239802927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50511429887122487891231221 4735446551917733239802927)
      ·
        refine ⟨7103169827876599859704391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4735446551917733239802927 7103169827876599859704391)
        ·
          refine ⟨10654754741814899789556587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7103169827876599859704391 10654754741814899789556587)
          ·
            refine ⟨15982132112722349684334881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10654754741814899789556587 15982132112722349684334881)
            ·
              refine ⟨11986599084541762263251161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15982132112722349684334881 11986599084541762263251161)
              ·
                refine ⟨8989949313406321697438371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11986599084541762263251161 8989949313406321697438371)
                ·
                  refine ⟨13484923970109482546157557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8989949313406321697438371 13484923970109482546157557)
                  ·
                    refine ⟨1264211622197763988702271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13484923970109482546157557 1264211622197763988702271)
                    ·
                      rfl

theorem cell23_7386130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7386130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386130 prefixEnd_7386130 := by exact prefixLift 7386130
  have htrace : WordTrace (prefixWord ++ tailWord_7386130) baseStart_7386130 baseEnd_7386130 := by
    simpa [prefixWord, tailWord_7386130, baseEnd_7386130] using wordTrace_append hprefix tailTrace_7386130
  have hstable : (prefixWord ++ tailWord_7386130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386130).length < 2 ^ (prefixWord ++ tailWord_7386130).sum := by decide
  have hdescent : baseEnd_7386130 < baseStart_7386130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386136 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 1, 2, 3]
def baseStart_7386136 : Nat := 118140960795 + 7386136 * 2 ^ 59
def prefixEnd_7386136 : Nat := 4983230072969 + 3 ^ 40 * 7386136 * 2
def baseEnd_7386136 : Nat := 3792637947477218942631785

theorem tailTrace_7386136 : CollatzResearch.WordTrace tailWord_7386136 prefixEnd_7386136 3792637947477218942631785 := by
  unfold tailWord_7386136
  simp only [CollatzResearch.WordTrace]
  refine ⟨134697255784649099222309131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179596341046198798963078841 134697255784649099222309131)
  ·
    refine ⟨202045883676973648833463697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134697255784649099222309131 202045883676973648833463697)
    ·
      refine ⟨151534412757730236625097773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202045883676973648833463697 151534412757730236625097773)
      ·
        refine ⟨56825404784148838734411665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151534412757730236625097773 56825404784148838734411665)
        ·
          refine ⟨42619053588111629050808749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56825404784148838734411665 42619053588111629050808749)
          ·
            refine ⟨15982145095541860894053281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42619053588111629050808749 15982145095541860894053281)
            ·
              refine ⟨11986608821656395670539961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15982145095541860894053281 11986608821656395670539961)
              ·
                refine ⟨8989956616242296752904971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11986608821656395670539961 8989956616242296752904971)
                ·
                  refine ⟨13484934924363445129357457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8989956616242296752904971 13484934924363445129357457)
                  ·
                    refine ⟨10113701193272583847018093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13484934924363445129357457 10113701193272583847018093)
                    ·
                      refine ⟨3792637947477218942631785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10113701193272583847018093 3792637947477218942631785)
                      ·
                        rfl

theorem cell23_7386136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_7386136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386136 prefixEnd_7386136 := by exact prefixLift 7386136
  have htrace : WordTrace (prefixWord ++ tailWord_7386136) baseStart_7386136 baseEnd_7386136 := by
    simpa [prefixWord, tailWord_7386136, baseEnd_7386136] using wordTrace_append hprefix tailTrace_7386136
  have hstable : (prefixWord ++ tailWord_7386136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386136).length < 2 ^ (prefixWord ++ tailWord_7386136).sum := by decide
  have hdescent : baseEnd_7386136 < baseStart_7386136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386149 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 6, 1, 3]
def baseStart_7386149 : Nat := 118140960795 + 7386149 * 2 ^ 59
def prefixEnd_7386149 : Nat := 4983230072969 + 3 ^ 40 * 7386149 * 2
def baseEnd_7386149 : Nat := 3792644622725727391769225

theorem tailTrace_7386149 : CollatzResearch.WordTrace tailWord_7386149 prefixEnd_7386149 3792644622725727391769225 := by
  unfold tailWord_7386149
  simp only [CollatzResearch.WordTrace]
  refine ⟨269394985718251101664841501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179596657145500734443227667 269394985718251101664841501)
  ·
    refine ⟨101023119644344163124315563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269394985718251101664841501 101023119644344163124315563)
    ·
      refine ⟨151534679466516244686473345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101023119644344163124315563 151534679466516244686473345)
      ·
        refine ⟨113651009599887183514855009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151534679466516244686473345 113651009599887183514855009)
        ·
          refine ⟨85238257199915387636141257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113651009599887183514855009 85238257199915387636141257)
          ·
            refine ⟨63928692899936540727105943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85238257199915387636141257 63928692899936540727105943)
            ·
              refine ⟨95893039349904811090658915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63928692899936540727105943 95893039349904811090658915)
              ·
                refine ⟨143839559024857216635988373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95893039349904811090658915 143839559024857216635988373)
                ·
                  refine ⟨6742479329290182029811955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143839559024857216635988373 6742479329290182029811955)
                  ·
                    refine ⟨10113718993935273044717933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6742479329290182029811955 10113718993935273044717933)
                    ·
                      refine ⟨3792644622725727391769225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10113718993935273044717933 3792644622725727391769225)
                      ·
                        rfl

theorem cell23_7386149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_7386149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386149 prefixEnd_7386149 := by exact prefixLift 7386149
  have htrace : WordTrace (prefixWord ++ tailWord_7386149) baseStart_7386149 baseEnd_7386149 := by
    simpa [prefixWord, tailWord_7386149, baseEnd_7386149] using wordTrace_append hprefix tailTrace_7386149
  have hstable : (prefixWord ++ tailWord_7386149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386149).length < 2 ^ (prefixWord ++ tailWord_7386149).sum := by decide
  have hdescent : baseEnd_7386149 < baseStart_7386149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386162 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_7386162 : Nat := 118140960795 + 7386162 * 2 ^ 59
def prefixEnd_7386162 : Nat := 4983230072969 + 3 ^ 40 * 7386162 * 2
def baseEnd_7386162 : Nat := 3792651297974235840906665

theorem tailTrace_7386162 : CollatzResearch.WordTrace tailWord_7386162 prefixEnd_7386162 3792651297974235840906665 := by
  unfold tailWord_7386162
  simp only [CollatzResearch.WordTrace]
  refine ⟨67348864966801001221266185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179596973244802669923376493 67348864966801001221266185)
  ·
    refine ⟨50511648725100750915949639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67348864966801001221266185 50511648725100750915949639)
    ·
      refine ⟨75767473087651126373924459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50511648725100750915949639 75767473087651126373924459)
      ·
        refine ⟨113651209631476689560886689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75767473087651126373924459 113651209631476689560886689)
        ·
          refine ⟨85238407223607517170665017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113651209631476689560886689 85238407223607517170665017)
          ·
            refine ⟨63928805417705637877998763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85238407223607517170665017 63928805417705637877998763)
            ·
              refine ⟨95893208126558456816998145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63928805417705637877998763 95893208126558456816998145)
              ·
                refine ⟨71919906094918842612748609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95893208126558456816998145 71919906094918842612748609)
                ·
                  refine ⟨53939929571189131959561457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71919906094918842612748609 53939929571189131959561457)
                  ·
                    refine ⟨40454947178391848969671093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53939929571189131959561457 40454947178391848969671093)
                    ·
                      refine ⟨3792651297974235840906665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40454947178391848969671093 3792651297974235840906665)
                      ·
                        rfl

theorem cell23_7386162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_7386162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386162 prefixEnd_7386162 := by exact prefixLift 7386162
  have htrace : WordTrace (prefixWord ++ tailWord_7386162) baseStart_7386162 baseEnd_7386162 := by
    simpa [prefixWord, tailWord_7386162, baseEnd_7386162] using wordTrace_append hprefix tailTrace_7386162
  have hstable : (prefixWord ++ tailWord_7386162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386162).length < 2 ^ (prefixWord ++ tailWord_7386162).sum := by decide
  have hdescent : baseEnd_7386162 < baseStart_7386162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386183 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 2, 1, 3]
def baseStart_7386183 : Nat := 118140960795 + 7386183 * 2 ^ 59
def prefixEnd_7386183 : Nat := 4983230072969 + 3 ^ 40 * 7386183 * 2
def baseEnd_7386183 : Nat := 3792662081067980258744069

theorem tailTrace_7386183 : CollatzResearch.WordTrace tailWord_7386183 prefixEnd_7386183 3792662081067980258744069 := by
  unfold tailWord_7386183
  simp only [CollatzResearch.WordTrace]
  refine ⟨269396225800127925471579203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179597483866751950314386135 269396225800127925471579203)
  ·
    refine ⟨404094338700191888207368805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269396225800127925471579203 404094338700191888207368805)
    ·
      refine ⟨75767688506285979038881651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404094338700191888207368805 75767688506285979038881651)
      ·
        refine ⟨113651532759428968558322477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75767688506285979038881651 113651532759428968558322477)
        ·
          refine ⟨42619324784785863209370929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113651532759428968558322477 42619324784785863209370929)
          ·
            refine ⟨31964493588589397407028197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42619324784785863209370929 31964493588589397407028197)
            ·
              refine ⟨5993342547860512013817787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31964493588589397407028197 5993342547860512013817787)
              ·
                refine ⟨8990013821790768020726681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5993342547860512013817787 8990013821790768020726681)
                ·
                  refine ⟨6742510366343076015545011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8990013821790768020726681 6742510366343076015545011)
                  ·
                    refine ⟨10113765549514614023317517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6742510366343076015545011 10113765549514614023317517)
                    ·
                      refine ⟨3792662081067980258744069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10113765549514614023317517 3792662081067980258744069)
                      ·
                        rfl

theorem cell23_7386183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_7386183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386183 prefixEnd_7386183 := by exact prefixLift 7386183
  have htrace : WordTrace (prefixWord ++ tailWord_7386183) baseStart_7386183 baseEnd_7386183 := by
    simpa [prefixWord, tailWord_7386183, baseEnd_7386183] using wordTrace_append hprefix tailTrace_7386183
  have hstable : (prefixWord ++ tailWord_7386183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386183).length < 2 ^ (prefixWord ++ tailWord_7386183).sum := by decide
  have hdescent : baseEnd_7386183 < baseStart_7386183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386202 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_7386202 : Nat := 118140960795 + 7386202 * 2 ^ 59
def prefixEnd_7386202 : Nat := 4983230072969 + 3 ^ 40 * 7386202 * 2
def baseEnd_7386202 : Nat := 3792671837200415684406481

theorem tailTrace_7386202 : CollatzResearch.WordTrace tailWord_7386202 prefixEnd_7386202 3792671837200415684406481 := by
  unfold tailWord_7386202
  simp only [CollatzResearch.WordTrace]
  refine ⟨67349229696764772929130215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179597945858039394477680573 67349229696764772929130215)
  ·
    refine ⟨101023844545147159393695323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67349229696764772929130215 101023844545147159393695323)
    ·
      refine ⟨151535766817720739090542985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101023844545147159393695323 151535766817720739090542985)
      ·
        refine ⟨113651825113290554317907239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151535766817720739090542985 113651825113290554317907239)
        ·
          refine ⟨170477737669935831476860859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113651825113290554317907239 170477737669935831476860859)
          ·
            refine ⟨255716606504903747215291289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170477737669935831476860859 255716606504903747215291289)
            ·
              refine ⟨191787454878677810411468467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255716606504903747215291289 191787454878677810411468467)
              ·
                refine ⟨287681182318016715617202701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191787454878677810411468467 287681182318016715617202701)
                ·
                  refine ⟨107880443369256268356451013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287681182318016715617202701 107880443369256268356451013)
                  ·
                    refine ⟨20227583131735550316834565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107880443369256268356451013 20227583131735550316834565)
                    ·
                      refine ⟨3792671837200415684406481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20227583131735550316834565 3792671837200415684406481)
                      ·
                        rfl

theorem cell23_7386202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_7386202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386202 prefixEnd_7386202 := by exact prefixLift 7386202
  have htrace : WordTrace (prefixWord ++ tailWord_7386202) baseStart_7386202 baseEnd_7386202 := by
    simpa [prefixWord, tailWord_7386202, baseEnd_7386202] using wordTrace_append hprefix tailTrace_7386202
  have hstable : (prefixWord ++ tailWord_7386202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386202).length < 2 ^ (prefixWord ++ tailWord_7386202).sum := by decide
  have hdescent : baseEnd_7386202 < baseStart_7386202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386223 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 2, 2, 2]
def baseStart_7386223 : Nat := 118140960795 + 7386223 * 2 ^ 59
def prefixEnd_7386223 : Nat := 4983230072969 + 3 ^ 40 * 7386223 * 2
def baseEnd_7386223 : Nat := 3792682620294160102243885

theorem tailTrace_7386223 : CollatzResearch.WordTrace tailWord_7386223 prefixEnd_7386223 3792682620294160102243885 := by
  unfold tailWord_7386223
  simp only [CollatzResearch.WordTrace]
  refine ⟨269397684719983012303035323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179598456479988674868690215 269397684719983012303035323)
  ·
    refine ⟨404096527079974518454552985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269397684719983012303035323 404096527079974518454552985)
    ·
      refine ⟨303072395309980888840914739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404096527079974518454552985 303072395309980888840914739)
      ·
        refine ⟨454608592964971333261372109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303072395309980888840914739 454608592964971333261372109)
        ·
          refine ⟨170478222361864249973014541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454608592964971333261372109 170478222361864249973014541)
          ·
            refine ⟨63929333385699093739880453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170478222361864249973014541 63929333385699093739880453)
            ·
              refine ⟨11986750009818580076227585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63929333385699093739880453 11986750009818580076227585)
              ·
                refine ⟨8990062507363935057170689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11986750009818580076227585 8990062507363935057170689)
                ·
                  refine ⟨6742546880522951292878017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8990062507363935057170689 6742546880522951292878017)
                  ·
                    refine ⟨5056910160392213469658513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6742546880522951292878017 5056910160392213469658513)
                    ·
                      refine ⟨3792682620294160102243885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056910160392213469658513 3792682620294160102243885)
                      ·
                        rfl

theorem cell23_7386223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 2, 2].length) (baseStart_7386223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386223 prefixEnd_7386223 := by exact prefixLift 7386223
  have htrace : WordTrace (prefixWord ++ tailWord_7386223) baseStart_7386223 baseEnd_7386223 := by
    simpa [prefixWord, tailWord_7386223, baseEnd_7386223] using wordTrace_append hprefix tailTrace_7386223
  have hstable : (prefixWord ++ tailWord_7386223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386223).length < 2 ^ (prefixWord ++ tailWord_7386223).sum := by decide
  have hdescent : baseEnd_7386223 < baseStart_7386223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386252 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_7386252 : Nat := 118140960795 + 7386252 * 2 ^ 59
def prefixEnd_7386252 : Nat := 4983230072969 + 3 ^ 40 * 7386252 * 2
def baseEnd_7386252 : Nat := 3792697511233140488781251

theorem tailTrace_7386252 : CollatzResearch.WordTrace tailWord_7386252 prefixEnd_7386252 3792697511233140488781251 := by
  unfold tailWord_7386252
  simp only [CollatzResearch.WordTrace]
  refine ⟨134699371218438975127920505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179599161624585300170560673 134699371218438975127920505)
  ·
    refine ⟨101024528413829231345940379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134699371218438975127920505 101024528413829231345940379)
    ·
      refine ⟨151536792620743847018910569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101024528413829231345940379 151536792620743847018910569)
      ·
        refine ⟨113652594465557885264182927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151536792620743847018910569 113652594465557885264182927)
        ·
          refine ⟨170478891698336827896274391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113652594465557885264182927 170478891698336827896274391)
          ·
            refine ⟨255718337547505241844411587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170478891698336827896274391 255718337547505241844411587)
            ·
              refine ⟨383577506321257862766617381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255718337547505241844411587 383577506321257862766617381)
              ·
                refine ⟨71920782435235849268740759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383577506321257862766617381 71920782435235849268740759)
                ·
                  refine ⟨107881173652853773903111139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71920782435235849268740759 107881173652853773903111139)
                  ·
                    refine ⟨161821760479280660854666709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107881173652853773903111139 161821760479280660854666709)
                    ·
                      refine ⟨3792697511233140488781251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161821760479280660854666709 3792697511233140488781251)
                      ·
                        rfl

theorem cell23_7386252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_7386252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386252 prefixEnd_7386252 := by exact prefixLift 7386252
  have htrace : WordTrace (prefixWord ++ tailWord_7386252) baseStart_7386252 baseEnd_7386252 := by
    simpa [prefixWord, tailWord_7386252, baseEnd_7386252] using wordTrace_append hprefix tailTrace_7386252
  have hstable : (prefixWord ++ tailWord_7386252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386252).length < 2 ^ (prefixWord ++ tailWord_7386252).sum := by decide
  have hdescent : baseEnd_7386252 < baseStart_7386252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386259 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 2, 5]
def baseStart_7386259 : Nat := 118140960795 + 7386259 * 2 ^ 59
def prefixEnd_7386259 : Nat := 4983230072969 + 3 ^ 40 * 7386259 * 2
def baseEnd_7386259 : Nat := 1264233701865907320464573

theorem tailTrace_7386259 : CollatzResearch.WordTrace tailWord_7386259 prefixEnd_7386259 1264233701865907320464573 := by
  unfold tailWord_7386259
  simp only [CollatzResearch.WordTrace]
  refine ⟨269398997747852590451345831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179599331831901726967563887 269398997747852590451345831)
  ·
    refine ⟨404098496621778885677018747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269398997747852590451345831 404098496621778885677018747)
    ·
      refine ⟨606147744932668328515528121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404098496621778885677018747 606147744932668328515528121)
      ·
        refine ⟨454610808699501246386646091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606147744932668328515528121 454610808699501246386646091)
        ·
          refine ⟨681916213049251869579969137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454610808699501246386646091 681916213049251869579969137)
          ·
            refine ⟨511437159786938902184976853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681916213049251869579969137 511437159786938902184976853)
            ·
              refine ⟨11986808432506380519960395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 511437159786938902184976853 11986808432506380519960395)
              ·
                refine ⟨17980212648759570779940593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11986808432506380519960395 17980212648759570779940593)
                ·
                  refine ⟨13485159486569678084955445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17980212648759570779940593 13485159486569678084955445)
                  ·
                    refine ⟨1264233701865907320464573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13485159486569678084955445 1264233701865907320464573)
                    ·
                      rfl

theorem cell23_7386259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 5].length) (baseStart_7386259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386259 prefixEnd_7386259 := by exact prefixLift 7386259
  have htrace : WordTrace (prefixWord ++ tailWord_7386259) baseStart_7386259 baseEnd_7386259 := by
    simpa [prefixWord, tailWord_7386259, baseEnd_7386259] using wordTrace_append hprefix tailTrace_7386259
  have hstable : (prefixWord ++ tailWord_7386259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386259).length < 2 ^ (prefixWord ++ tailWord_7386259).sum := by decide
  have hdescent : baseEnd_7386259 < baseStart_7386259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386274 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_7386274 : Nat := 118140960795 + 7386274 * 2 ^ 59
def prefixEnd_7386274 : Nat := 4983230072969 + 3 ^ 40 * 7386274 * 2
def baseEnd_7386274 : Nat := 3792708807807539402706151

theorem tailTrace_7386274 : CollatzResearch.WordTrace tailWord_7386274 prefixEnd_7386274 3792708807807539402706151 := by
  unfold tailWord_7386274
  simp only [CollatzResearch.WordTrace]
  refine ⟨67349886210699562003285469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179599696561865498675427917 67349886210699562003285469)
  ·
    refine ⟨25256207329012335751232051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67349886210699562003285469 25256207329012335751232051)
    ·
      refine ⟨37884310993518503626848077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25256207329012335751232051 37884310993518503626848077)
      ·
        refine ⟨14206616622569438860068029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37884310993518503626848077 14206616622569438860068029)
        ·
          refine ⟨5327481233463539572525511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14206616622569438860068029 5327481233463539572525511)
          ·
            refine ⟨7991221850195309358788267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5327481233463539572525511 7991221850195309358788267)
            ·
              refine ⟨11986832775292964038182401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7991221850195309358788267 11986832775292964038182401)
              ·
                refine ⟨8990124581469723028636801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11986832775292964038182401 8990124581469723028636801)
                ·
                  refine ⟨6742593436102292271477601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8990124581469723028636801 6742593436102292271477601)
                  ·
                    refine ⟨5056945077076719203608201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6742593436102292271477601 5056945077076719203608201)
                    ·
                      refine ⟨3792708807807539402706151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5056945077076719203608201 3792708807807539402706151)
                      ·
                        rfl

theorem cell23_7386274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_7386274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386274 prefixEnd_7386274 := by exact prefixLift 7386274
  have htrace : WordTrace (prefixWord ++ tailWord_7386274) baseStart_7386274 baseEnd_7386274 := by
    simpa [prefixWord, tailWord_7386274, baseEnd_7386274] using wordTrace_append hprefix tailTrace_7386274
  have hstable : (prefixWord ++ tailWord_7386274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386274).length < 2 ^ (prefixWord ++ tailWord_7386274).sum := by decide
  have hdescent : baseEnd_7386274 < baseStart_7386274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386299 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 3]
def baseStart_7386299 : Nat := 118140960795 + 7386299 * 2 ^ 59
def prefixEnd_7386299 : Nat := 4983230072969 + 3 ^ 40 * 7386299 * 2
def baseEnd_7386299 : Nat := 3792721644823901804893535

theorem tailTrace_7386299 : CollatzResearch.WordTrace tailWord_7386299 prefixEnd_7386299 3792721644823901804893535 := by
  unfold tailWord_7386299
  simp only [CollatzResearch.WordTrace]
  refine ⟨269400456667707677282801951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179600304445138451521867967 269400456667707677282801951)
  ·
    refine ⟨404100685001561515924202927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269400456667707677282801951 404100685001561515924202927)
    ·
      refine ⟨606151027502342273886304391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404100685001561515924202927 606151027502342273886304391)
      ·
        refine ⟨909226541253513410829456587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606151027502342273886304391 909226541253513410829456587)
        ·
          refine ⟨1363839811880270116244184881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909226541253513410829456587 1363839811880270116244184881)
          ·
            refine ⟨1022879858910202587183138661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363839811880270116244184881 1022879858910202587183138661)
            ·
              refine ⟨191789973545662985096838499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1022879858910202587183138661 191789973545662985096838499)
              ·
                refine ⟨287684960318494477645257749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191789973545662985096838499 287684960318494477645257749)
                ·
                  refine ⟨13485232514929428639621457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 287684960318494477645257749 13485232514929428639621457)
                  ·
                    refine ⟨10113924386197071479716093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13485232514929428639621457 10113924386197071479716093)
                    ·
                      refine ⟨3792721644823901804893535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10113924386197071479716093 3792721644823901804893535)
                      ·
                        rfl

theorem cell23_7386299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 3].length) (baseStart_7386299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386299 prefixEnd_7386299 := by exact prefixLift 7386299
  have htrace : WordTrace (prefixWord ++ tailWord_7386299) baseStart_7386299 baseEnd_7386299 := by
    simpa [prefixWord, tailWord_7386299, baseEnd_7386299] using wordTrace_append hprefix tailTrace_7386299
  have hstable : (prefixWord ++ tailWord_7386299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386299).length < 2 ^ (prefixWord ++ tailWord_7386299).sum := by decide
  have hdescent : baseEnd_7386299 < baseStart_7386299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386373 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 2, 3, 2]
def baseStart_7386373 : Nat := 118140960795 + 7386373 * 2 ^ 59
def prefixEnd_7386373 : Nat := 4983230072969 + 3 ^ 40 * 7386373 * 2
def baseEnd_7386373 : Nat := 3792759642392334515368195

theorem tailTrace_7386373 : CollatzResearch.WordTrace tailWord_7386373 prefixEnd_7386373 3792759642392334515368195 := by
  unfold tailWord_7386373
  simp only [CollatzResearch.WordTrace]
  refine ⟨269403155669439587920995773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179602103779626391947330515 269403155669439587920995773)
  ·
    refine ⟨101026183376039845470373415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269403155669439587920995773 101026183376039845470373415)
    ·
      refine ⟨151539275064059768205560123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101026183376039845470373415 151539275064059768205560123)
      ·
        refine ⟨227308912596089652308340185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151539275064059768205560123 227308912596089652308340185)
        ·
          refine ⟨170481684447067239231255139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227308912596089652308340185 170481684447067239231255139)
          ·
            refine ⟨255722526670600858846882709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170481684447067239231255139 255722526670600858846882709)
            ·
              refine ⟨11986993437684415258447627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255722526670600858846882709 11986993437684415258447627)
              ·
                refine ⟨17980490156526622887671441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11986993437684415258447627 17980490156526622887671441)
                ·
                  refine ⟨13485367617394967165753581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17980490156526622887671441 13485367617394967165753581)
                  ·
                    refine ⟨5057012856523112687157593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13485367617394967165753581 5057012856523112687157593)
                    ·
                      refine ⟨3792759642392334515368195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057012856523112687157593 3792759642392334515368195)
                      ·
                        rfl

theorem cell23_7386373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_7386373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386373 prefixEnd_7386373 := by exact prefixLift 7386373
  have htrace : WordTrace (prefixWord ++ tailWord_7386373) baseStart_7386373 baseEnd_7386373 := by
    simpa [prefixWord, tailWord_7386373, baseEnd_7386373] using wordTrace_append hprefix tailTrace_7386373
  have hstable : (prefixWord ++ tailWord_7386373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386373).length < 2 ^ (prefixWord ++ tailWord_7386373).sum := by decide
  have hdescent : baseEnd_7386373 < baseStart_7386373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386379 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 3, 6]
def baseStart_7386379 : Nat := 118140960795 + 7386379 * 2 ^ 59
def prefixEnd_7386379 : Nat := 4983230072969 + 3 ^ 40 * 7386379 * 2
def baseEnd_7386379 : Nat := 1264254241092087163964389

theorem tailTrace_7386379 : CollatzResearch.WordTrace tailWord_7386379 prefixEnd_7386379 1264254241092087163964389 := by
  unfold tailWord_7386379
  simp only [CollatzResearch.WordTrace]
  refine ⟨269403374507417850945714191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179602249671611900630476127 269403374507417850945714191)
  ·
    refine ⟨404105061761126776418571287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269403374507417850945714191 404105061761126776418571287)
    ·
      refine ⟨606157592641690164627856931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404105061761126776418571287 606157592641690164627856931)
      ·
        refine ⟨909236388962535246941785397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606157592641690164627856931 909236388962535246941785397)
        ·
          refine ⟨85240911465237679400792381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 909236388962535246941785397 85240911465237679400792381)
          ·
            refine ⟨31965341799464129775297143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85240911465237679400792381 31965341799464129775297143)
            ·
              refine ⟨47948012699196194662945715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31965341799464129775297143 47948012699196194662945715)
              ·
                refine ⟨71922019048794291994418573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47948012699196194662945715 71922019048794291994418573)
                ·
                  refine ⟨26970757143297859497906965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71922019048794291994418573 26970757143297859497906965)
                  ·
                    refine ⟨1264254241092087163964389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26970757143297859497906965 1264254241092087163964389)
                    ·
                      rfl

theorem cell23_7386379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 6].length) (baseStart_7386379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386379 prefixEnd_7386379 := by exact prefixLift 7386379
  have htrace : WordTrace (prefixWord ++ tailWord_7386379) baseStart_7386379 baseEnd_7386379 := by
    simpa [prefixWord, tailWord_7386379, baseEnd_7386379] using wordTrace_append hprefix tailTrace_7386379
  have hstable : (prefixWord ++ tailWord_7386379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386379).length < 2 ^ (prefixWord ++ tailWord_7386379).sum := by decide
  have hdescent : baseEnd_7386379 < baseStart_7386379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386396 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_7386396 : Nat := 118140960795 + 7386396 * 2 ^ 59
def prefixEnd_7386396 : Nat := 4983230072969 + 3 ^ 40 * 7386396 * 2
def baseEnd_7386396 : Nat := 1264257150815795975126863

theorem tailTrace_7386396 : CollatzResearch.WordTrace tailWord_7386396 prefixEnd_7386396 1264257150815795975126863 := by
  unfold tailWord_7386396
  simp only [CollatzResearch.WordTrace]
  refine ⟨134701997274178131424541521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179602663032237508566055361 134701997274178131424541521)
  ·
    refine ⟨101026497955633598568406141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134701997274178131424541521 101026497955633598568406141)
    ·
      refine ⟨37884936733362599463152303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101026497955633598568406141 37884936733362599463152303)
      ·
        refine ⟨56827405100043899194728455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37884936733362599463152303 56827405100043899194728455)
        ·
          refine ⟨85241107650065848792092683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56827405100043899194728455 85241107650065848792092683)
          ·
            refine ⟨127861661475098773188139025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85241107650065848792092683 127861661475098773188139025)
            ·
              refine ⟨95896246106324079891104269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127861661475098773188139025 95896246106324079891104269)
              ·
                refine ⟨35961092289871529959164101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95896246106324079891104269 35961092289871529959164101)
                ·
                  refine ⟨6742704804350911867343269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35961092289871529959164101 6742704804350911867343269)
                  ·
                    refine ⟨1264257150815795975126863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6742704804350911867343269 1264257150815795975126863)
                    ·
                      rfl

theorem cell23_7386396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_7386396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386396 prefixEnd_7386396 := by exact prefixLift 7386396
  have htrace : WordTrace (prefixWord ++ tailWord_7386396) baseStart_7386396 baseEnd_7386396 := by
    simpa [prefixWord, tailWord_7386396, baseEnd_7386396] using wordTrace_append hprefix tailTrace_7386396
  have hstable : (prefixWord ++ tailWord_7386396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386396).length < 2 ^ (prefixWord ++ tailWord_7386396).sum := by decide
  have hdescent : baseEnd_7386396 < baseStart_7386396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386397 : List Nat := [1, 4, 2, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_7386397 : Nat := 118140960795 + 7386397 * 2 ^ 59
def prefixEnd_7386397 : Nat := 4983230072969 + 3 ^ 40 * 7386397 * 2
def baseEnd_7386397 : Nat := 3792771965928042421468085

theorem tailTrace_7386397 : CollatzResearch.WordTrace tailWord_7386397 prefixEnd_7386397 3792771965928042421468085 := by
  unfold tailWord_7386397
  simp only [CollatzResearch.WordTrace]
  refine ⟨269404031021352640019869445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179602687347568426679912963 269404031021352640019869445)
  ·
    refine ⟨50513255816503620003725521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269404031021352640019869445 50513255816503620003725521)
    ·
      refine ⟨37884941862377715002794141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50513255816503620003725521 37884941862377715002794141)
      ·
        refine ⟨14206853198391643126047803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37884941862377715002794141 14206853198391643126047803)
        ·
          refine ⟨21310279797587464689071705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14206853198391643126047803 21310279797587464689071705)
          ·
            refine ⟨15982709848190598516803779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21310279797587464689071705 15982709848190598516803779)
            ·
              refine ⟨23974064772285897775205669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15982709848190598516803779 23974064772285897775205669)
              ·
                refine ⟨4495137144803605832851063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23974064772285897775205669 4495137144803605832851063)
                ·
                  refine ⟨6742705717205408749276595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4495137144803605832851063 6742705717205408749276595)
                  ·
                    refine ⟨10114058575808113123914893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6742705717205408749276595 10114058575808113123914893)
                    ·
                      refine ⟨3792771965928042421468085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10114058575808113123914893 3792771965928042421468085)
                      ·
                        rfl

theorem cell23_7386397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_7386397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386397 prefixEnd_7386397 := by exact prefixLift 7386397
  have htrace : WordTrace (prefixWord ++ tailWord_7386397) baseStart_7386397 baseEnd_7386397 := by
    simpa [prefixWord, tailWord_7386397, baseEnd_7386397] using wordTrace_append hprefix tailTrace_7386397
  have hstable : (prefixWord ++ tailWord_7386397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386397).length < 2 ^ (prefixWord ++ tailWord_7386397).sum := by decide
  have hdescent : baseEnd_7386397 < baseStart_7386397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386413 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_7386413 : Nat := 118140960795 + 7386413 * 2 ^ 59
def prefixEnd_7386413 : Nat := 4983230072969 + 3 ^ 40 * 7386413 * 2
def baseEnd_7386413 : Nat := 1264260060539504786289337

theorem tailTrace_7386413 : CollatzResearch.WordTrace tailWord_7386413 prefixEnd_7386413 1264260060539504786289337 := by
  unfold tailWord_7386413
  simp only [CollatzResearch.WordTrace]
  refine ⟨269404614589294674752451893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179603076392863116501634595 269404614589294674752451893)
  ·
    refine ⟨25256682617746375758042365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269404614589294674752451893 25256682617746375758042365)
    ·
      refine ⟨9471255981654890909265887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25256682617746375758042365 9471255981654890909265887)
      ·
        refine ⟨14206883972482336363898831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9471255981654890909265887 14206883972482336363898831)
        ·
          refine ⟨21310325958723504545848247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14206883972482336363898831 21310325958723504545848247)
          ·
            refine ⟨31965488938085256818772371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21310325958723504545848247 31965488938085256818772371)
            ·
              refine ⟨47948233407127885228158557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31965488938085256818772371 47948233407127885228158557)
              ·
                refine ⟨17980587527672956960559459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47948233407127885228158557 17980587527672956960559459)
                ·
                  refine ⟨26970881291509435440839189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17980587527672956960559459 26970881291509435440839189)
                  ·
                    refine ⟨1264260060539504786289337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26970881291509435440839189 1264260060539504786289337)
                    ·
                      rfl

theorem cell23_7386413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_7386413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386413 prefixEnd_7386413 := by exact prefixLift 7386413
  have htrace : WordTrace (prefixWord ++ tailWord_7386413) baseStart_7386413 baseEnd_7386413 := by
    simpa [prefixWord, tailWord_7386413, baseEnd_7386413] using wordTrace_append hprefix tailTrace_7386413
  have hstable : (prefixWord ++ tailWord_7386413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386413).length < 2 ^ (prefixWord ++ tailWord_7386413).sum := by decide
  have hdescent : baseEnd_7386413 < baseStart_7386413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386416 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 4]
def baseStart_7386416 : Nat := 118140960795 + 7386416 * 2 ^ 59
def prefixEnd_7386416 : Nat := 4983230072969 + 3 ^ 40 * 7386416 * 2
def baseEnd_7386416 : Nat := 3792781722060477847130497

theorem tailTrace_7386416 : CollatzResearch.WordTrace tailWord_7386416 prefixEnd_7386416 3792781722060477847130497 := by
  unfold tailWord_7386416
  simp only [CollatzResearch.WordTrace]
  refine ⟨134702362004141903132405551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179603149338855870843207401 134702362004141903132405551)
  ·
    refine ⟨202053543006212854698608327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134702362004141903132405551 202053543006212854698608327)
    ·
      refine ⟨303080314509319282047912491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202053543006212854698608327 303080314509319282047912491)
      ·
        refine ⟨454620471763978923071868737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303080314509319282047912491 454620471763978923071868737)
        ·
          refine ⟨340965353822984192303901553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454620471763978923071868737 340965353822984192303901553)
          ·
            refine ⟨255724015367238144227926165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340965353822984192303901553 255724015367238144227926165)
            ·
              refine ⟨11987063220339288010684039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255724015367238144227926165 11987063220339288010684039)
              ·
                refine ⟨17980594830508932016026059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11987063220339288010684039 17980594830508932016026059)
                ·
                  refine ⟨26970892245763398024039089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17980594830508932016026059 26970892245763398024039089)
                  ·
                    refine ⟨20228169184322548518029317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26970892245763398024039089 20228169184322548518029317)
                    ·
                      refine ⟨3792781722060477847130497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20228169184322548518029317 3792781722060477847130497)
                      ·
                        rfl

theorem cell23_7386416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 4].length) (baseStart_7386416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386416 prefixEnd_7386416 := by exact prefixLift 7386416
  have htrace : WordTrace (prefixWord ++ tailWord_7386416) baseStart_7386416 baseEnd_7386416 := by
    simpa [prefixWord, tailWord_7386416, baseEnd_7386416] using wordTrace_append hprefix tailTrace_7386416
  have hstable : (prefixWord ++ tailWord_7386416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386416).length < 2 ^ (prefixWord ++ tailWord_7386416).sum := by decide
  have hdescent : baseEnd_7386416 < baseStart_7386416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386426 : List Nat := [3, 1, 1, 1, 4, 1, 5, 7]
def baseStart_7386426 : Nat := 118140960795 + 7386426 * 2 ^ 59
def prefixEnd_7386426 : Nat := 4983230072969 + 3 ^ 40 * 7386426 * 2
def baseEnd_7386426 : Nat := 140473587291371215111313

theorem tailTrace_7386426 : CollatzResearch.WordTrace tailWord_7386426 prefixEnd_7386426 140473587291371215111313 := by
  unfold tailWord_7386426
  simp only [CollatzResearch.WordTrace]
  refine ⟨67351272184561894493168783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179603392492165051981783421 67351272184561894493168783)
  ·
    refine ⟨101026908276842841739753175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67351272184561894493168783 101026908276842841739753175)
    ·
      refine ⟨151540362415264262609629763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101026908276842841739753175 151540362415264262609629763)
      ·
        refine ⟨227310543622896393914444645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151540362415264262609629763 227310543622896393914444645)
        ·
          refine ⟨42620726929293073858958371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227310543622896393914444645 42620726929293073858958371)
          ·
            refine ⟨63931090393939610788437557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42620726929293073858958371 63931090393939610788437557)
            ·
              refine ⟨5993539724431838511416021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63931090393939610788437557 5993539724431838511416021)
              ·
                refine ⟨140473587291371215111313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5993539724431838511416021 140473587291371215111313)
                ·
                  rfl

theorem cell23_7386426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 7].length) (baseStart_7386426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386426 prefixEnd_7386426 := by exact prefixLift 7386426
  have htrace : WordTrace (prefixWord ++ tailWord_7386426) baseStart_7386426 baseEnd_7386426 := by
    simpa [prefixWord, tailWord_7386426, baseEnd_7386426] using wordTrace_append hprefix tailTrace_7386426
  have hstable : (prefixWord ++ tailWord_7386426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386426).length < 2 ^ (prefixWord ++ tailWord_7386426).sum := by decide
  have hdescent : baseEnd_7386426 < baseStart_7386426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386433 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7386433 : Nat := 118140960795 + 7386433 * 2 ^ 59
def prefixEnd_7386433 : Nat := 4983230072969 + 3 ^ 40 * 7386433 * 2
def baseEnd_7386433 : Nat := 3792790451231604280617919

theorem tailTrace_7386433 : CollatzResearch.WordTrace tailWord_7386433 prefixEnd_7386433 3792790451231604280617919 := by
  unfold tailWord_7386433
  simp only [CollatzResearch.WordTrace]
  refine ⟨269405344049222218168179953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179603562699481478778786635 269405344049222218168179953)
  ·
    refine ⟨202054008036916663626134965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269405344049222218168179953 202054008036916663626134965)
    ·
      refine ⟨18942563253460937214950153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202054008036916663626134965 18942563253460937214950153)
      ·
        refine ⟨14206922440095702911212615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18942563253460937214950153 14206922440095702911212615)
        ·
          refine ⟨21310383660143554366818923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14206922440095702911212615 21310383660143554366818923)
          ·
            refine ⟨31965575490215331550228385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21310383660143554366818923 31965575490215331550228385)
            ·
              refine ⟨23974181617661498662671289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31965575490215331550228385 23974181617661498662671289)
              ·
                refine ⟨17980636213246123997003467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23974181617661498662671289 17980636213246123997003467)
                ·
                  refine ⟨26970954319869185995505201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17980636213246123997003467 26970954319869185995505201)
                  ·
                    refine ⟨20228215739901889496628901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26970954319869185995505201 20228215739901889496628901)
                    ·
                      refine ⟨3792790451231604280617919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20228215739901889496628901 3792790451231604280617919)
                      ·
                        rfl

theorem cell23_7386433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7386433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386433 prefixEnd_7386433 := by exact prefixLift 7386433
  have htrace : WordTrace (prefixWord ++ tailWord_7386433) baseStart_7386433 baseEnd_7386433 := by
    simpa [prefixWord, tailWord_7386433, baseEnd_7386433] using wordTrace_append hprefix tailTrace_7386433
  have hstable : (prefixWord ++ tailWord_7386433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386433).length < 2 ^ (prefixWord ++ tailWord_7386433).sum := by decide
  have hdescent : baseEnd_7386433 < baseStart_7386433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386480 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 1, 3, 2]
def baseStart_7386480 : Nat := 118140960795 + 7386480 * 2 ^ 59
def prefixEnd_7386480 : Nat := 4983230072969 + 3 ^ 40 * 7386480 * 2
def baseEnd_7386480 : Nat := 3792814584822365596730203

theorem tailTrace_7386480 : CollatzResearch.WordTrace tailWord_7386480 prefixEnd_7386480 3792814584822365596730203 := by
  unfold tailWord_7386480
  simp only [CollatzResearch.WordTrace]
  refine ⟨134703529140025972597570447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179604705520034630130093929 134703529140025972597570447)
  ·
    refine ⟨202055293710038958896355671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134703529140025972597570447 202055293710038958896355671)
    ·
      refine ⟨303082940565058438344533507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202055293710038958896355671 303082940565058438344533507)
      ·
        refine ⟨454624410847587657516800261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303082940565058438344533507 454624410847587657516800261)
        ·
          refine ⟨85242077033922685784400049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454624410847587657516800261 85242077033922685784400049)
          ·
            refine ⟨63931557775442014338300037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85242077033922685784400049 63931557775442014338300037)
            ·
              refine ⟨11987167082895377688431257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63931557775442014338300037 11987167082895377688431257)
              ·
                refine ⟨8990375312171533266323443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11987167082895377688431257 8990375312171533266323443)
                ·
                  refine ⟨13485562968257299899485165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8990375312171533266323443 13485562968257299899485165)
                  ·
                    refine ⟨5057086113096487462306937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13485562968257299899485165 5057086113096487462306937)
                    ·
                      refine ⟨3792814584822365596730203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057086113096487462306937 3792814584822365596730203)
                      ·
                        rfl

theorem cell23_7386480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 3, 2].length) (baseStart_7386480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386480 prefixEnd_7386480 := by exact prefixLift 7386480
  have htrace : WordTrace (prefixWord ++ tailWord_7386480) baseStart_7386480 baseEnd_7386480 := by
    simpa [prefixWord, tailWord_7386480, baseEnd_7386480] using wordTrace_append hprefix tailTrace_7386480
  have hstable : (prefixWord ++ tailWord_7386480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386480).length < 2 ^ (prefixWord ++ tailWord_7386480).sum := by decide
  have hdescent : baseEnd_7386480 < baseStart_7386480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
