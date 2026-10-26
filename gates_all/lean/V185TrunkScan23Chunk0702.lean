import V185TrunkScan23Chunk0701

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4150883 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 2, 2, 2]
def baseStart_4150883 : Nat := 118140960795 + 4150883 * 2 ^ 59
def prefixEnd_4150883 : Nat := 4983230072969 + 3 ^ 40 * 4150883 * 2
def baseEnd_4150883 : Nat := 2131398119576788384872943

theorem tailTrace_4150883 : CollatzResearch.WordTrace tailWord_4150883 prefixEnd_4150883 2131398119576788384872943 := by
  unfold tailWord_4150883
  simp only [CollatzResearch.WordTrace]
  refine ⟨151395140621067280221953303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100930093747378186814635535 151395140621067280221953303)
  ·
    refine ⟨227092710931600920332929955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151395140621067280221953303 227092710931600920332929955)
    ·
      refine ⟨340639066397401380499394933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227092710931600920332929955 340639066397401380499394933)
      ·
        refine ⟨31934912474756379421818275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340639066397401380499394933 31934912474756379421818275)
        ·
          refine ⟨47902368712134569132727413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31934912474756379421818275 47902368712134569132727413)
          ·
            refine ⟨4490847066762615856193195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47902368712134569132727413 4490847066762615856193195)
            ·
              refine ⟨6736270600143923784289793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490847066762615856193195 6736270600143923784289793)
              ·
                refine ⟨5052202950107942838217345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6736270600143923784289793 5052202950107942838217345)
                ·
                  refine ⟨3789152212580957128663009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5052202950107942838217345 3789152212580957128663009)
                  ·
                    refine ⟨2841864159435717846497257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3789152212580957128663009 2841864159435717846497257)
                    ·
                      refine ⟨2131398119576788384872943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841864159435717846497257 2131398119576788384872943)
                      ·
                        rfl

theorem cell23_4150883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_4150883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150883 prefixEnd_4150883 := by exact prefixLift 4150883
  have htrace : WordTrace (prefixWord ++ tailWord_4150883) baseStart_4150883 baseEnd_4150883 := by
    simpa [prefixWord, tailWord_4150883, baseEnd_4150883] using wordTrace_append hprefix tailTrace_4150883
  have hstable : (prefixWord ++ tailWord_4150883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150883).length < 2 ^ (prefixWord ++ tailWord_4150883).sum := by decide
  have hdescent : baseEnd_4150883 < baseStart_4150883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150895 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_4150895 : Nat := 118140960795 + 4150895 * 2 ^ 59
def prefixEnd_4150895 : Nat := 4983230072969 + 3 ^ 40 * 4150895 * 2
def baseEnd_4150895 : Nat := 2131404281344642337922887

theorem tailTrace_4150895 : CollatzResearch.WordTrace tailWord_4150895 prefixEnd_4150895 2131404281344642337922887 := by
  unfold tailWord_4150895
  simp only [CollatzResearch.WordTrace]
  refine ⟨151395578297023806271390139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100930385531349204180926759 151395578297023806271390139)
  ·
    refine ⟨227093367445535709407085209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151395578297023806271390139 227093367445535709407085209)
    ·
      refine ⟨170320025584151782055313907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227093367445535709407085209 170320025584151782055313907)
      ·
        refine ⟨255480038376227673082970861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170320025584151782055313907 255480038376227673082970861)
        ·
          refine ⟨95805014391085377406114073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255480038376227673082970861 95805014391085377406114073)
          ·
            refine ⟨71853760793314033054585555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95805014391085377406114073 71853760793314033054585555)
            ·
              refine ⟨107780641189971049581878333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71853760793314033054585555 107780641189971049581878333)
              ·
                refine ⟨40417740446239143593204375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107780641189971049581878333 40417740446239143593204375)
                ·
                  refine ⟨60626610669358715389806563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40417740446239143593204375 60626610669358715389806563)
                  ·
                    refine ⟨90939916004038073084709845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60626610669358715389806563 90939916004038073084709845)
                    ·
                      refine ⟨2131404281344642337922887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90939916004038073084709845 2131404281344642337922887)
                      ·
                        rfl

theorem cell23_4150895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_4150895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150895 prefixEnd_4150895 := by exact prefixLift 4150895
  have htrace : WordTrace (prefixWord ++ tailWord_4150895) baseStart_4150895 baseEnd_4150895 := by
    simpa [prefixWord, tailWord_4150895, baseEnd_4150895] using wordTrace_append hprefix tailTrace_4150895
  have hstable : (prefixWord ++ tailWord_4150895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150895).length < 2 ^ (prefixWord ++ tailWord_4150895).sum := by decide
  have hdescent : baseEnd_4150895 < baseStart_4150895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150915 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 1, 10]
def baseStart_4150915 : Nat := 118140960795 + 4150915 * 2 ^ 59
def prefixEnd_4150915 : Nat := 4983230072969 + 3 ^ 40 * 4150915 * 2
def baseEnd_4150915 : Nat := 710471516985910753224265

theorem tailTrace_4150915 : CollatzResearch.WordTrace tailWord_4150915 prefixEnd_4150915 710471516985910753224265 := by
  unfold tailWord_4150915
  simp only [CollatzResearch.WordTrace]
  refine ⟨151396307756951349687118199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100930871837967566458078799 151396307756951349687118199)
  ·
    refine ⟨227094461635427024530677299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151396307756951349687118199 227094461635427024530677299)
    ·
      refine ⟨340641692453140536796015949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227094461635427024530677299 340641692453140536796015949)
      ·
        refine ⟨127740634669927701298505981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340641692453140536796015949 127740634669927701298505981)
        ·
          refine ⟨47902738001222887986939743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127740634669927701298505981 47902738001222887986939743)
          ·
            refine ⟨71854107001834331980409615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47902738001222887986939743 71854107001834331980409615)
            ·
              refine ⟨107781160502751497970614423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71854107001834331980409615 107781160502751497970614423)
              ·
                refine ⟨161671740754127246955921635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107781160502751497970614423 161671740754127246955921635)
                ·
                  refine ⟨242507611131190870433882453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161671740754127246955921635 242507611131190870433882453)
                  ·
                    refine ⟨710471516985910753224265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 242507611131190870433882453 710471516985910753224265)
                    ·
                      rfl

theorem cell23_4150915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 10].length) (baseStart_4150915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150915 prefixEnd_4150915 := by exact prefixLift 4150915
  have htrace : WordTrace (prefixWord ++ tailWord_4150915) baseStart_4150915 baseEnd_4150915 := by
    simpa [prefixWord, tailWord_4150915, baseEnd_4150915] using wordTrace_append hprefix tailTrace_4150915
  have hstable : (prefixWord ++ tailWord_4150915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150915).length < 2 ^ (prefixWord ++ tailWord_4150915).sum := by decide
  have hdescent : baseEnd_4150915 < baseStart_4150915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150946 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_4150946 : Nat := 118140960795 + 4150946 * 2 ^ 59
def prefixEnd_4150946 : Nat := 4983230072969 + 3 ^ 40 * 4150946 * 2
def baseEnd_4150946 : Nat := 2131430468858021638385153

theorem tailTrace_4150946 : CollatzResearch.WordTrace tailWord_4150946 prefixEnd_4150946 2131430468858021638385153 := by
  unfold tailWord_4150946
  simp only [CollatzResearch.WordTrace]
  refine ⟨37849359604959760495374173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100931625613226027987664461 37849359604959760495374173)
  ·
    refine ⟨14193509851859910185765315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37849359604959760495374173 14193509851859910185765315)
    ·
      refine ⟨21290264777789865278647973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14193509851859910185765315 21290264777789865278647973)
      ·
        refine ⟨3991924645835599739746495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21290264777789865278647973 3991924645835599739746495)
        ·
          refine ⟨5987886968753399609619743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991924645835599739746495 5987886968753399609619743)
          ·
            refine ⟨8981830453130099414429615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987886968753399609619743 8981830453130099414429615)
            ·
              refine ⟨13472745679695149121644423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8981830453130099414429615 13472745679695149121644423)
              ·
                refine ⟨20209118519542723682466635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13472745679695149121644423 20209118519542723682466635)
                ·
                  refine ⟨30313677779314085523699953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20209118519542723682466635 30313677779314085523699953)
                  ·
                    refine ⟨22735258334485564142774965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30313677779314085523699953 22735258334485564142774965)
                    ·
                      refine ⟨2131430468858021638385153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22735258334485564142774965 2131430468858021638385153)
                      ·
                        rfl

theorem cell23_4150946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_4150946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150946 prefixEnd_4150946 := by exact prefixLift 4150946
  have htrace : WordTrace (prefixWord ++ tailWord_4150946) baseStart_4150946 baseEnd_4150946 := by
    simpa [prefixWord, tailWord_4150946, baseEnd_4150946] using wordTrace_append hprefix tailTrace_4150946
  have hstable : (prefixWord ++ tailWord_4150946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150946).length < 2 ^ (prefixWord ++ tailWord_4150946).sum := by decide
  have hdescent : baseEnd_4150946 < baseStart_4150946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150949 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_4150949 : Nat := 118140960795 + 4150949 * 2 ^ 59
def prefixEnd_4150949 : Nat := 4983230072969 + 3 ^ 40 * 4150949 * 2
def baseEnd_4150949 : Nat := 710477336433328375549213

theorem tailTrace_4150949 : CollatzResearch.WordTrace tailWord_4150949 prefixEnd_4150949 710477336433328375549213 := by
  unfold tailWord_4150949
  simp only [CollatzResearch.WordTrace]
  refine ⟨151397547838828173493855901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100931698559218782329237267 151397547838828173493855901)
  ·
    refine ⟨56774080439560565060195963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151397547838828173493855901 56774080439560565060195963)
    ·
      refine ⟨85161120659340847590293945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56774080439560565060195963 85161120659340847590293945)
      ·
        refine ⟨63870840494505635692720459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85161120659340847590293945 63870840494505635692720459)
        ·
          refine ⟨95806260741758453539080689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63870840494505635692720459 95806260741758453539080689)
          ·
            refine ⟨71854695556318840154310517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95806260741758453539080689 71854695556318840154310517)
            ·
              refine ⟨6736377708404891264466611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71854695556318840154310517 6736377708404891264466611)
              ·
                refine ⟨10104566562607336896699917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736377708404891264466611 10104566562607336896699917)
                ·
                  refine ⟨3789212460977751336262469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10104566562607336896699917 3789212460977751336262469)
                  ·
                    refine ⟨710477336433328375549213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3789212460977751336262469 710477336433328375549213)
                    ·
                      rfl

theorem cell23_4150949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_4150949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150949 prefixEnd_4150949 := by exact prefixLift 4150949
  have htrace : WordTrace (prefixWord ++ tailWord_4150949) baseStart_4150949 baseEnd_4150949 := by
    simpa [prefixWord, tailWord_4150949, baseEnd_4150949] using wordTrace_append hprefix tailTrace_4150949
  have hstable : (prefixWord ++ tailWord_4150949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150949).length < 2 ^ (prefixWord ++ tailWord_4150949).sum := by decide
  have hdescent : baseEnd_4150949 < baseStart_4150949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150996 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 6]
def baseStart_4150996 : Nat := 118140960795 + 4150996 * 2 ^ 59
def prefixEnd_4150996 : Nat := 4983230072969 + 3 ^ 40 * 4150996 * 2
def baseEnd_4150996 : Nat := 236828460321194049195547

theorem tailTrace_4150996 : CollatzResearch.WordTrace tailWord_4150996 prefixEnd_4150996 236828460321194049195547 := by
  unfold tailWord_4150996
  simp only [CollatzResearch.WordTrace]
  refine ⟨75699631034828950260408421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100932841379771933680544561 75699631034828950260408421)
  ·
    refine ⟨14193680819030428173826579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75699631034828950260408421 14193680819030428173826579)
    ·
      refine ⟨21290521228545642260739869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14193680819030428173826579 21290521228545642260739869)
      ·
        refine ⟨7983945460704615847777451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21290521228545642260739869 7983945460704615847777451)
        ·
          refine ⟨11975918191056923771666177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7983945460704615847777451 11975918191056923771666177)
          ·
            refine ⟨8981938643292692828749633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11975918191056923771666177 8981938643292692828749633)
            ·
              refine ⟨6736453982469519621562225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8981938643292692828749633 6736453982469519621562225)
              ·
                refine ⟨5052340486852139716171669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6736453982469519621562225 5052340486852139716171669)
                ·
                  refine ⟨236828460321194049195547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5052340486852139716171669 236828460321194049195547)
                  ·
                    rfl

theorem cell23_4150996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_4150996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150996 prefixEnd_4150996 := by exact prefixLift 4150996
  have htrace : WordTrace (prefixWord ++ tailWord_4150996) baseStart_4150996 baseEnd_4150996 := by
    simpa [prefixWord, tailWord_4150996, baseEnd_4150996] using wordTrace_append hprefix tailTrace_4150996
  have hstable : (prefixWord ++ tailWord_4150996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150996).length < 2 ^ (prefixWord ++ tailWord_4150996).sum := by decide
  have hdescent : baseEnd_4150996 < baseStart_4150996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151032 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_4151032 : Nat := 118140960795 + 4151032 * 2 ^ 59
def prefixEnd_4151032 : Nat := 4983230072969 + 3 ^ 40 * 4151032 * 2
def baseEnd_4151032 : Nat := 2131474628194308301909757

theorem tailTrace_4151032 : CollatzResearch.WordTrace tailWord_4151032 prefixEnd_4151032 2131474628194308301909757 := by
  unfold tailWord_4151032
  simp only [CollatzResearch.WordTrace]
  refine ⟨75700287548763739334563675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100933716731684985779418233 75700287548763739334563675)
  ·
    refine ⟨113550431323145609001845513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75700287548763739334563675 113550431323145609001845513)
    ·
      refine ⟨85162823492359206751384135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113550431323145609001845513 85162823492359206751384135)
      ·
        refine ⟨127744235238538810127076203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85162823492359206751384135 127744235238538810127076203)
        ·
          refine ⟨191616352857808215190614305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127744235238538810127076203 191616352857808215190614305)
          ·
            refine ⟨143712264643356161392960729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191616352857808215190614305 143712264643356161392960729)
            ·
              refine ⟨107784198482517121044720547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143712264643356161392960729 107784198482517121044720547)
              ·
                refine ⟨161676297723775681567080821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107784198482517121044720547 161676297723775681567080821)
                ·
                  refine ⟨15157152911603970146913827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161676297723775681567080821 15157152911603970146913827)
                  ·
                    refine ⟨22735729367405955220370741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15157152911603970146913827 22735729367405955220370741)
                    ·
                      refine ⟨2131474628194308301909757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22735729367405955220370741 2131474628194308301909757)
                      ·
                        rfl

theorem cell23_4151032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_4151032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151032 prefixEnd_4151032 := by exact prefixLift 4151032
  have htrace : WordTrace (prefixWord ++ tailWord_4151032) baseStart_4151032 baseEnd_4151032 := by
    simpa [prefixWord, tailWord_4151032, baseEnd_4151032] using wordTrace_append hprefix tailTrace_4151032
  have hstable : (prefixWord ++ tailWord_4151032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151032).length < 2 ^ (prefixWord ++ tailWord_4151032).sum := by decide
  have hdescent : baseEnd_4151032 < baseStart_4151032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151063 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 3, 2, 2]
def baseStart_4151063 : Nat := 118140960795 + 4151063 * 2 ^ 59
def prefixEnd_4151063 : Nat := 4983230072969 + 3 ^ 40 * 4151063 * 2
def baseEnd_4151063 : Nat := 2131490546094597680622115

theorem tailTrace_4151063 : CollatzResearch.WordTrace tailWord_4151063 prefixEnd_4151063 2131490546094597680622115 := by
  unfold tailWord_4151063
  simp only [CollatzResearch.WordTrace]
  refine ⟨151401705760415170963505843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100934470506943447309003895 151401705760415170963505843)
  ·
    refine ⟨227102558640622756445258765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151401705760415170963505843 227102558640622756445258765)
    ·
      refine ⟨85163459490233533666972037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227102558640622756445258765 85163459490233533666972037)
      ·
        refine ⟨15968148654418787562557257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85163459490233533666972037 15968148654418787562557257)
        ·
          refine ⟨11976111490814090671917943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15968148654418787562557257 11976111490814090671917943)
          ·
            refine ⟨17964167236221136007876915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11976111490814090671917943 17964167236221136007876915)
            ·
              refine ⟨26946250854331704011815373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17964167236221136007876915 26946250854331704011815373)
              ·
                refine ⟨10104844070374389004430765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26946250854331704011815373 10104844070374389004430765)
                ·
                  refine ⟨3789316526390395876661537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10104844070374389004430765 3789316526390395876661537)
                  ·
                    refine ⟨2841987394792796907496153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3789316526390395876661537 2841987394792796907496153)
                    ·
                      refine ⟨2131490546094597680622115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841987394792796907496153 2131490546094597680622115)
                      ·
                        rfl

theorem cell23_4151063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_4151063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151063 prefixEnd_4151063 := by exact prefixLift 4151063
  have htrace : WordTrace (prefixWord ++ tailWord_4151063) baseStart_4151063 baseEnd_4151063 := by
    simpa [prefixWord, tailWord_4151063, baseEnd_4151063] using wordTrace_append hprefix tailTrace_4151063
  have hstable : (prefixWord ++ tailWord_4151063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151063).length < 2 ^ (prefixWord ++ tailWord_4151063).sum := by decide
  have hdescent : baseEnd_4151063 < baseStart_4151063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151073 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 2, 4]
def baseStart_4151073 : Nat := 118140960795 + 4151073 * 2 ^ 59
def prefixEnd_4151073 : Nat := 4983230072969 + 3 ^ 40 * 4151073 * 2
def baseEnd_4151073 : Nat := 710498560300380880499023

theorem tailTrace_4151073 : CollatzResearch.WordTrace tailWord_4151073 prefixEnd_4151073 710498560300380880499023 := by
  unfold tailWord_4151073
  simp only [CollatzResearch.WordTrace]
  refine ⟨151402070490378942671369873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100934713660252628447579915 151402070490378942671369873)
  ·
    refine ⟨113551552867784207003527405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151402070490378942671369873 113551552867784207003527405)
    ·
      refine ⟨42581832325419077626322777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113551552867784207003527405 42581832325419077626322777)
      ·
        refine ⟨31936374244064308219742083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42581832325419077626322777 31936374244064308219742083)
        ·
          refine ⟨47904561366096462329613125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31936374244064308219742083 47904561366096462329613125)
          ·
            refine ⟨8982105256143086686802461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47904561366096462329613125 8982105256143086686802461)
            ·
              refine ⟨3368289471053657507550923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8982105256143086686802461 3368289471053657507550923)
              ·
                refine ⟨5052434206580486261326385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368289471053657507550923 5052434206580486261326385)
                ·
                  refine ⟨3789325654935364695994789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5052434206580486261326385 3789325654935364695994789)
                  ·
                    refine ⟨710498560300380880499023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3789325654935364695994789 710498560300380880499023)
                    ·
                      rfl

theorem cell23_4151073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_4151073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151073 prefixEnd_4151073 := by exact prefixLift 4151073
  have htrace : WordTrace (prefixWord ++ tailWord_4151073) baseStart_4151073 baseEnd_4151073 := by
    simpa [prefixWord, tailWord_4151073, baseEnd_4151073] using wordTrace_append hprefix tailTrace_4151073
  have hstable : (prefixWord ++ tailWord_4151073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151073).length < 2 ^ (prefixWord ++ tailWord_4151073).sum := by decide
  have hdescent : baseEnd_4151073 < baseStart_4151073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151076 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_4151076 : Nat := 118140960795 + 4151076 * 2 ^ 59
def prefixEnd_4151076 : Nat := 4983230072969 + 3 ^ 40 * 4151076 * 2
def baseEnd_4151076 : Nat := 2131497221343106129759555

theorem tailTrace_4151076 : CollatzResearch.WordTrace tailWord_4151076 prefixEnd_4151076 2131497221343106129759555 := by
  unfold tailWord_4151076
  simp only [CollatzResearch.WordTrace]
  refine ⟨75701089954684037091864541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100934786606245382789152721 75701089954684037091864541)
  ·
    refine ⟨28387908733006513909449203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75701089954684037091864541 28387908733006513909449203)
    ·
      refine ⟨42581863099509770864173805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28387908733006513909449203 42581863099509770864173805)
      ·
        refine ⟨15968198662316164074065177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42581863099509770864173805 15968198662316164074065177)
        ·
          refine ⟨11976148996737123055548883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15968198662316164074065177 11976148996737123055548883)
          ·
            refine ⟨17964223495105684583323325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11976148996737123055548883 17964223495105684583323325)
            ·
              refine ⟨6736583810664631718746247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17964223495105684583323325 6736583810664631718746247)
              ·
                refine ⟨10104875715996947578119371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736583810664631718746247 10104875715996947578119371)
                ·
                  refine ⟨15157313573995421367179057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104875715996947578119371 15157313573995421367179057)
                  ·
                    refine ⟨11367985180496566025384293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15157313573995421367179057 11367985180496566025384293)
                    ·
                      refine ⟨2131497221343106129759555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11367985180496566025384293 2131497221343106129759555)
                      ·
                        rfl

theorem cell23_4151076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_4151076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151076 prefixEnd_4151076 := by exact prefixLift 4151076
  have htrace : WordTrace (prefixWord ++ tailWord_4151076) baseStart_4151076 baseEnd_4151076 := by
    simpa [prefixWord, tailWord_4151076, baseEnd_4151076] using wordTrace_append hprefix tailTrace_4151076
  have hstable : (prefixWord ++ tailWord_4151076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151076).length < 2 ^ (prefixWord ++ tailWord_4151076).sum := by decide
  have hdescent : baseEnd_4151076 < baseStart_4151076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151086 : List Nat := [4, 1, 3, 2, 2, 1, 1, 9]
def baseStart_4151086 : Nat := 118140960795 + 4151086 * 2 ^ 59
def prefixEnd_4151086 : Nat := 4983230072969 + 3 ^ 40 * 4151086 * 2
def baseEnd_4151086 : Nat := 78944531709246336690167

theorem tailTrace_4151086 : CollatzResearch.WordTrace tailWord_4151086 prefixEnd_4151086 78944531709246336690167 := by
  unfold tailWord_4151086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18925318079916480736449139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100935029759554563927728741 18925318079916480736449139)
  ·
    refine ⟨28387977119874721104673709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18925318079916480736449139 28387977119874721104673709)
    ·
      refine ⟨10645491419953020414252641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28387977119874721104673709 10645491419953020414252641)
      ·
        refine ⟨7984118564964765310689481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10645491419953020414252641 7984118564964765310689481)
        ·
          refine ⟨5988088923723573983017111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7984118564964765310689481 5988088923723573983017111)
          ·
            refine ⟨8982133385585360974525667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988088923723573983017111 8982133385585360974525667)
            ·
              refine ⟨13473200078378041461788501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8982133385585360974525667 13473200078378041461788501)
              ·
                refine ⟨78944531709246336690167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13473200078378041461788501 78944531709246336690167)
                ·
                  rfl

theorem cell23_4151086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_4151086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151086 prefixEnd_4151086 := by exact prefixLift 4151086
  have htrace : WordTrace (prefixWord ++ tailWord_4151086) baseStart_4151086 baseEnd_4151086 := by
    simpa [prefixWord, tailWord_4151086, baseEnd_4151086] using wordTrace_append hprefix tailTrace_4151086
  have hstable : (prefixWord ++ tailWord_4151086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151086).length < 2 ^ (prefixWord ++ tailWord_4151086).sum := by decide
  have hdescent : baseEnd_4151086 < baseStart_4151086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151096 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 4, 1, 3]
def baseStart_4151096 : Nat := 118140960795 + 4151096 * 2 ^ 59
def prefixEnd_4151096 : Nat := 4983230072969 + 3 ^ 40 * 4151096 * 2
def baseEnd_4151096 : Nat := 2131507490956196051509463

theorem tailTrace_4151096 : CollatzResearch.WordTrace tailWord_4151096 prefixEnd_4151096 2131507490956196051509463 := by
  unfold tailWord_4151096
  simp only [CollatzResearch.WordTrace]
  refine ⟨75701454684647808799728571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100935272912863745066304761 75701454684647808799728571)
  ·
    refine ⟨113552182026971713199592857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75701454684647808799728571 113552182026971713199592857)
    ·
      refine ⟨85164136520228784899694643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113552182026971713199592857 85164136520228784899694643)
      ·
        refine ⟨127746204780343177349541965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85164136520228784899694643 127746204780343177349541965)
        ·
          refine ⟨47904826792628691506078237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127746204780343177349541965 47904826792628691506078237)
          ·
            refine ⟨17964310047235759314779339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47904826792628691506078237 17964310047235759314779339)
            ·
              refine ⟨26946465070853638972169009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17964310047235759314779339 26946465070853638972169009)
              ·
                refine ⟨20209848803140229229126757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26946465070853638972169009 20209848803140229229126757)
                ·
                  refine ⟨3789346650588792980461267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20209848803140229229126757 3789346650588792980461267)
                  ·
                    refine ⟨5684019975883189470691901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3789346650588792980461267 5684019975883189470691901)
                    ·
                      refine ⟨2131507490956196051509463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5684019975883189470691901 2131507490956196051509463)
                      ·
                        rfl

theorem cell23_4151096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_4151096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151096 prefixEnd_4151096 := by exact prefixLift 4151096
  have htrace : WordTrace (prefixWord ++ tailWord_4151096) baseStart_4151096 baseEnd_4151096 := by
    simpa [prefixWord, tailWord_4151096, baseEnd_4151096] using wordTrace_append hprefix tailTrace_4151096
  have hstable : (prefixWord ++ tailWord_4151096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151096).length < 2 ^ (prefixWord ++ tailWord_4151096).sum := by decide
  have hdescent : baseEnd_4151096 < baseStart_4151096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151189 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_4151189 : Nat := 118140960795 + 4151189 * 2 ^ 59
def prefixEnd_4151189 : Nat := 4983230072969 + 3 ^ 40 * 4151189 * 2
def baseEnd_4151189 : Nat := 710518414885688062548845

theorem tailTrace_4151189 : CollatzResearch.WordTrace tailWord_4151189 prefixEnd_4151189 710518414885688062548845 := by
  unfold tailWord_4151189
  simp only [CollatzResearch.WordTrace]
  refine ⟨151406301357958694482592621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100937534238639129655061747 151406301357958694482592621)
  ·
    refine ⟨56777363009234510430972233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151406301357958694482592621 56777363009234510430972233)
    ·
      refine ⟨42583022256925882823229175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56777363009234510430972233 42583022256925882823229175)
      ·
        refine ⟨63874533385388824234843763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42583022256925882823229175 63874533385388824234843763)
        ·
          refine ⟨95811800078083236352265645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63874533385388824234843763 95811800078083236352265645)
          ·
            refine ⟨35929425029281213632099617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95811800078083236352265645 35929425029281213632099617)
            ·
              refine ⟨26947068771960910224074713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35929425029281213632099617 26947068771960910224074713)
              ·
                refine ⟨20210301578970682668056035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26947068771960910224074713 20210301578970682668056035)
                ·
                  refine ⟨30315452368456024002084053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20210301578970682668056035 30315452368456024002084053)
                  ·
                    refine ⟨710518414885688062548845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30315452368456024002084053 710518414885688062548845)
                    ·
                      rfl

theorem cell23_4151189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_4151189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151189 prefixEnd_4151189 := by exact prefixLift 4151189
  have htrace : WordTrace (prefixWord ++ tailWord_4151189) baseStart_4151189 baseEnd_4151189 := by
    simpa [prefixWord, tailWord_4151189, baseEnd_4151189] using wordTrace_append hprefix tailTrace_4151189
  have hstable : (prefixWord ++ tailWord_4151189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151189).length < 2 ^ (prefixWord ++ tailWord_4151189).sum := by decide
  have hdescent : baseEnd_4151189 < baseStart_4151189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151239 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_4151239 : Nat := 118140960795 + 4151239 * 2 ^ 59
def prefixEnd_4151239 : Nat := 4983230072969 + 3 ^ 40 * 4151239 * 2
def baseEnd_4151239 : Nat := 2131580918689788992021305

theorem tailTrace_4151239 : CollatzResearch.WordTrace tailWord_4151239 prefixEnd_4151239 2131580918689788992021305 := by
  unfold tailWord_4151239
  simp only [CollatzResearch.WordTrace]
  refine ⟨151408125007777553021912771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100938750005185035347941847 151408125007777553021912771)
  ·
    refine ⟨227112187511666329532869157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151408125007777553021912771 227112187511666329532869157)
    ·
      refine ⟨42583535158437436787412967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227112187511666329532869157 42583535158437436787412967)
      ·
        refine ⟨63875302737656155181119451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42583535158437436787412967 63875302737656155181119451)
        ·
          refine ⟨95812954106484232771679177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63875302737656155181119451 95812954106484232771679177)
          ·
            refine ⟨71859715579863174578759383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95812954106484232771679177 71859715579863174578759383)
            ·
              refine ⟨107789573369794761868139075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71859715579863174578759383 107789573369794761868139075)
              ·
                refine ⟨161684360054692142802208613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107789573369794761868139075 161684360054692142802208613)
                ·
                  refine ⟨30315817510254776775414115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161684360054692142802208613 30315817510254776775414115)
                  ·
                    refine ⟨45473726265382165163121173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30315817510254776775414115 45473726265382165163121173)
                    ·
                      refine ⟨2131580918689788992021305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45473726265382165163121173 2131580918689788992021305)
                      ·
                        rfl

theorem cell23_4151239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_4151239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151239 prefixEnd_4151239 := by exact prefixLift 4151239
  have htrace : WordTrace (prefixWord ++ tailWord_4151239) baseStart_4151239 baseEnd_4151239 := by
    simpa [prefixWord, tailWord_4151239, baseEnd_4151239] using wordTrace_append hprefix tailTrace_4151239
  have hstable : (prefixWord ++ tailWord_4151239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151239).length < 2 ^ (prefixWord ++ tailWord_4151239).sum := by decide
  have hdescent : baseEnd_4151239 < baseStart_4151239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151246 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_4151246 : Nat := 118140960795 + 4151246 * 2 ^ 59
def prefixEnd_4151246 : Nat := 4983230072969 + 3 ^ 40 * 4151246 * 2
def baseEnd_4151246 : Nat := 2131584513054370464633773

theorem tailTrace_4151246 : CollatzResearch.WordTrace tailWord_4151246 prefixEnd_4151246 2131584513054370464633773 := by
  unfold tailWord_4151246
  simp only [CollatzResearch.WordTrace]
  refine ⟨18926047539844024152177199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100938920212501462144945061 18926047539844024152177199)
  ·
    refine ⟨28389071309766036228265799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18926047539844024152177199 28389071309766036228265799)
    ·
      refine ⟨42583606964649054342398699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28389071309766036228265799 42583606964649054342398699)
      ·
        refine ⟨63875410446973581513598049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42583606964649054342398699 63875410446973581513598049)
        ·
          refine ⟨47906557835230186135198537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63875410446973581513598049 47906557835230186135198537)
          ·
            refine ⟨35929918376422639601398903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47906557835230186135198537 35929918376422639601398903)
            ·
              refine ⟨53894877564633959402098355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35929918376422639601398903 53894877564633959402098355)
              ·
                refine ⟨80842316346950939103147533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53894877564633959402098355 80842316346950939103147533)
                ·
                  refine ⟨30315868630106602163680325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80842316346950939103147533 30315868630106602163680325)
                  ·
                    refine ⟨5684225368144987905690061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30315868630106602163680325 5684225368144987905690061)
                    ·
                      refine ⟨2131584513054370464633773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5684225368144987905690061 2131584513054370464633773)
                      ·
                        rfl

theorem cell23_4151246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_4151246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151246 prefixEnd_4151246 := by exact prefixLift 4151246
  have htrace : WordTrace (prefixWord ++ tailWord_4151246) baseStart_4151246 baseEnd_4151246 := by
    simpa [prefixWord, tailWord_4151246, baseEnd_4151246] using wordTrace_append hprefix tailTrace_4151246
  have hstable : (prefixWord ++ tailWord_4151246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151246).length < 2 ^ (prefixWord ++ tailWord_4151246).sum := by decide
  have hdescent : baseEnd_4151246 < baseStart_4151246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151253 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_4151253 : Nat := 118140960795 + 4151253 * 2 ^ 59
def prefixEnd_4151253 : Nat := 4983230072969 + 3 ^ 40 * 4151253 * 2
def baseEnd_4151253 : Nat := 710529369139650645748747

theorem tailTrace_4151253 : CollatzResearch.WordTrace tailWord_4151253 prefixEnd_4151253 710529369139650645748747 := by
  unfold tailWord_4151253
  simp only [CollatzResearch.WordTrace]
  refine ⟨151408635629726833412922413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100939090419817888941948275 151408635629726833412922413)
  ·
    refine ⟨56778238361147562529845905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151408635629726833412922413 56778238361147562529845905)
    ·
      refine ⟨42583678770860671897384429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56778238361147562529845905 42583678770860671897384429)
      ·
        refine ⟨15968879539072751961519161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42583678770860671897384429 15968879539072751961519161)
        ·
          refine ⟨11976659654304563971139371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15968879539072751961519161 11976659654304563971139371)
          ·
            refine ⟨17964989481456845956709057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11976659654304563971139371 17964989481456845956709057)
            ·
              refine ⟨13473742111092634467531793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17964989481456845956709057 13473742111092634467531793)
              ·
                refine ⟨10105306583319475850648845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13473742111092634467531793 10105306583319475850648845)
                ·
                  refine ⟨3789489968744803443993317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10105306583319475850648845 3789489968744803443993317)
                  ·
                    refine ⟨710529369139650645748747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3789489968744803443993317 710529369139650645748747)
                    ·
                      rfl

theorem cell23_4151253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_4151253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151253 prefixEnd_4151253 := by exact prefixLift 4151253
  have htrace : WordTrace (prefixWord ++ tailWord_4151253) baseStart_4151253 baseEnd_4151253 := by
    simpa [prefixWord, tailWord_4151253, baseEnd_4151253] using wordTrace_append hprefix tailTrace_4151253
  have hstable : (prefixWord ++ tailWord_4151253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151253).length < 2 ^ (prefixWord ++ tailWord_4151253).sum := by decide
  have hdescent : baseEnd_4151253 < baseStart_4151253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151300 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 6]
def baseStart_4151300 : Nat := 118140960795 + 4151300 * 2 ^ 59
def prefixEnd_4151300 : Nat := 4983230072969 + 3 ^ 40 * 4151300 * 2
def baseEnd_4151300 : Nat := 236845804556634805928725

theorem tailTrace_4151300 : CollatzResearch.WordTrace tailWord_4151300 prefixEnd_4151300 236845804556634805928725 := by
  unfold tailWord_4151300
  simp only [CollatzResearch.WordTrace]
  refine ⟨75705174930278280219941677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100940233240371040293255569 75705174930278280219941677)
  ·
    refine ⟨28389440598854355082478129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75705174930278280219941677 28389440598854355082478129)
    ·
      refine ⟨21292080449140766311858597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28389440598854355082478129 21292080449140766311858597)
      ·
        refine ⟨3992265084213893683473487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21292080449140766311858597 3992265084213893683473487)
        ·
          refine ⟨5988397626320840525210231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992265084213893683473487 5988397626320840525210231)
          ·
            refine ⟨8982596439481260787815347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988397626320840525210231 8982596439481260787815347)
            ·
              refine ⟨13473894659221891181723021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8982596439481260787815347 13473894659221891181723021)
              ·
                refine ⟨5052710497208209193146133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13473894659221891181723021 5052710497208209193146133)
                ·
                  refine ⟨236845804556634805928725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5052710497208209193146133 236845804556634805928725)
                  ·
                    rfl

theorem cell23_4151300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_4151300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151300 prefixEnd_4151300 := by exact prefixLift 4151300
  have htrace : WordTrace (prefixWord ++ tailWord_4151300) baseStart_4151300 baseEnd_4151300 := by
    simpa [prefixWord, tailWord_4151300, baseEnd_4151300] using wordTrace_append hprefix tailTrace_4151300
  have hstable : (prefixWord ++ tailWord_4151300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151300).length < 2 ^ (prefixWord ++ tailWord_4151300).sum := by decide
  have hdescent : baseEnd_4151300 < baseStart_4151300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151320 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 2, 3, 2]
def baseStart_4151320 : Nat := 118140960795 + 4151320 * 2 ^ 59
def prefixEnd_4151320 : Nat := 4983230072969 + 3 ^ 40 * 4151320 * 2
def baseEnd_4151320 : Nat := 2131622510622803175108433

theorem tailTrace_4151320 : CollatzResearch.WordTrace tailWord_4151320 prefixEnd_4151320 2131622510622803175108433 := by
  unfold tailWord_4151320
  simp only [CollatzResearch.WordTrace]
  refine ⟨75705539660242051927805707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100940719546989402570407609 75705539660242051927805707)
  ·
    refine ⟨113558309490363077891708561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75705539660242051927805707 113558309490363077891708561)
    ·
      refine ⟨85168732117772308418781421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113558309490363077891708561 85168732117772308418781421)
      ·
        refine ⟨31938274544164615657043033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85168732117772308418781421 31938274544164615657043033)
        ·
          refine ⟨23953705908123461742782275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31938274544164615657043033 23953705908123461742782275)
          ·
            refine ⟨35930558862185192614173413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23953705908123461742782275 35930558862185192614173413)
            ·
              refine ⟨6736979786659723615157515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35930558862185192614173413 6736979786659723615157515)
              ·
                refine ⟨10105469679989585422736273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736979786659723615157515 10105469679989585422736273)
                ·
                  refine ⟨7579102259992189067052205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10105469679989585422736273 7579102259992189067052205)
                  ·
                    refine ⟨2842163347497070900144577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7579102259992189067052205 2842163347497070900144577)
                    ·
                      refine ⟨2131622510622803175108433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842163347497070900144577 2131622510622803175108433)
                      ·
                        rfl

theorem cell23_4151320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_4151320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151320 prefixEnd_4151320 := by exact prefixLift 4151320
  have htrace : WordTrace (prefixWord ++ tailWord_4151320) baseStart_4151320 baseEnd_4151320 := by
    simpa [prefixWord, tailWord_4151320, baseEnd_4151320] using wordTrace_append hprefix tailTrace_4151320
  have hstable : (prefixWord ++ tailWord_4151320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151320).length < 2 ^ (prefixWord ++ tailWord_4151320).sum := by decide
  have hdescent : baseEnd_4151320 < baseStart_4151320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151330 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_4151330 : Nat := 118140960795 + 4151330 * 2 ^ 59
def prefixEnd_4151330 : Nat := 4983230072969 + 3 ^ 40 * 4151330 * 2
def baseEnd_4151330 : Nat := 710542548476449378661129

theorem tailTrace_4151330 : CollatzResearch.WordTrace tailWord_4151330 prefixEnd_4151330 710542548476449378661129 := by
  unfold tailWord_4151330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37852861012611968890868861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100940962700298583708983629 37852861012611968890868861)
  ·
    refine ⟨14194822879729488334075823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37852861012611968890868861 14194822879729488334075823)
    ·
      refine ⟨21292234319594232501113735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14194822879729488334075823 21292234319594232501113735)
      ·
        refine ⟨31938351479391348751670603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21292234319594232501113735 31938351479391348751670603)
        ·
          refine ⟨47907527219087023127505905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31938351479391348751670603 47907527219087023127505905)
          ·
            refine ⟨35930645414315267345629429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47907527219087023127505905 35930645414315267345629429)
            ·
              refine ⟨3368498007592056313652759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35930645414315267345629429 3368498007592056313652759)
              ·
                refine ⟨5052747011388084470479139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368498007592056313652759 5052747011388084470479139)
                ·
                  refine ⟨7579120517082126705718709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052747011388084470479139 7579120517082126705718709)
                  ·
                    refine ⟨710542548476449378661129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7579120517082126705718709 710542548476449378661129)
                    ·
                      rfl

theorem cell23_4151330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_4151330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151330 prefixEnd_4151330 := by exact prefixLift 4151330
  have htrace : WordTrace (prefixWord ++ tailWord_4151330) baseStart_4151330 baseEnd_4151330 := by
    simpa [prefixWord, tailWord_4151330, baseEnd_4151330] using wordTrace_append hprefix tailTrace_4151330
  have hstable : (prefixWord ++ tailWord_4151330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151330).length < 2 ^ (prefixWord ++ tailWord_4151330).sum := by decide
  have hdescent : baseEnd_4151330 < baseStart_4151330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151344 : List Nat := [2, 1, 1, 1, 2, 7, 2, 2, 1, 1, 3]
def baseStart_4151344 : Nat := 118140960795 + 4151344 * 2 ^ 59
def prefixEnd_4151344 : Nat := 4983230072969 + 3 ^ 40 * 4151344 * 2
def baseEnd_4151344 : Nat := 2131634834158511081208323

theorem tailTrace_4151344 : CollatzResearch.WordTrace tailWord_4151344 prefixEnd_4151344 2131634834158511081208323 := by
  unfold tailWord_4151344
  simp only [CollatzResearch.WordTrace]
  refine ⟨75705977336198577977242543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100941303114931437302990057 75705977336198577977242543)
  ·
    refine ⟨113558966004297866965863815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75705977336198577977242543 113558966004297866965863815)
    ·
      refine ⟨170338449006446800448795723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113558966004297866965863815 170338449006446800448795723)
      ·
        refine ⟨255507673509670200673193585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170338449006446800448795723 255507673509670200673193585)
        ·
          refine ⟨191630755132252650504895189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255507673509670200673193585 191630755132252650504895189)
          ·
            refine ⟨4491345823412171496208481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 191630755132252650504895189 4491345823412171496208481)
            ·
              refine ⟨3368509367559128622156361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491345823412171496208481 3368509367559128622156361)
              ·
                refine ⟨2526382025669346466617271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3368509367559128622156361 2526382025669346466617271)
                ·
                  refine ⟨3789573038504019699925907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526382025669346466617271 3789573038504019699925907)
                  ·
                    refine ⟨5684359557756029549888861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3789573038504019699925907 5684359557756029549888861)
                    ·
                      refine ⟨2131634834158511081208323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5684359557756029549888861 2131634834158511081208323)
                      ·
                        rfl

theorem cell23_4151344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 1, 1, 3].length) (baseStart_4151344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151344 prefixEnd_4151344 := by exact prefixLift 4151344
  have htrace : WordTrace (prefixWord ++ tailWord_4151344) baseStart_4151344 baseEnd_4151344 := by
    simpa [prefixWord, tailWord_4151344, baseEnd_4151344] using wordTrace_append hprefix tailTrace_4151344
  have hstable : (prefixWord ++ tailWord_4151344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151344).length < 2 ^ (prefixWord ++ tailWord_4151344).sum := by decide
  have hdescent : baseEnd_4151344 < baseStart_4151344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151383 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 3]
def baseStart_4151383 : Nat := 118140960795 + 4151383 * 2 ^ 59
def prefixEnd_4151383 : Nat := 4983230072969 + 3 ^ 40 * 4151383 * 2
def baseEnd_4151383 : Nat := 2131654859904036428620643

theorem tailTrace_4151383 : CollatzResearch.WordTrace tailWord_4151383 prefixEnd_4151383 2131654859904036428620643 := by
  unfold tailWord_4151383
  simp only [CollatzResearch.WordTrace]
  refine ⟨151413377119255865615154803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100942251412837243743436535 151413377119255865615154803)
  ·
    refine ⟨227120065678883798422732205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151413377119255865615154803 227120065678883798422732205)
    ·
      refine ⟨85170024629581424408524577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227120065678883798422732205 85170024629581424408524577)
      ·
        refine ⟨63877518472186068306393433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85170024629581424408524577 63877518472186068306393433)
        ·
          refine ⟨47908138854139551229795075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63877518472186068306393433 47908138854139551229795075)
          ·
            refine ⟨71862208281209326844692613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47908138854139551229795075 71862208281209326844692613)
            ·
              refine ⟨13474164052726748783379865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71862208281209326844692613 13474164052726748783379865)
              ·
                refine ⟨10105623039545061587534899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13474164052726748783379865 10105623039545061587534899)
                ·
                  refine ⟨15158434559317592381302349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10105623039545061587534899 15158434559317592381302349)
                  ·
                    refine ⟨5684412959744097142988381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15158434559317592381302349 5684412959744097142988381)
                    ·
                      refine ⟨2131654859904036428620643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5684412959744097142988381 2131654859904036428620643)
                      ·
                        rfl

theorem cell23_4151383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_4151383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151383 prefixEnd_4151383 := by exact prefixLift 4151383
  have htrace : WordTrace (prefixWord ++ tailWord_4151383) baseStart_4151383 baseEnd_4151383 := by
    simpa [prefixWord, tailWord_4151383, baseEnd_4151383] using wordTrace_append hprefix tailTrace_4151383
  have hstable : (prefixWord ++ tailWord_4151383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151383).length < 2 ^ (prefixWord ++ tailWord_4151383).sum := by decide
  have hdescent : baseEnd_4151383 < baseStart_4151383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151384 : List Nat := [2, 1, 2, 2, 1, 5, 2, 3, 1, 2, 2]
def baseStart_4151384 : Nat := 118140960795 + 4151384 * 2 ^ 59
def prefixEnd_4151384 : Nat := 4983230072969 + 3 ^ 40 * 4151384 * 2
def baseEnd_4151384 : Nat := 2131655373384690924708139

theorem tailTrace_4151384 : CollatzResearch.WordTrace tailWord_4151384 prefixEnd_4151384 2131655373384690924708139 := by
  unfold tailWord_4151384
  simp only [CollatzResearch.WordTrace]
  refine ⟨75706706796126121392970603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100942275728168161857294137 75706706796126121392970603)
  ·
    refine ⟨113560060194189182089455905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75706706796126121392970603 113560060194189182089455905)
    ·
      refine ⟨85170045145641886567091929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113560060194189182089455905 85170045145641886567091929)
      ·
        refine ⟨63877533859231414925318947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85170045145641886567091929 63877533859231414925318947)
        ·
          refine ⟨95816300788847122387978421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63877533859231414925318947 95816300788847122387978421)
          ·
            refine ⟨8982778198954417723872977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95816300788847122387978421 8982778198954417723872977)
            ·
              refine ⟨6737083649215813292904733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8982778198954417723872977 6737083649215813292904733)
              ·
                refine ⟨2526406368455929984839275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6737083649215813292904733 2526406368455929984839275)
                ·
                  refine ⟨3789609552683894977258913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526406368455929984839275 3789609552683894977258913)
                  ·
                    refine ⟨2842207164512921232944185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3789609552683894977258913 2842207164512921232944185)
                    ·
                      refine ⟨2131655373384690924708139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842207164512921232944185 2131655373384690924708139)
                      ·
                        rfl

theorem cell23_4151384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_4151384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151384 prefixEnd_4151384 := by exact prefixLift 4151384
  have htrace : WordTrace (prefixWord ++ tailWord_4151384) baseStart_4151384 baseEnd_4151384 := by
    simpa [prefixWord, tailWord_4151384, baseEnd_4151384] using wordTrace_append hprefix tailTrace_4151384
  have hstable : (prefixWord ++ tailWord_4151384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151384).length < 2 ^ (prefixWord ++ tailWord_4151384).sum := by decide
  have hdescent : baseEnd_4151384 < baseStart_4151384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151394 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_4151394 : Nat := 118140960795 + 4151394 * 2 ^ 59
def prefixEnd_4151394 : Nat := 4983230072969 + 3 ^ 40 * 4151394 * 2
def baseEnd_4151394 : Nat := 710553502730411961861031

theorem tailTrace_4151394 : CollatzResearch.WordTrace tailWord_4151394 prefixEnd_4151394 710553502730411961861031 := by
  unfold tailWord_4151394
  simp only [CollatzResearch.WordTrace]
  refine ⟨37853444580554003623451309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100942518881477342995870157 37853444580554003623451309)
  ·
    refine ⟨14195041717707751358794241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37853444580554003623451309 14195041717707751358794241)
    ·
      refine ⟨10646281288280813519095681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14195041717707751358794241 10646281288280813519095681)
      ·
        refine ⟨7984710966210610139321761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10646281288280813519095681 7984710966210610139321761)
        ·
          refine ⟨5988533224657957604491321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7984710966210610139321761 5988533224657957604491321)
          ·
            refine ⟨4491399918493468203368491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5988533224657957604491321 4491399918493468203368491)
            ·
              refine ⟨6737099877740202305052737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491399918493468203368491 6737099877740202305052737)
              ·
                refine ⟨5052824908305151728789553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6737099877740202305052737 5052824908305151728789553)
                ·
                  refine ⟨3789618681228863796592165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5052824908305151728789553 3789618681228863796592165)
                  ·
                    refine ⟨710553502730411961861031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3789618681228863796592165 710553502730411961861031)
                    ·
                      rfl

theorem cell23_4151394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_4151394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151394 prefixEnd_4151394 := by exact prefixLift 4151394
  have htrace : WordTrace (prefixWord ++ tailWord_4151394) baseStart_4151394 baseEnd_4151394 := by
    simpa [prefixWord, tailWord_4151394, baseEnd_4151394] using wordTrace_append hprefix tailTrace_4151394
  have hstable : (prefixWord ++ tailWord_4151394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151394).length < 2 ^ (prefixWord ++ tailWord_4151394).sum := by decide
  have hdescent : baseEnd_4151394 < baseStart_4151394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151427 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 1, 3, 2]
def baseStart_4151427 : Nat := 118140960795 + 4151427 * 2 ^ 59
def prefixEnd_4151427 : Nat := 4983230072969 + 3 ^ 40 * 4151427 * 2
def baseEnd_4151427 : Nat := 2131677453052834256470441

theorem tailTrace_4151427 : CollatzResearch.WordTrace tailWord_4151427 prefixEnd_4151427 2131677453052834256470441 := by
  unfold tailWord_4151427
  simp only [CollatzResearch.WordTrace]
  refine ⟨151414981931096461129756535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100943321287397640753171023 151414981931096461129756535)
  ·
    refine ⟨227122472896644691694634803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151414981931096461129756535 227122472896644691694634803)
    ·
      refine ⟨340683709344967037541952205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227122472896644691694634803 340683709344967037541952205)
      ·
        refine ⟨127756391004362639078232077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340683709344967037541952205 127756391004362639078232077)
        ·
          refine ⟨47908646626635989654337029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127756391004362639078232077 47908646626635989654337029)
          ·
            refine ⟨8982871242494248060188193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47908646626635989654337029 8982871242494248060188193)
            ·
              refine ⟨6737153431870686045141145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8982871242494248060188193 6737153431870686045141145)
              ·
                refine ⟨5052865073903014533855859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6737153431870686045141145 5052865073903014533855859)
                ·
                  refine ⟨7579297610854521800783789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052865073903014533855859 7579297610854521800783789)
                  ·
                    refine ⟨2842236604070445675293921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7579297610854521800783789 2842236604070445675293921)
                    ·
                      refine ⟨2131677453052834256470441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842236604070445675293921 2131677453052834256470441)
                      ·
                        rfl

theorem cell23_4151427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_4151427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151427 prefixEnd_4151427 := by exact prefixLift 4151427
  have htrace : WordTrace (prefixWord ++ tailWord_4151427) baseStart_4151427 baseEnd_4151427 := by
    simpa [prefixWord, tailWord_4151427, baseEnd_4151427] using wordTrace_append hprefix tailTrace_4151427
  have hstable : (prefixWord ++ tailWord_4151427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151427).length < 2 ^ (prefixWord ++ tailWord_4151427).sum := by decide
  have hdescent : baseEnd_4151427 < baseStart_4151427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151440 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 6, 2, 2]
def baseStart_4151440 : Nat := 118140960795 + 4151440 * 2 ^ 59
def prefixEnd_4151440 : Nat := 4983230072969 + 3 ^ 40 * 4151440 * 2
def baseEnd_4151440 : Nat := 2131684128301342705607881

theorem tailTrace_4151440 : CollatzResearch.WordTrace tailWord_4151440 prefixEnd_4151440 2131684128301342705607881 := by
  unfold tailWord_4151440
  simp only [CollatzResearch.WordTrace]
  refine ⟨75707728040024682174989887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100943637386699576233319849 75707728040024682174989887)
  ·
    refine ⟨113561592060037023262484831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75707728040024682174989887 113561592060037023262484831)
    ·
      refine ⟨170342388090055534893727247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113561592060037023262484831 170342388090055534893727247)
      ·
        refine ⟨255513582135083302340590871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170342388090055534893727247 255513582135083302340590871)
        ·
          refine ⟨383270373202624953510886307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255513582135083302340590871 383270373202624953510886307)
          ·
            refine ⟨574905559803937430266329461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383270373202624953510886307 574905559803937430266329461)
            ·
              refine ⟨53897396231619134087468387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 574905559803937430266329461 53897396231619134087468387)
              ·
                refine ⟨80846094347428701131202581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53897396231619134087468387 80846094347428701131202581)
                ·
                  refine ⟨3789660672535720365525121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80846094347428701131202581 3789660672535720365525121)
                  ·
                    refine ⟨2842245504401790274143841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3789660672535720365525121 2842245504401790274143841)
                    ·
                      refine ⟨2131684128301342705607881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842245504401790274143841 2131684128301342705607881)
                      ·
                        rfl

theorem cell23_4151440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 6, 2, 2].length) (baseStart_4151440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151440 prefixEnd_4151440 := by exact prefixLift 4151440
  have htrace : WordTrace (prefixWord ++ tailWord_4151440) baseStart_4151440 baseEnd_4151440 := by
    simpa [prefixWord, tailWord_4151440, baseEnd_4151440] using wordTrace_append hprefix tailTrace_4151440
  have hstable : (prefixWord ++ tailWord_4151440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151440).length < 2 ^ (prefixWord ++ tailWord_4151440).sum := by decide
  have hdescent : baseEnd_4151440 < baseStart_4151440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151457 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 4, 2, 2]
def baseStart_4151457 : Nat := 118140960795 + 4151457 * 2 ^ 59
def prefixEnd_4151457 : Nat := 4983230072969 + 3 ^ 40 * 4151457 * 2
def baseEnd_4151457 : Nat := 2131692857472469139095303

theorem tailTrace_4151457 : CollatzResearch.WordTrace tailWord_4151457 prefixEnd_4151457 2131692857472469139095303 := by
  unfold tailWord_4151457
  simp only [CollatzResearch.WordTrace]
  refine ⟨151416076120987776253348625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100944050747325184168899083 151416076120987776253348625)
  ·
    refine ⟨113562057090740832190011469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151416076120987776253348625 113562057090740832190011469)
    ·
      refine ⟨42585771409027812071254301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113562057090740832190011469 42585771409027812071254301)
      ·
        refine ⟨15969664278385429526720363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42585771409027812071254301 15969664278385429526720363)
        ·
          refine ⟨23954496417578144290080545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15969664278385429526720363 23954496417578144290080545)
          ·
            refine ⟨17965872313183608217560409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23954496417578144290080545 17965872313183608217560409)
            ·
              refine ⟨13474404234887706163170307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17965872313183608217560409 13474404234887706163170307)
              ·
                refine ⟨20211606352331559244755461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13474404234887706163170307 20211606352331559244755461)
                ·
                  refine ⟨3789676191062167358391649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20211606352331559244755461 3789676191062167358391649)
                  ·
                    refine ⟨2842257143296625518793737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3789676191062167358391649 2842257143296625518793737)
                    ·
                      refine ⟨2131692857472469139095303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842257143296625518793737 2131692857472469139095303)
                      ·
                        rfl

theorem cell23_4151457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_4151457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151457 prefixEnd_4151457 := by exact prefixLift 4151457
  have htrace : WordTrace (prefixWord ++ tailWord_4151457) baseStart_4151457 baseEnd_4151457 := by
    simpa [prefixWord, tailWord_4151457, baseEnd_4151457] using wordTrace_append hprefix tailTrace_4151457
  have hstable : (prefixWord ++ tailWord_4151457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151457).length < 2 ^ (prefixWord ++ tailWord_4151457).sum := by decide
  have hdescent : baseEnd_4151457 < baseStart_4151457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151493 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_4151493 : Nat := 118140960795 + 4151493 * 2 ^ 59
def prefixEnd_4151493 : Nat := 4983230072969 + 3 ^ 40 * 4151493 * 2
def baseEnd_4151493 : Nat := 710570447592010332748379

theorem tailTrace_4151493 : CollatzResearch.WordTrace tailWord_4151493 prefixEnd_4151493 710570447592010332748379 := by
  unfold tailWord_4151493
  simp only [CollatzResearch.WordTrace]
  refine ⟨151417389148857354401659133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100944926099238236267772755 151417389148857354401659133)
  ·
    refine ⟨56781520930821507900622175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151417389148857354401659133 56781520930821507900622175)
    ·
      refine ⟨85172281396232261850933263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56781520930821507900622175 85172281396232261850933263)
      ·
        refine ⟨127758422094348392776399895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85172281396232261850933263 127758422094348392776399895)
        ·
          refine ⟨191637633141522589164599843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127758422094348392776399895 191637633141522589164599843)
          ·
            refine ⟨287456449712283883746899765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191637633141522589164599843 287456449712283883746899765)
            ·
              refine ⟨26949042160526614101271853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287456449712283883746899765 26949042160526614101271853)
              ·
                refine ⟨10105890810197480287976945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26949042160526614101271853 10105890810197480287976945)
                ·
                  refine ⟨7579418107648110215982709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10105890810197480287976945 7579418107648110215982709)
                  ·
                    refine ⟨710570447592010332748379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7579418107648110215982709 710570447592010332748379)
                    ·
                      rfl

theorem cell23_4151493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_4151493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151493 prefixEnd_4151493 := by exact prefixLift 4151493
  have htrace : WordTrace (prefixWord ++ tailWord_4151493) baseStart_4151493 baseEnd_4151493 := by
    simpa [prefixWord, tailWord_4151493, baseEnd_4151493] using wordTrace_append hprefix tailTrace_4151493
  have hstable : (prefixWord ++ tailWord_4151493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151493).length < 2 ^ (prefixWord ++ tailWord_4151493).sum := by decide
  have hdescent : baseEnd_4151493 < baseStart_4151493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151517 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_4151517 : Nat := 118140960795 + 4151517 * 2 ^ 59
def prefixEnd_4151517 : Nat := 4983230072969 + 3 ^ 40 * 4151517 * 2
def baseEnd_4151517 : Nat := 2131723666311738904345027

theorem tailTrace_4151517 : CollatzResearch.WordTrace tailWord_4151517 prefixEnd_4151517 2131723666311738904345027 := by
  unfold tailWord_4151517
  simp only [CollatzResearch.WordTrace]
  refine ⟨151418264500770406500532805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100945509667180271000355203 151418264500770406500532805)
  ·
    refine ⟨28390924593894451218849901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151418264500770406500532805 28390924593894451218849901)
    ·
      refine ⟨10646596722710419207068713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28390924593894451218849901 10646596722710419207068713)
      ·
        refine ⟨7984947542032814405301535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10646596722710419207068713 7984947542032814405301535)
        ·
          refine ⟨11977421313049221607952303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7984947542032814405301535 11977421313049221607952303)
          ·
            refine ⟨17966131969573832411928455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11977421313049221607952303 17966131969573832411928455)
            ·
              refine ⟨26949197954360748617892683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17966131969573832411928455 26949197954360748617892683)
              ·
                refine ⟨40423796931541122926839025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26949197954360748617892683 40423796931541122926839025)
                ·
                  refine ⟨30317847698655842195129269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40423796931541122926839025 30317847698655842195129269)
                  ·
                    refine ⟨2842298221748985205793369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30317847698655842195129269 2842298221748985205793369)
                    ·
                      refine ⟨2131723666311738904345027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842298221748985205793369 2131723666311738904345027)
                      ·
                        rfl

theorem cell23_4151517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_4151517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151517 prefixEnd_4151517 := by exact prefixLift 4151517
  have htrace : WordTrace (prefixWord ++ tailWord_4151517) baseStart_4151517 baseEnd_4151517 := by
    simpa [prefixWord, tailWord_4151517, baseEnd_4151517] using wordTrace_append hprefix tailTrace_4151517
  have hstable : (prefixWord ++ tailWord_4151517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151517).length < 2 ^ (prefixWord ++ tailWord_4151517).sum := by decide
  have hdescent : baseEnd_4151517 < baseStart_4151517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151553 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 8]
def baseStart_4151553 : Nat := 118140960795 + 4151553 * 2 ^ 59
def prefixEnd_4151553 : Nat := 4983230072969 + 3 ^ 40 * 4151553 * 2
def baseEnd_4151553 : Nat := 236860239068366751499429

theorem tailTrace_4151553 : CollatzResearch.WordTrace tailWord_4151553 prefixEnd_4151553 236860239068366751499429 := by
  unfold tailWord_4151553
  simp only [CollatzResearch.WordTrace]
  refine ⟨151419577528639984648843313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100946385019093323099228875 151419577528639984648843313)
  ·
    refine ⟨113564683146479988486632485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151419577528639984648843313 113564683146479988486632485)
    ·
      refine ⟨21293378089964997841243591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113564683146479988486632485 21293378089964997841243591)
      ·
        refine ⟨31940067134947496761865387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21293378089964997841243591 31940067134947496761865387)
        ·
          refine ⟨47910100702421245142798081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31940067134947496761865387 47910100702421245142798081)
          ·
            refine ⟨35932575526815933857098561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47910100702421245142798081 35932575526815933857098561)
            ·
              refine ⟨26949431645111950392823921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35932575526815933857098561 26949431645111950392823921)
              ·
                refine ⟨20212073733833962794617941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26949431645111950392823921 20212073733833962794617941)
                ·
                  refine ⟨236860239068366751499429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20212073733833962794617941 236860239068366751499429)
                  ·
                    rfl

theorem cell23_4151553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 8].length) (baseStart_4151553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151553 prefixEnd_4151553 := by exact prefixLift 4151553
  have htrace : WordTrace (prefixWord ++ tailWord_4151553) baseStart_4151553 baseEnd_4151553 := by
    simpa [prefixWord, tailWord_4151553, baseEnd_4151553] using wordTrace_append hprefix tailTrace_4151553
  have hstable : (prefixWord ++ tailWord_4151553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151553).length < 2 ^ (prefixWord ++ tailWord_4151553).sum := by decide
  have hdescent : baseEnd_4151553 < baseStart_4151553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151573 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_4151573 : Nat := 118140960795 + 4151573 * 2 ^ 59
def prefixEnd_4151573 : Nat := 4983230072969 + 3 ^ 40 * 4151573 * 2
def baseEnd_4151573 : Nat := 2131752421228390685244769

theorem tailTrace_4151573 : CollatzResearch.WordTrace tailWord_4151573 prefixEnd_4151573 2131752421228390685244769 := by
  unfold tailWord_4151573
  simp only [CollatzResearch.WordTrace]
  refine ⟨151420306988567528064571373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100946871325711685376380915 151420306988567528064571373)
  ·
    refine ⟨56782615120712823024214265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151420306988567528064571373 56782615120712823024214265)
    ·
      refine ⟨42586961340534617268160699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56782615120712823024214265 42586961340534617268160699)
      ·
        refine ⟨63880442010801925902241049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42586961340534617268160699 63880442010801925902241049)
        ·
          refine ⟨47910331508101444426680787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63880442010801925902241049 47910331508101444426680787)
          ·
            refine ⟨71865497262152166640021181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47910331508101444426680787 71865497262152166640021181)
            ·
              refine ⟨26949561473307062490007943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71865497262152166640021181 26949561473307062490007943)
              ·
                refine ⟨40424342209960593735011915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26949561473307062490007943 40424342209960593735011915)
                ·
                  refine ⟨60636513314940890602517873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40424342209960593735011915 60636513314940890602517873)
                  ·
                    refine ⟨45477384986205667951888405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60636513314940890602517873 45477384986205667951888405)
                    ·
                      refine ⟨2131752421228390685244769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45477384986205667951888405 2131752421228390685244769)
                      ·
                        rfl

theorem cell23_4151573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_4151573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151573 prefixEnd_4151573 := by exact prefixLift 4151573
  have htrace : WordTrace (prefixWord ++ tailWord_4151573) baseStart_4151573 baseEnd_4151573 := by
    simpa [prefixWord, tailWord_4151573, baseEnd_4151573] using wordTrace_append hprefix tailTrace_4151573
  have hstable : (prefixWord ++ tailWord_4151573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151573).length < 2 ^ (prefixWord ++ tailWord_4151573).sum := by decide
  have hdescent : baseEnd_4151573 < baseStart_4151573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151682 : List Nat := [3, 4, 2, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_4151682 : Nat := 118140960795 + 4151682 * 2 ^ 59
def prefixEnd_4151682 : Nat := 4983230072969 + 3 ^ 40 * 4151682 * 2
def baseEnd_4151682 : Nat := 2131808390619730758781769

theorem tailTrace_4151682 : CollatzResearch.WordTrace tailWord_4151682 prefixEnd_4151682 2131808390619730758781769 := by
  unfold tailWord_4151682
  simp only [CollatzResearch.WordTrace]
  refine ⟨37856070636293159920072325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100949521696781759786859533 37856070636293159920072325)
  ·
    refine ⟨7098013244304967485013561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37856070636293159920072325 7098013244304967485013561)
    ·
      refine ⟨5323509933228725613760171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7098013244304967485013561 5323509933228725613760171)
      ·
        refine ⟨7985264899843088420640257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5323509933228725613760171 7985264899843088420640257)
        ·
          refine ⟨5988948674882316315480193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7985264899843088420640257 5988948674882316315480193)
          ·
            refine ⟨4491711506161737236610145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5988948674882316315480193 4491711506161737236610145)
            ·
              refine ⟨3368783629621302927457609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491711506161737236610145 3368783629621302927457609)
              ·
                refine ⟨2526587722215977195593207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3368783629621302927457609 2526587722215977195593207)
                ·
                  refine ⟨3789881583323965793389811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526587722215977195593207 3789881583323965793389811)
                  ·
                    refine ⟨5684822374985948690084717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3789881583323965793389811 5684822374985948690084717)
                    ·
                      refine ⟨2131808390619730758781769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5684822374985948690084717 2131808390619730758781769)
                      ·
                        rfl

theorem cell23_4151682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_4151682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151682 prefixEnd_4151682 := by exact prefixLift 4151682
  have htrace : WordTrace (prefixWord ++ tailWord_4151682) baseStart_4151682 baseEnd_4151682 := by
    simpa [prefixWord, tailWord_4151682, baseEnd_4151682] using wordTrace_append hprefix tailTrace_4151682
  have hstable : (prefixWord ++ tailWord_4151682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151682).length < 2 ^ (prefixWord ++ tailWord_4151682).sum := by decide
  have hdescent : baseEnd_4151682 < baseStart_4151682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151704 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4151704 : Nat := 118140960795 + 4151704 * 2 ^ 59
def prefixEnd_4151704 : Nat := 4983230072969 + 3 ^ 40 * 4151704 * 2
def baseEnd_4151704 : Nat := 2131819687194129672706667

theorem tailTrace_4151704 : CollatzResearch.WordTrace tailWord_4151704 prefixEnd_4151704 2131819687194129672706667 := by
  unfold tailWord_4151704
  simp only [CollatzResearch.WordTrace]
  refine ⟨75712542475546468718795083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100950056634061958291726777 75712542475546468718795083)
  ·
    refine ⟨113568813713319703078192625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75712542475546468718795083 113568813713319703078192625)
    ·
      refine ⟨85176610284989777308644469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113568813713319703078192625 85176610284989777308644469)
      ·
        refine ⟨7985307214217791622685419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85176610284989777308644469 7985307214217791622685419)
        ·
          refine ⟨11977960821326687434028129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7985307214217791622685419 11977960821326687434028129)
          ·
            refine ⟨8983470615995015575521097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11977960821326687434028129 8983470615995015575521097)
            ·
              refine ⟨6737602961996261681640823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8983470615995015575521097 6737602961996261681640823)
              ·
                refine ⟨10106404442994392522461235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6737602961996261681640823 10106404442994392522461235)
                ·
                  refine ⟨15159606664491588783691853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10106404442994392522461235 15159606664491588783691853)
                  ·
                    refine ⟨5684852499184345793884445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15159606664491588783691853 5684852499184345793884445)
                    ·
                      refine ⟨2131819687194129672706667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5684852499184345793884445 2131819687194129672706667)
                      ·
                        rfl

theorem cell23_4151704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4151704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151704 prefixEnd_4151704 := by exact prefixLift 4151704
  have htrace : WordTrace (prefixWord ++ tailWord_4151704) baseStart_4151704 baseEnd_4151704 := by
    simpa [prefixWord, tailWord_4151704, baseEnd_4151704] using wordTrace_append hprefix tailTrace_4151704
  have hstable : (prefixWord ++ tailWord_4151704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151704).length < 2 ^ (prefixWord ++ tailWord_4151704).sum := by decide
  have hdescent : baseEnd_4151704 < baseStart_4151704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151714 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_4151714 : Nat := 118140960795 + 4151714 * 2 ^ 59
def prefixEnd_4151714 : Nat := 4983230072969 + 3 ^ 40 * 4151714 * 2
def baseEnd_4151714 : Nat := 2131824822000674633581621

theorem tailTrace_4151714 : CollatzResearch.WordTrace tailWord_4151714 prefixEnd_4151714 2131824822000674633581621 := by
  unfold tailWord_4151714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37856362420264177286363549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100950299787371139430302797 37856362420264177286363549)
  ·
    refine ⟨14196135907599066482386331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37856362420264177286363549 14196135907599066482386331)
    ·
      refine ⟨21294203861398599723579497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14196135907599066482386331 21294203861398599723579497)
      ·
        refine ⟨15970652896048949792684623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21294203861398599723579497 15970652896048949792684623)
        ·
          refine ⟨23955979344073424689026935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15970652896048949792684623 23955979344073424689026935)
          ·
            refine ⟨35933969016110137033540403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23955979344073424689026935 35933969016110137033540403)
            ·
              refine ⟨53900953524165205550310605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35933969016110137033540403 53900953524165205550310605)
              ·
                refine ⟨20212857571561952081366477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53900953524165205550310605 20212857571561952081366477)
                ·
                  refine ⟨7579821589335732030512429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20212857571561952081366477 7579821589335732030512429)
                  ·
                    refine ⟨2842433096000899511442161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7579821589335732030512429 2842433096000899511442161)
                    ·
                      refine ⟨2131824822000674633581621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842433096000899511442161 2131824822000674633581621)
                      ·
                        rfl

theorem cell23_4151714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_4151714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151714 prefixEnd_4151714 := by exact prefixLift 4151714
  have htrace : WordTrace (prefixWord ++ tailWord_4151714) baseStart_4151714 baseEnd_4151714 := by
    simpa [prefixWord, tailWord_4151714, baseEnd_4151714] using wordTrace_append hprefix tailTrace_4151714
  have hstable : (prefixWord ++ tailWord_4151714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151714).length < 2 ^ (prefixWord ++ tailWord_4151714).sum := by decide
  have hdescent : baseEnd_4151714 < baseStart_4151714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151722 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4151722 : Nat := 118140960795 + 4151722 * 2 ^ 59
def prefixEnd_4151722 : Nat := 4983230072969 + 3 ^ 40 * 4151722 * 2
def baseEnd_4151722 : Nat := 2131828929845910602281585

theorem tailTrace_4151722 : CollatzResearch.WordTrace tailWord_4151722 prefixEnd_4151722 2131828929845910602281585 := by
  unfold tailWord_4151722
  simp only [CollatzResearch.WordTrace]
  refine ⟨37856435366256931627936355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100950494310018484341163613 37856435366256931627936355)
  ·
    refine ⟨56784653049385397441904533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37856435366256931627936355 56784653049385397441904533)
    ·
      refine ⟨2661780611689940505089275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56784653049385397441904533 2661780611689940505089275)
      ·
        refine ⟨3992670917534910757633913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661780611689940505089275 3992670917534910757633913)
        ·
          refine ⟨2994503188151183068225435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3992670917534910757633913 2994503188151183068225435)
          ·
            refine ⟨4491754782226774602338153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994503188151183068225435 4491754782226774602338153)
            ·
              refine ⟨3368816086670080951753615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491754782226774602338153 3368816086670080951753615)
              ·
                refine ⟨5053224130005121427630423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368816086670080951753615 5053224130005121427630423)
                ·
                  refine ⟨7579836195007682141445635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053224130005121427630423 7579836195007682141445635)
                  ·
                    refine ⟨11369754292511523212168453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7579836195007682141445635 11369754292511523212168453)
                    ·
                      refine ⟨2131828929845910602281585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11369754292511523212168453 2131828929845910602281585)
                      ·
                        rfl

theorem cell23_4151722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4151722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151722 prefixEnd_4151722 := by exact prefixLift 4151722
  have htrace : WordTrace (prefixWord ++ tailWord_4151722) baseStart_4151722 baseEnd_4151722 := by
    simpa [prefixWord, tailWord_4151722, baseEnd_4151722] using wordTrace_append hprefix tailTrace_4151722
  have hstable : (prefixWord ++ tailWord_4151722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151722).length < 2 ^ (prefixWord ++ tailWord_4151722).sum := by decide
  have hdescent : baseEnd_4151722 < baseStart_4151722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151725 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4151725 : Nat := 118140960795 + 4151725 * 2 ^ 59
def prefixEnd_4151725 : Nat := 4983230072969 + 3 ^ 40 * 4151725 * 2
def baseEnd_4151725 : Nat := 2131830470287874090544071

theorem tailTrace_4151725 : CollatzResearch.WordTrace tailWord_4151725 prefixEnd_4151725 2131830470287874090544071 := by
  unfold tailWord_4151725
  simp only [CollatzResearch.WordTrace]
  refine ⟨151425850884016858024104629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100950567256011238682736419 151425850884016858024104629)
  ·
    refine ⟨14196173520376580439759809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151425850884016858024104629 14196173520376580439759809)
    ·
      refine ⟨10647130140282435329819857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14196173520376580439759809 10647130140282435329819857)
      ·
        refine ⟨7985347605211826497364893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10647130140282435329819857 7985347605211826497364893)
        ·
          refine ⟨2994505351954434936511835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7985347605211826497364893 2994505351954434936511835)
          ·
            refine ⟨4491758027931652404767753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994505351954434936511835 4491758027931652404767753)
            ·
              refine ⟨3368818520948739303575815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491758027931652404767753 3368818520948739303575815)
              ·
                refine ⟨5053227781423108955363723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368818520948739303575815 5053227781423108955363723)
                ·
                  refine ⟨7579841672134663433045585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053227781423108955363723 7579841672134663433045585)
                  ·
                    refine ⟨5684881254100997574784189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7579841672134663433045585 5684881254100997574784189)
                    ·
                      refine ⟨2131830470287874090544071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5684881254100997574784189 2131830470287874090544071)
                      ·
                        rfl

theorem cell23_4151725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4151725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151725 prefixEnd_4151725 := by exact prefixLift 4151725
  have htrace : WordTrace (prefixWord ++ tailWord_4151725) baseStart_4151725 baseEnd_4151725 := by
    simpa [prefixWord, tailWord_4151725, baseEnd_4151725] using wordTrace_append hprefix tailTrace_4151725
  have hstable : (prefixWord ++ tailWord_4151725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151725).length < 2 ^ (prefixWord ++ tailWord_4151725).sum := by decide
  have hdescent : baseEnd_4151725 < baseStart_4151725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151730 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_4151730 : Nat := 118140960795 + 4151730 * 2 ^ 59
def prefixEnd_4151730 : Nat := 4983230072969 + 3 ^ 40 * 4151730 * 2
def baseEnd_4151730 : Nat := 2131833037691146570981547

theorem tailTrace_4151730 : CollatzResearch.WordTrace tailWord_4151730 prefixEnd_4151730 2131833037691146570981547 := by
  unfold tailWord_4151730
  simp only [CollatzResearch.WordTrace]
  refine ⟨37856508312249685969509161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100950688832665829252024429 37856508312249685969509161)
  ·
    refine ⟨28392381234187264477131871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37856508312249685969509161 28392381234187264477131871)
    ·
      refine ⟨42588571851280896715697807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28392381234187264477131871 42588571851280896715697807)
      ·
        refine ⟨63882857776921345073546711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42588571851280896715697807 63882857776921345073546711)
        ·
          refine ⟨95824286665382017610320067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63882857776921345073546711 95824286665382017610320067)
          ·
            refine ⟨143736429998073026415480101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95824286665382017610320067 143736429998073026415480101)
            ·
              refine ⟨26950580624638692452902519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143736429998073026415480101 26950580624638692452902519)
              ·
                refine ⟨40425870936958038679353779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26950580624638692452902519 40425870936958038679353779)
                ·
                  refine ⟨60638806405437058019030669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40425870936958038679353779 60638806405437058019030669)
                  ·
                    refine ⟨22739552402038896757136501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60638806405437058019030669 22739552402038896757136501)
                    ·
                      refine ⟨2131833037691146570981547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22739552402038896757136501 2131833037691146570981547)
                      ·
                        rfl

theorem cell23_4151730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_4151730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151730 prefixEnd_4151730 := by exact prefixLift 4151730
  have htrace : WordTrace (prefixWord ++ tailWord_4151730) baseStart_4151730 baseEnd_4151730 := by
    simpa [prefixWord, tailWord_4151730, baseEnd_4151730] using wordTrace_append hprefix tailTrace_4151730
  have hstable : (prefixWord ++ tailWord_4151730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151730).length < 2 ^ (prefixWord ++ tailWord_4151730).sum := by decide
  have hdescent : baseEnd_4151730 < baseStart_4151730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151784 : List Nat := [2, 1, 4, 1, 1, 3, 3, 3, 5]
def baseStart_4151784 : Nat := 118140960795 + 4151784 * 2 ^ 59
def prefixEnd_4151784 : Nat := 4983230072969 + 3 ^ 40 * 4151784 * 2
def baseEnd_4151784 : Nat := 236873418405165484411811

theorem tailTrace_4151784 : CollatzResearch.WordTrace tailWord_4151784 prefixEnd_4151784 236873418405165484411811 := by
  unfold tailWord_4151784
  simp only [CollatzResearch.WordTrace]
  refine ⟨75714001395401555550251203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100952001860535407400334937 75714001395401555550251203)
  ·
    refine ⟨113571002093102333325376805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75714001395401555550251203 113571002093102333325376805)
    ·
      refine ⟨21294562892456687498508151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113571002093102333325376805 21294562892456687498508151)
      ·
        refine ⟨31941844338685031247762227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21294562892456687498508151 31941844338685031247762227)
        ·
          refine ⟨47912766508027546871643341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31941844338685031247762227 47912766508027546871643341)
          ·
            refine ⟨17967287440510330076866253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47912766508027546871643341 17967287440510330076866253)
            ·
              refine ⟨6737732790191373778824845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17967287440510330076866253 6737732790191373778824845)
              ·
                refine ⟨2526649796321765167059317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6737732790191373778824845 2526649796321765167059317)
                ·
                  refine ⟨236873418405165484411811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2526649796321765167059317 236873418405165484411811)
                  ·
                    rfl

theorem cell23_4151784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 5].length) (baseStart_4151784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151784 prefixEnd_4151784 := by exact prefixLift 4151784
  have htrace : WordTrace (prefixWord ++ tailWord_4151784) baseStart_4151784 baseEnd_4151784 := by
    simpa [prefixWord, tailWord_4151784, baseEnd_4151784] using wordTrace_append hprefix tailTrace_4151784
  have hstable : (prefixWord ++ tailWord_4151784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151784).length < 2 ^ (prefixWord ++ tailWord_4151784).sum := by decide
  have hdescent : baseEnd_4151784 < baseStart_4151784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151827 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 5, 4]
def baseStart_4151827 : Nat := 118140960795 + 4151827 * 2 ^ 59
def prefixEnd_4151827 : Nat := 4983230072969 + 3 ^ 40 * 4151827 * 2
def baseEnd_4151827 : Nat := 710627615104877563822867

theorem tailTrace_4151827 : CollatzResearch.WordTrace tailWord_4151827 prefixEnd_4151827 710627615104877563822867 := by
  unfold tailWord_4151827
  simp only [CollatzResearch.WordTrace]
  refine ⟨151429571129647329444317735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100953047419764886296211823 151429571129647329444317735)
  ·
    refine ⟨227144356694470994166476603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151429571129647329444317735 227144356694470994166476603)
    ·
      refine ⟨340716535041706491249714905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227144356694470994166476603 340716535041706491249714905)
      ·
        refine ⟨255537401281279868437286179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340716535041706491249714905 255537401281279868437286179)
        ·
          refine ⟨383306101921919802655929269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255537401281279868437286179 383306101921919802655929269)
          ·
            refine ⟨35934947055179981498993369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383306101921919802655929269 35934947055179981498993369)
            ·
              refine ⟨26951210291384986124245027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35934947055179981498993369 26951210291384986124245027)
              ·
                refine ⟨40426815437077479186367541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26951210291384986124245027 40426815437077479186367541)
                ·
                  refine ⟨3790013947226013673721957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40426815437077479186367541 3790013947226013673721957)
                  ·
                    refine ⟨710627615104877563822867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3790013947226013673721957 710627615104877563822867)
                    ·
                      rfl

theorem cell23_4151827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 4].length) (baseStart_4151827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151827 prefixEnd_4151827 := by exact prefixLift 4151827
  have htrace : WordTrace (prefixWord ++ tailWord_4151827) baseStart_4151827 baseEnd_4151827 := by
    simpa [prefixWord, tailWord_4151827, baseEnd_4151827] using wordTrace_append hprefix tailTrace_4151827
  have hstable : (prefixWord ++ tailWord_4151827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151827).length < 2 ^ (prefixWord ++ tailWord_4151827).sum := by decide
  have hdescent : baseEnd_4151827 < baseStart_4151827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151831 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 2, 5]
def baseStart_4151831 : Nat := 118140960795 + 4151831 * 2 ^ 59
def prefixEnd_4151831 : Nat := 4983230072969 + 3 ^ 40 * 4151831 * 2
def baseEnd_4151831 : Nat := 710628299745750225272861

theorem tailTrace_4151831 : CollatzResearch.WordTrace tailWord_4151831 prefixEnd_4151831 710628299745750225272861 := by
  unfold tailWord_4151831
  simp only [CollatzResearch.WordTrace]
  refine ⟨151429717021632838127463347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100953144681088558751642231 151429717021632838127463347)
  ·
    refine ⟨227144575532449257191195021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151429717021632838127463347 227144575532449257191195021)
    ·
      refine ⟨85179215824668471446698133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227144575532449257191195021 85179215824668471446698133)
      ·
        refine ⟨3992775741781334599063975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85179215824668471446698133 3992775741781334599063975)
        ·
          refine ⟨5989163612672001898595963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992775741781334599063975 5989163612672001898595963)
          ·
            refine ⟨8983745419008002847893945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989163612672001898595963 8983745419008002847893945)
            ·
              refine ⟨6737809064256002135920459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8983745419008002847893945 6737809064256002135920459)
              ·
                refine ⟨10106713596384003203880689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6737809064256002135920459 10106713596384003203880689)
                ·
                  refine ⟨7580035197288002402910517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10106713596384003203880689 7580035197288002402910517)
                  ·
                    refine ⟨710628299745750225272861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7580035197288002402910517 710628299745750225272861)
                    ·
                      rfl

theorem cell23_4151831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_4151831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151831 prefixEnd_4151831 := by exact prefixLift 4151831
  have htrace : WordTrace (prefixWord ++ tailWord_4151831) baseStart_4151831 baseEnd_4151831 := by
    simpa [prefixWord, tailWord_4151831, baseEnd_4151831] using wordTrace_append hprefix tailTrace_4151831
  have hstable : (prefixWord ++ tailWord_4151831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151831).length < 2 ^ (prefixWord ++ tailWord_4151831).sum := by decide
  have hdescent : baseEnd_4151831 < baseStart_4151831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151857 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 6]
def baseStart_4151857 : Nat := 118140960795 + 4151857 * 2 ^ 59
def prefixEnd_4151857 : Nat := 4983230072969 + 3 ^ 40 * 4151857 * 2
def baseEnd_4151857 : Nat := 236877583303807508232607

theorem tailTrace_4151857 : CollatzResearch.WordTrace tailWord_4151857 prefixEnd_4151857 236877583303807508232607 := by
  unfold tailWord_4151857
  simp only [CollatzResearch.WordTrace]
  refine ⟨151430665319538644567909825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100953776879692429711939883 151430665319538644567909825)
  ·
    refine ⟨113572998989653983425932369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151430665319538644567909825 113572998989653983425932369)
    ·
      refine ⟨85179749242240487569449277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113572998989653983425932369 85179749242240487569449277)
      ·
        refine ⟨31942405965840182838543479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85179749242240487569449277 31942405965840182838543479)
        ·
          refine ⟨47913608948760274257815219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31942405965840182838543479 47913608948760274257815219)
          ·
            refine ⟨71870413423140411386722829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47913608948760274257815219 71870413423140411386722829)
            ·
              refine ⟨26951405033677654270021061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71870413423140411386722829 26951405033677654270021061)
              ·
                refine ⟨5053388443814560175628949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26951405033677654270021061 5053388443814560175628949)
                ·
                  refine ⟨236877583303807508232607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5053388443814560175628949 236877583303807508232607)
                  ·
                    rfl

theorem cell23_4151857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 6].length) (baseStart_4151857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151857 prefixEnd_4151857 := by exact prefixLift 4151857
  have htrace : WordTrace (prefixWord ++ tailWord_4151857) baseStart_4151857 baseEnd_4151857 := by
    simpa [prefixWord, tailWord_4151857, baseEnd_4151857] using wordTrace_append hprefix tailTrace_4151857
  have hstable : (prefixWord ++ tailWord_4151857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151857).length < 2 ^ (prefixWord ++ tailWord_4151857).sum := by decide
  have hdescent : baseEnd_4151857 < baseStart_4151857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151861 : List Nat := [1, 3, 3, 1, 1, 2, 3, 4, 1, 4]
def baseStart_4151861 : Nat := 118140960795 + 4151861 * 2 ^ 59
def prefixEnd_4151861 : Nat := 4983230072969 + 3 ^ 40 * 4151861 * 2
def baseEnd_4151861 : Nat := 710633434552295186147815

theorem tailTrace_4151861 : CollatzResearch.WordTrace tailWord_4151861 prefixEnd_4151861 710633434552295186147815 := by
  unfold tailWord_4151861
  simp only [CollatzResearch.WordTrace]
  refine ⟨151430811211524153251055437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100953874141016102167370291 151430811211524153251055437)
  ·
    refine ⟨56786554204321557469145789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151430811211524153251055437 56786554204321557469145789)
    ·
      refine ⟨21294957826620584050929671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56786554204321557469145789 21294957826620584050929671)
      ·
        refine ⟨31942436739930876076394507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21294957826620584050929671 31942436739930876076394507)
        ·
          refine ⟨47913655109896314114591761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31942436739930876076394507 47913655109896314114591761)
          ·
            refine ⟨35935241332422235585943821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47913655109896314114591761 35935241332422235585943821)
            ·
              refine ⟨13475715499658338344728933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35935241332422235585943821 13475715499658338344728933)
              ·
                refine ⟨2526696656185938439636675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13475715499658338344728933 2526696656185938439636675)
                ·
                  refine ⟨3790044984278907659455013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526696656185938439636675 3790044984278907659455013)
                  ·
                    refine ⟨710633434552295186147815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3790044984278907659455013 710633434552295186147815)
                    ·
                      rfl

theorem cell23_4151861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_4151861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151861 prefixEnd_4151861 := by exact prefixLift 4151861
  have htrace : WordTrace (prefixWord ++ tailWord_4151861) baseStart_4151861 baseEnd_4151861 := by
    simpa [prefixWord, tailWord_4151861, baseEnd_4151861] using wordTrace_append hprefix tailTrace_4151861
  have hstable : (prefixWord ++ tailWord_4151861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151861).length < 2 ^ (prefixWord ++ tailWord_4151861).sum := by decide
  have hdescent : baseEnd_4151861 < baseStart_4151861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151878 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_4151878 : Nat := 118140960795 + 4151878 * 2 ^ 59
def prefixEnd_4151878 : Nat := 4983230072969 + 3 ^ 40 * 4151878 * 2
def baseEnd_4151878 : Nat := 710636344276003997310289

theorem tailTrace_4151878 : CollatzResearch.WordTrace tailWord_4151878 prefixEnd_4151878 710636344276003997310289 := by
  unfold tailWord_4151878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732232226639455161075759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100954287501641710102949525 4732232226639455161075759)
  ·
    refine ⟨7098348339959182741613639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4732232226639455161075759 7098348339959182741613639)
    ·
      refine ⟨10647522509938774112420459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7098348339959182741613639 10647522509938774112420459)
      ·
        refine ⟨15971283764908161168630689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10647522509938774112420459 15971283764908161168630689)
        ·
          refine ⟨11978462823681120876473017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15971283764908161168630689 11978462823681120876473017)
          ·
            refine ⟨8983847117760840657354763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11978462823681120876473017 8983847117760840657354763)
            ·
              refine ⟨13475770676641260986032145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8983847117760840657354763 13475770676641260986032145)
              ·
                refine ⟨10106828007480945739524109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13475770676641260986032145 10106828007480945739524109)
                ·
                  refine ⟨3790060502805354652321541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10106828007480945739524109 3790060502805354652321541)
                  ·
                    refine ⟨710636344276003997310289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3790060502805354652321541 710636344276003997310289)
                    ·
                      rfl

theorem cell23_4151878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_4151878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151878 prefixEnd_4151878 := by exact prefixLift 4151878
  have htrace : WordTrace (prefixWord ++ tailWord_4151878) baseStart_4151878 baseEnd_4151878 := by
    simpa [prefixWord, tailWord_4151878, baseEnd_4151878] using wordTrace_append hprefix tailTrace_4151878
  have hstable : (prefixWord ++ tailWord_4151878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151878).length < 2 ^ (prefixWord ++ tailWord_4151878).sum := by decide
  have hdescent : baseEnd_4151878 < baseStart_4151878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151887 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 3, 5]
def baseStart_4151887 : Nat := 118140960795 + 4151887 * 2 ^ 59
def prefixEnd_4151887 : Nat := 4983230072969 + 3 ^ 40 * 4151887 * 2
def baseEnd_4151887 : Nat := 710637884717967485572775

theorem tailTrace_4151887 : CollatzResearch.WordTrace tailWord_4151887 prefixEnd_4151887 710637884717967485572775 := by
  unfold tailWord_4151887
  simp only [CollatzResearch.WordTrace]
  refine ⟨151431759509429959691501915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100954506339619973127667943 151431759509429959691501915)
  ·
    refine ⟨227147639264144939537252873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151431759509429959691501915 227147639264144939537252873)
    ·
      refine ⟨170360729448108704652939655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227147639264144939537252873 170360729448108704652939655)
      ·
        refine ⟨255541094172163056979409483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170360729448108704652939655 255541094172163056979409483)
        ·
          refine ⟨383311641258244585469114225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255541094172163056979409483 383311641258244585469114225)
          ·
            refine ⟨287483730943683439101835669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383311641258244585469114225 287483730943683439101835669)
            ·
              refine ⟨13475799887985161207898547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 287483730943683439101835669 13475799887985161207898547)
              ·
                refine ⟨20213699831977741811847821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13475799887985161207898547 20213699831977741811847821)
                ·
                  refine ⟨7580137436991653179442933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20213699831977741811847821 7580137436991653179442933)
                  ·
                    refine ⟨710637884717967485572775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7580137436991653179442933 710637884717967485572775)
                    ·
                      rfl

theorem cell23_4151887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_4151887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151887 prefixEnd_4151887 := by exact prefixLift 4151887
  have htrace : WordTrace (prefixWord ++ tailWord_4151887) baseStart_4151887 baseEnd_4151887 := by
    simpa [prefixWord, tailWord_4151887, baseEnd_4151887] using wordTrace_append hprefix tailTrace_4151887
  have hstable : (prefixWord ++ tailWord_4151887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151887).length < 2 ^ (prefixWord ++ tailWord_4151887).sum := by decide
  have hdescent : baseEnd_4151887 < baseStart_4151887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151918 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_4151918 : Nat := 118140960795 + 4151918 * 2 ^ 59
def prefixEnd_4151918 : Nat := 4983230072969 + 3 ^ 40 * 4151918 * 2
def baseEnd_4151918 : Nat := 2131929572054191835430683

theorem tailTrace_4151918 : CollatzResearch.WordTrace tailWord_4151918 prefixEnd_4151918 2131929572054191835430683 := by
  unfold tailWord_4151918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18929111271539706498235051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100955260114878434657253605 18929111271539706498235051)
  ·
    refine ⟨28393666907309559747352577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18929111271539706498235051 28393666907309559747352577)
    ·
      refine ⟨21295250180482169810514433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28393666907309559747352577 21295250180482169810514433)
      ·
        refine ⟨15971437635361627357885825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21295250180482169810514433 15971437635361627357885825)
        ·
          refine ⟨11978578226521220518414369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15971437635361627357885825 11978578226521220518414369)
          ·
            refine ⟨8983933669890915388810777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11978578226521220518414369 8983933669890915388810777)
            ·
              refine ⟨6737950252418186541608083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8983933669890915388810777 6737950252418186541608083)
              ·
                refine ⟨10106925378627279812412125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6737950252418186541608083 10106925378627279812412125)
                ·
                  refine ⟨3790097016985229929654547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10106925378627279812412125 3790097016985229929654547)
                  ·
                    refine ⟨5685145525477844894481821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3790097016985229929654547 5685145525477844894481821)
                    ·
                      refine ⟨2131929572054191835430683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5685145525477844894481821 2131929572054191835430683)
                      ·
                        rfl

theorem cell23_4151918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_4151918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151918 prefixEnd_4151918 := by exact prefixLift 4151918
  have htrace : WordTrace (prefixWord ++ tailWord_4151918) baseStart_4151918 baseEnd_4151918 := by
    simpa [prefixWord, tailWord_4151918, baseEnd_4151918] using wordTrace_append hprefix tailTrace_4151918
  have hstable : (prefixWord ++ tailWord_4151918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151918).length < 2 ^ (prefixWord ++ tailWord_4151918).sum := by decide
  have hdescent : baseEnd_4151918 < baseStart_4151918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151927 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_4151927 : Nat := 118140960795 + 4151927 * 2 ^ 59
def prefixEnd_4151927 : Nat := 4983230072969 + 3 ^ 40 * 4151927 * 2
def baseEnd_4151927 : Nat := 2131934193380082300218141

theorem tailTrace_4151927 : CollatzResearch.WordTrace tailWord_4151927 prefixEnd_4151927 2131934193380082300218141 := by
  unfold tailWord_4151927
  simp only [CollatzResearch.WordTrace]
  refine ⟨151433218429285046522958035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100955478952856697681972023 151433218429285046522958035)
  ·
    refine ⟨227149827643927569784437053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151433218429285046522958035 227149827643927569784437053)
    ·
      refine ⟨85181185366472838669163895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227149827643927569784437053 85181185366472838669163895)
      ·
        refine ⟨127771778049709258003745843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85181185366472838669163895 127771778049709258003745843)
        ·
          refine ⟨191657667074563887005618765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127771778049709258003745843 191657667074563887005618765)
          ·
            refine ⟨71871625152961457627107037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191657667074563887005618765 71871625152961457627107037)
            ·
              refine ⟨26951859432360546610165139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71871625152961457627107037 26951859432360546610165139)
              ·
                refine ⟨40427789148540819915247709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26951859432360546610165139 40427789148540819915247709)
                ·
                  refine ⟨15160420930702807468217891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40427789148540819915247709 15160420930702807468217891)
                  ·
                    refine ⟨22740631396054211202326837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15160420930702807468217891 22740631396054211202326837)
                    ·
                      refine ⟨2131934193380082300218141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22740631396054211202326837 2131934193380082300218141)
                      ·
                        rfl

theorem cell23_4151927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_4151927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151927 prefixEnd_4151927 := by exact prefixLift 4151927
  have htrace : WordTrace (prefixWord ++ tailWord_4151927) baseStart_4151927 baseEnd_4151927 := by
    simpa [prefixWord, tailWord_4151927, baseEnd_4151927] using wordTrace_append hprefix tailTrace_4151927
  have hstable : (prefixWord ++ tailWord_4151927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151927).length < 2 ^ (prefixWord ++ tailWord_4151927).sum := by decide
  have hdescent : baseEnd_4151927 < baseStart_4151927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151941 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 4]
def baseStart_4151941 : Nat := 118140960795 + 4151941 * 2 ^ 59
def prefixEnd_4151941 : Nat := 4983230072969 + 3 ^ 40 * 4151941 * 2
def baseEnd_4151941 : Nat := 2131941382109245245443077

theorem tailTrace_4151941 : CollatzResearch.WordTrace tailWord_4151941 prefixEnd_4151941 2131941382109245245443077 := by
  unfold tailWord_4151941
  simp only [CollatzResearch.WordTrace]
  refine ⟨151433729051234326913967677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100955819367489551275978451 151433729051234326913967677)
  ·
    refine ⟨56787648394212872592737879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151433729051234326913967677 56787648394212872592737879)
    ·
      refine ⟨85181472591319308889106819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56787648394212872592737879 85181472591319308889106819)
      ·
        refine ⟨127772208886978963333660229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85181472591319308889106819 127772208886978963333660229)
        ·
          refine ⟨23957289166308555625061293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127772208886978963333660229 23957289166308555625061293)
          ·
            refine ⟨8983983437365708359397985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23957289166308555625061293 8983983437365708359397985)
            ·
              refine ⟨6737987578024281269548489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8983983437365708359397985 6737987578024281269548489)
              ·
                refine ⟨5053490683518210952161367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6737987578024281269548489 5053490683518210952161367)
                ·
                  refine ⟨7580236025277316428242051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053490683518210952161367 7580236025277316428242051)
                  ·
                    refine ⟨11370354037915974642363077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7580236025277316428242051 11370354037915974642363077)
                    ·
                      refine ⟨2131941382109245245443077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11370354037915974642363077 2131941382109245245443077)
                      ·
                        rfl

theorem cell23_4151941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_4151941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151941 prefixEnd_4151941 := by exact prefixLift 4151941
  have htrace : WordTrace (prefixWord ++ tailWord_4151941) baseStart_4151941 baseEnd_4151941 := by
    simpa [prefixWord, tailWord_4151941, baseEnd_4151941] using wordTrace_append hprefix tailTrace_4151941
  have hstable : (prefixWord ++ tailWord_4151941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151941).length < 2 ^ (prefixWord ++ tailWord_4151941).sum := by decide
  have hdescent : baseEnd_4151941 < baseStart_4151941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151964 : List Nat := [2, 2, 3, 2, 2, 3, 9]
def baseStart_4151964 : Nat := 118140960795 + 4151964 * 2 ^ 59
def prefixEnd_4151964 : Nat := 4983230072969 + 3 ^ 40 * 4151964 * 2
def baseEnd_4151964 : Nat := 26320409779806156240191

theorem tailTrace_4151964 : CollatzResearch.WordTrace tailWord_4151964 prefixEnd_4151964 26320409779806156240191 := by
  unfold tailWord_4151964
  simp only [CollatzResearch.WordTrace]
  refine ⟨75717283965075500921027473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100956378620100667894703297 75717283965075500921027473)
  ·
    refine ⟨56787962973806625690770605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75717283965075500921027473 56787962973806625690770605)
    ·
      refine ⟨21295486115177484634038977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56787962973806625690770605 21295486115177484634038977)
      ·
        refine ⟨15971614586383113475529233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21295486115177484634038977 15971614586383113475529233)
        ·
          refine ⟨11978710939787335106646925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15971614586383113475529233 11978710939787335106646925)
          ·
            refine ⟨4492016602420250664992597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11978710939787335106646925 4492016602420250664992597)
            ·
              refine ⟨26320409779806156240191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4492016602420250664992597 26320409779806156240191)
              ·
                rfl

theorem cell23_4151964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 9].length) (baseStart_4151964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151964 prefixEnd_4151964 := by exact prefixLift 4151964
  have htrace : WordTrace (prefixWord ++ tailWord_4151964) baseStart_4151964 baseEnd_4151964 := by
    simpa [prefixWord, tailWord_4151964, baseEnd_4151964] using wordTrace_append hprefix tailTrace_4151964
  have hstable : (prefixWord ++ tailWord_4151964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151964).length < 2 ^ (prefixWord ++ tailWord_4151964).sum := by decide
  have hdescent : baseEnd_4151964 < baseStart_4151964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4151984 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 2, 7, 2]
def baseStart_4151984 : Nat := 118140960795 + 4151984 * 2 ^ 59
def prefixEnd_4151984 : Nat := 4983230072969 + 3 ^ 40 * 4151984 * 2
def baseEnd_4151984 : Nat := 2131963461777388577205379

theorem tailTrace_4151984 : CollatzResearch.WordTrace tailWord_4151984 prefixEnd_4151984 2131963461777388577205379 := by
  unfold tailWord_4151984
  simp only [CollatzResearch.WordTrace]
  refine ⟨75717648695039272628891503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100956864926719030171855337 75717648695039272628891503)
  ·
    refine ⟨113576473042558908943337255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75717648695039272628891503 113576473042558908943337255)
    ·
      refine ⟨170364709563838363415005883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113576473042558908943337255 170364709563838363415005883)
      ·
        refine ⟨255547064345757545122508825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170364709563838363415005883 255547064345757545122508825)
        ·
          refine ⟨191660298259318158841881619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255547064345757545122508825 191660298259318158841881619)
          ·
            refine ⟨287490447388977238262822429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191660298259318158841881619 287490447388977238262822429)
            ·
              refine ⟨107808917770866464348558411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287490447388977238262822429 107808917770866464348558411)
              ·
                refine ⟨161713376656299696522837617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107808917770866464348558411 161713376656299696522837617)
                ·
                  refine ⟨121285032492224772392128213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161713376656299696522837617 121285032492224772392128213)
                  ·
                    refine ⟨2842617949036518102940505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 121285032492224772392128213 2842617949036518102940505)
                    ·
                      refine ⟨2131963461777388577205379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842617949036518102940505 2131963461777388577205379)
                      ·
                        rfl

theorem cell23_4151984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 7, 2].length) (baseStart_4151984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4151984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4151984 prefixEnd_4151984 := by exact prefixLift 4151984
  have htrace : WordTrace (prefixWord ++ tailWord_4151984) baseStart_4151984 baseEnd_4151984 := by
    simpa [prefixWord, tailWord_4151984, baseEnd_4151984] using wordTrace_append hprefix tailTrace_4151984
  have hstable : (prefixWord ++ tailWord_4151984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4151984).length < 2 ^ (prefixWord ++ tailWord_4151984).sum := by decide
  have hdescent : baseEnd_4151984 < baseStart_4151984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4151984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152007 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 3, 8]
def baseStart_4152007 : Nat := 118140960795 + 4152007 * 2 ^ 59
def prefixEnd_4152007 : Nat := 4983230072969 + 3 ^ 40 * 4152007 * 2
def baseEnd_4152007 : Nat := 710658423944147329072591

theorem tailTrace_4152007 : CollatzResearch.WordTrace tailWord_4152007 prefixEnd_4152007 710658423944147329072591 := by
  unfold tailWord_4152007
  simp only [CollatzResearch.WordTrace]
  refine ⟨151436136268995220185870275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100957424179330146790580183 151436136268995220185870275)
  ·
    refine ⟨227154204403492830278805413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151436136268995220185870275 227154204403492830278805413)
    ·
      refine ⟨42591413325654905677276015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227154204403492830278805413 42591413325654905677276015)
      ·
        refine ⟨63887119988482358515914023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42591413325654905677276015 63887119988482358515914023)
        ·
          refine ⟨95830679982723537773871035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63887119988482358515914023 95830679982723537773871035)
          ·
            refine ⟨143746019974085306660806553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95830679982723537773871035 143746019974085306660806553)
            ·
              refine ⟨107809514980563979995604915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143746019974085306660806553 107809514980563979995604915)
              ·
                refine ⟨161714272470845969993407373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107809514980563979995604915 161714272470845969993407373)
                ·
                  refine ⟨60642852176567238747527765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161714272470845969993407373 60642852176567238747527765)
                  ·
                    refine ⟨710658423944147329072591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60642852176567238747527765 710658423944147329072591)
                    ·
                      rfl

theorem cell23_4152007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_4152007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152007 prefixEnd_4152007 := by exact prefixLift 4152007
  have htrace : WordTrace (prefixWord ++ tailWord_4152007) baseStart_4152007 baseEnd_4152007 := by
    simpa [prefixWord, tailWord_4152007, baseEnd_4152007] using wordTrace_append hprefix tailTrace_4152007
  have hstable : (prefixWord ++ tailWord_4152007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152007).length < 2 ^ (prefixWord ++ tailWord_4152007).sum := by decide
  have hdescent : baseEnd_4152007 < baseStart_4152007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152048 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 2, 2, 2]
def baseStart_4152048 : Nat := 118140960795 + 4152048 * 2 ^ 59
def prefixEnd_4152048 : Nat := 4983230072969 + 3 ^ 40 * 4152048 * 2
def baseEnd_4152048 : Nat := 2131996324539276326805085

theorem tailTrace_4152048 : CollatzResearch.WordTrace tailWord_4152048 prefixEnd_4152048 2131996324539276326805085 := by
  unfold tailWord_4152048
  simp only [CollatzResearch.WordTrace]
  refine ⟨75718815830923342094056399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100958421107897789458741865 75718815830923342094056399)
  ·
    refine ⟨113578223746385013141084599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75718815830923342094056399 113578223746385013141084599)
    ·
      refine ⟨170367335619577519711626899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113578223746385013141084599 170367335619577519711626899)
      ·
        refine ⟨255551003429366279567440349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170367335619577519711626899 255551003429366279567440349)
        ·
          refine ⟨95831626286012354837790131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255551003429366279567440349 95831626286012354837790131)
          ·
            refine ⟨143747439429018532256685197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95831626286012354837790131 143747439429018532256685197)
            ·
              refine ⟨53905289785881949596256949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143747439429018532256685197 53905289785881949596256949)
              ·
                refine ⟨5053620917426432774649089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53905289785881949596256949 5053620917426432774649089)
                ·
                  refine ⟨3790215688069824580986817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5053620917426432774649089 3790215688069824580986817)
                  ·
                    refine ⟨2842661766052368435740113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3790215688069824580986817 2842661766052368435740113)
                    ·
                      refine ⟨2131996324539276326805085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842661766052368435740113 2131996324539276326805085)
                      ·
                        rfl

theorem cell23_4152048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2, 2, 2].length) (baseStart_4152048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152048 prefixEnd_4152048 := by exact prefixLift 4152048
  have htrace : WordTrace (prefixWord ++ tailWord_4152048) baseStart_4152048 baseEnd_4152048 := by
    simpa [prefixWord, tailWord_4152048, baseEnd_4152048] using wordTrace_append hprefix tailTrace_4152048
  have hstable : (prefixWord ++ tailWord_4152048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152048).length < 2 ^ (prefixWord ++ tailWord_4152048).sum := by decide
  have hdescent : baseEnd_4152048 < baseStart_4152048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152064 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 3]
def baseStart_4152064 : Nat := 118140960795 + 4152064 * 2 ^ 59
def prefixEnd_4152064 : Nat := 4983230072969 + 3 ^ 40 * 4152064 * 2
def baseEnd_4152064 : Nat := 2132004540229748264205011

theorem tailTrace_4152064 : CollatzResearch.WordTrace tailWord_4152064 prefixEnd_4152064 2132004540229748264205011 := by
  unfold tailWord_4152064
  simp only [CollatzResearch.WordTrace]
  refine ⟨75719107614894359460347623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100958810153192479280463497 75719107614894359460347623)
  ·
    refine ⟨113578661422341539190521435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75719107614894359460347623 113578661422341539190521435)
    ·
      refine ⟨170367992133512308785782153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113578661422341539190521435 170367992133512308785782153)
      ·
        refine ⟨127775994100134231589336615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170367992133512308785782153 127775994100134231589336615)
        ·
          refine ⟨191663991150201347384004923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127775994100134231589336615 191663991150201347384004923)
          ·
            refine ⟨287495986725302021076007385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191663991150201347384004923 287495986725302021076007385)
            ·
              refine ⟨215621990043976515807005539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287495986725302021076007385 215621990043976515807005539)
              ·
                refine ⟨323432985065964773710508309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215621990043976515807005539 323432985065964773710508309)
                ·
                  refine ⟨15160921174967098767680077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 323432985065964773710508309 15160921174967098767680077)
                  ·
                    refine ⟨5685345440612662037880029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15160921174967098767680077 5685345440612662037880029)
                    ·
                      refine ⟨2132004540229748264205011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5685345440612662037880029 2132004540229748264205011)
                      ·
                        rfl

theorem cell23_4152064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_4152064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152064 prefixEnd_4152064 := by exact prefixLift 4152064
  have htrace : WordTrace (prefixWord ++ tailWord_4152064) baseStart_4152064 baseEnd_4152064 := by
    simpa [prefixWord, tailWord_4152064, baseEnd_4152064] using wordTrace_append hprefix tailTrace_4152064
  have hstable : (prefixWord ++ tailWord_4152064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152064).length < 2 ^ (prefixWord ++ tailWord_4152064).sum := by decide
  have hdescent : baseEnd_4152064 < baseStart_4152064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152082 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_4152082 : Nat := 118140960795 + 4152082 * 2 ^ 59
def prefixEnd_4152082 : Nat := 4983230072969 + 3 ^ 40 * 4152082 * 2
def baseEnd_4152082 : Nat := 2132013782881529193779929

theorem tailTrace_4152082 : CollatzResearch.WordTrace tailWord_4152082 prefixEnd_4152082 2132013782881529193779929 := by
  unfold tailWord_4152082
  simp only [CollatzResearch.WordTrace]
  refine ⟨37859717935930876998712625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100959247829149005329900333 37859717935930876998712625)
  ·
    refine ⟨28394788451948157749034469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37859717935930876998712625 28394788451948157749034469)
    ·
      refine ⟨5324022834740279577943963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28394788451948157749034469 5324022834740279577943963)
      ·
        refine ⟨7986034252110419366915945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5324022834740279577943963 7986034252110419366915945)
        ·
          refine ⟨5989525689082814525186959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7986034252110419366915945 5989525689082814525186959)
          ·
            refine ⟨8984288533624221787780439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989525689082814525186959 8984288533624221787780439)
            ·
              refine ⟨13476432800436332681670659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984288533624221787780439 13476432800436332681670659)
              ·
                refine ⟨20214649200654499022505989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13476432800436332681670659 20214649200654499022505989)
                ·
                  refine ⟨3790246725122718566719873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20214649200654499022505989 3790246725122718566719873)
                  ·
                    refine ⟨2842685043842038925039905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3790246725122718566719873 2842685043842038925039905)
                    ·
                      refine ⟨2132013782881529193779929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842685043842038925039905 2132013782881529193779929)
                      ·
                        rfl

theorem cell23_4152082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_4152082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152082 prefixEnd_4152082 := by exact prefixLift 4152082
  have htrace : WordTrace (prefixWord ++ tailWord_4152082) baseStart_4152082 baseEnd_4152082 := by
    simpa [prefixWord, tailWord_4152082, baseEnd_4152082] using wordTrace_append hprefix tailTrace_4152082
  have hstable : (prefixWord ++ tailWord_4152082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152082).length < 2 ^ (prefixWord ++ tailWord_4152082).sum := by decide
  have hdescent : baseEnd_4152082 < baseStart_4152082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152114 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_4152114 : Nat := 118140960795 + 4152114 * 2 ^ 59
def prefixEnd_4152114 : Nat := 4983230072969 + 3 ^ 40 * 4152114 * 2
def baseEnd_4152114 : Nat := 710676738087491022859927

theorem tailTrace_4152114 : CollatzResearch.WordTrace tailWord_4152114 prefixEnd_4152114 710676738087491022859927 := by
  unfold tailWord_4152114
  simp only [CollatzResearch.WordTrace]
  refine ⟨37860009719901894365003849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100960025919738384973343597 37860009719901894365003849)
  ·
    refine ⟨28395007289926420773752887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37860009719901894365003849 28395007289926420773752887)
    ·
      refine ⟨42592510934889631160629331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28395007289926420773752887 42592510934889631160629331)
      ·
        refine ⟨63888766402334446740943997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42592510934889631160629331 63888766402334446740943997)
        ·
          refine ⟨23958287400875417527853999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63888766402334446740943997 23958287400875417527853999)
          ·
            refine ⟨35937431101313126291780999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23958287400875417527853999 35937431101313126291780999)
            ·
              refine ⟨53906146651969689437671499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35937431101313126291780999 53906146651969689437671499)
              ·
                refine ⟨80859219977954534156507249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53906146651969689437671499 80859219977954534156507249)
                ·
                  refine ⟨60644414983465900617380437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80859219977954534156507249 60644414983465900617380437)
                  ·
                    refine ⟨710676738087491022859927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60644414983465900617380437 710676738087491022859927)
                    ·
                      rfl

theorem cell23_4152114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_4152114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152114 prefixEnd_4152114 := by exact prefixLift 4152114
  have htrace : WordTrace (prefixWord ++ tailWord_4152114) baseStart_4152114 baseEnd_4152114 := by
    simpa [prefixWord, tailWord_4152114, baseEnd_4152114] using wordTrace_append hprefix tailTrace_4152114
  have hstable : (prefixWord ++ tailWord_4152114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152114).length < 2 ^ (prefixWord ++ tailWord_4152114).sum := by decide
  have hdescent : baseEnd_4152114 < baseStart_4152114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152124 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_4152124 : Nat := 118140960795 + 4152124 * 2 ^ 59
def prefixEnd_4152124 : Nat := 4983230072969 + 3 ^ 40 * 4152124 * 2
def baseEnd_4152124 : Nat := 2132035349069018029454735

theorem tailTrace_4152124 : CollatzResearch.WordTrace tailWord_4152124 prefixEnd_4152124 2132035349069018029454735 := by
  unfold tailWord_4152124
  simp only [CollatzResearch.WordTrace]
  refine ⟨75720201804785674583939713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100960269073047566111919617 75720201804785674583939713)
  ·
    refine ⟨56790151353589255937954785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75720201804785674583939713 56790151353589255937954785)
    ·
      refine ⟨42592613515191941953466089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56790151353589255937954785 42592613515191941953466089)
      ·
        refine ⟨31944460136393956465099567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42592613515191941953466089 31944460136393956465099567)
        ·
          refine ⟨47916690204590934697649351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31944460136393956465099567 47916690204590934697649351)
          ·
            refine ⟨71875035306886402046474027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47916690204590934697649351 71875035306886402046474027)
            ·
              refine ⟨107812552960329603069711041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71875035306886402046474027 107812552960329603069711041)
              ·
                refine ⟨80859414720247202302283281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107812552960329603069711041 80859414720247202302283281)
                ·
                  refine ⟨60644561040185401726712461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80859414720247202302283281 60644561040185401726712461)
                  ·
                    refine ⟨22741710390069525647517173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60644561040185401726712461 22741710390069525647517173)
                    ·
                      refine ⟨2132035349069018029454735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22741710390069525647517173 2132035349069018029454735)
                      ·
                        rfl

theorem cell23_4152124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_4152124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152124 prefixEnd_4152124 := by exact prefixLift 4152124
  have htrace : WordTrace (prefixWord ++ tailWord_4152124) baseStart_4152124 baseEnd_4152124 := by
    simpa [prefixWord, tailWord_4152124, baseEnd_4152124] using wordTrace_append hprefix tailTrace_4152124
  have hstable : (prefixWord ++ tailWord_4152124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152124).length < 2 ^ (prefixWord ++ tailWord_4152124).sum := by decide
  have hdescent : baseEnd_4152124 < baseStart_4152124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152144 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 8]
def baseStart_4152144 : Nat := 118140960795 + 4152144 * 2 ^ 59
def prefixEnd_4152144 : Nat := 4983230072969 + 3 ^ 40 * 4152144 * 2
def baseEnd_4152144 : Nat := 236893957631345327911627

theorem tailTrace_4152144 : CollatzResearch.WordTrace tailWord_4152144 prefixEnd_4152144 236893957631345327911627 := by
  unfold tailWord_4152144
  simp only [CollatzResearch.WordTrace]
  refine ⟨75720566534749446291803743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100960755379665928389071657 75720566534749446291803743)
  ·
    refine ⟨113580849802124169437705615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75720566534749446291803743 113580849802124169437705615)
    ·
      refine ⟨170371274703186254156558423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113580849802124169437705615 170371274703186254156558423)
      ·
        refine ⟨255556912054779381234837635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170371274703186254156558423 255556912054779381234837635)
        ·
          refine ⟨383335368082169071852256453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255556912054779381234837635 383335368082169071852256453)
          ·
            refine ⟨71875381515406700972298085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383335368082169071852256453 71875381515406700972298085)
            ·
              refine ⟨13476634034138756432305891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71875381515406700972298085 13476634034138756432305891)
              ·
                refine ⟨20214951051208134648458837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13476634034138756432305891 20214951051208134648458837)
                ·
                  refine ⟨236893957631345327911627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20214951051208134648458837 236893957631345327911627)
                  ·
                    rfl

theorem cell23_4152144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 8].length) (baseStart_4152144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152144 prefixEnd_4152144 := by exact prefixLift 4152144
  have htrace : WordTrace (prefixWord ++ tailWord_4152144) baseStart_4152144 baseEnd_4152144 := by
    simpa [prefixWord, tailWord_4152144, baseEnd_4152144] using wordTrace_append hprefix tailTrace_4152144
  have hstable : (prefixWord ++ tailWord_4152144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152144).length < 2 ^ (prefixWord ++ tailWord_4152144).sum := by decide
  have hdescent : baseEnd_4152144 < baseStart_4152144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152184 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_4152184 : Nat := 118140960795 + 4152184 * 2 ^ 59
def prefixEnd_4152184 : Nat := 4983230072969 + 3 ^ 40 * 4152184 * 2
def baseEnd_4152184 : Nat := 2132066157908287794704459

theorem tailTrace_4152184 : CollatzResearch.WordTrace tailWord_4152184 prefixEnd_4152184 2132066157908287794704459 := by
  unfold tailWord_4152184
  simp only [CollatzResearch.WordTrace]
  refine ⟨75721295994676989707531803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100961727992902652943375737 75721295994676989707531803)
  ·
    refine ⟨113581943992015484561297705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75721295994676989707531803 113581943992015484561297705)
    ·
      refine ⟨85186457994011613420973279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113581943992015484561297705 85186457994011613420973279)
      ·
        refine ⟨127779686991017420131459919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85186457994011613420973279 127779686991017420131459919)
        ·
          refine ⟨191669530486526130197189879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127779686991017420131459919 191669530486526130197189879)
          ·
            refine ⟨287504295729789195295784819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191669530486526130197189879 287504295729789195295784819)
            ·
              refine ⟨431256443594683792943677229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287504295729789195295784819 431256443594683792943677229)
              ·
                refine ⟨161721166348006422353878961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431256443594683792943677229 161721166348006422353878961)
                ·
                  refine ⟨121290874761004816765409221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161721166348006422353878961 121290874761004816765409221)
                  ·
                    refine ⟨22742039017688403143514229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121290874761004816765409221 22742039017688403143514229)
                    ·
                      refine ⟨2132066157908287794704459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22742039017688403143514229 2132066157908287794704459)
                      ·
                        rfl

theorem cell23_4152184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_4152184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152184 prefixEnd_4152184 := by exact prefixLift 4152184
  have htrace : WordTrace (prefixWord ++ tailWord_4152184) baseStart_4152184 baseEnd_4152184 := by
    simpa [prefixWord, tailWord_4152184, baseEnd_4152184] using wordTrace_append hprefix tailTrace_4152184
  have hstable : (prefixWord ++ tailWord_4152184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152184).length < 2 ^ (prefixWord ++ tailWord_4152184).sum := by decide
  have hdescent : baseEnd_4152184 < baseStart_4152184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152191 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 1, 5]
def baseStart_4152191 : Nat := 118140960795 + 4152191 * 2 ^ 59
def prefixEnd_4152191 : Nat := 4983230072969 + 3 ^ 40 * 4152191 * 2
def baseEnd_4152191 : Nat := 710689917424289755772309

theorem tailTrace_4152191 : CollatzResearch.WordTrace tailWord_4152191 prefixEnd_4152191 710689917424289755772309 := by
  unfold tailWord_4152191
  simp only [CollatzResearch.WordTrace]
  refine ⟨151442847300328619610568427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100961898200219079740378951 151442847300328619610568427)
  ·
    refine ⟨227164270950492929415852641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151442847300328619610568427 227164270950492929415852641)
    ·
      refine ⟨170373203212869697061889481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227164270950492929415852641 170373203212869697061889481)
      ·
        refine ⟨127779902409652272796417111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170373203212869697061889481 127779902409652272796417111)
        ·
          refine ⟨191669853614478409194625667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127779902409652272796417111 191669853614478409194625667)
          ·
            refine ⟨287504780421717613791938501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191669853614478409194625667 287504780421717613791938501)
            ·
              refine ⟨53907146329072052585988469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287504780421717613791938501 53907146329072052585988469)
              ·
                refine ⟨5053794968350504929936419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53907146329072052585988469 5053794968350504929936419)
                ·
                  refine ⟨7580692452525757394904629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053794968350504929936419 7580692452525757394904629)
                  ·
                    refine ⟨710689917424289755772309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7580692452525757394904629 710689917424289755772309)
                    ·
                      rfl

theorem cell23_4152191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 5].length) (baseStart_4152191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152191 prefixEnd_4152191 := by exact prefixLift 4152191
  have htrace : WordTrace (prefixWord ++ tailWord_4152191) baseStart_4152191 baseEnd_4152191 := by
    simpa [prefixWord, tailWord_4152191, baseEnd_4152191] using wordTrace_append hprefix tailTrace_4152191
  have hstable : (prefixWord ++ tailWord_4152191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152191).length < 2 ^ (prefixWord ++ tailWord_4152191).sum := by decide
  have hdescent : baseEnd_4152191 < baseStart_4152191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152228 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_4152228 : Nat := 118140960795 + 4152228 * 2 ^ 59
def prefixEnd_4152228 : Nat := 4983230072969 + 3 ^ 40 * 4152228 * 2
def baseEnd_4152228 : Nat := 2132088751057085622554257

theorem tailTrace_4152228 : CollatzResearch.WordTrace tailWord_4152228 prefixEnd_4152228 2132088751057085622554257 := by
  unfold tailWord_4152228
  simp only [CollatzResearch.WordTrace]
  refine ⟨75722098400597287464832669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100962797867463049953110225 75722098400597287464832669)
  ·
    refine ⟨28395786900223982799312251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75722098400597287464832669 28395786900223982799312251)
    ·
      refine ⟨42593680350335974198968377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28395786900223982799312251 42593680350335974198968377)
      ·
        refine ⟨31945260262751980649226283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42593680350335974198968377 31945260262751980649226283)
        ·
          refine ⟨47917890394127970973839425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31945260262751980649226283 47917890394127970973839425)
          ·
            refine ⟨35938417795595978230379569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47917890394127970973839425 35938417795595978230379569)
            ·
              refine ⟨26953813346696983672784677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35938417795595978230379569 26953813346696983672784677)
              ·
                refine ⟨5053840002505684438647127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26953813346696983672784677 5053840002505684438647127)
                ·
                  refine ⟨7580760003758526657970691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053840002505684438647127 7580760003758526657970691)
                  ·
                    refine ⟨11371140005637789986956037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7580760003758526657970691 11371140005637789986956037)
                    ·
                      refine ⟨2132088751057085622554257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11371140005637789986956037 2132088751057085622554257)
                      ·
                        rfl

theorem cell23_4152228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_4152228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152228 prefixEnd_4152228 := by exact prefixLift 4152228
  have htrace : WordTrace (prefixWord ++ tailWord_4152228) baseStart_4152228 baseEnd_4152228 := by
    simpa [prefixWord, tailWord_4152228, baseEnd_4152228] using wordTrace_append hprefix tailTrace_4152228
  have hstable : (prefixWord ++ tailWord_4152228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152228).length < 2 ^ (prefixWord ++ tailWord_4152228).sum := by decide
  have hdescent : baseEnd_4152228 < baseStart_4152228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152245 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_4152245 : Nat := 118140960795 + 4152245 * 2 ^ 59
def prefixEnd_4152245 : Nat := 4983230072969 + 3 ^ 40 * 4152245 * 2
def baseEnd_4152245 : Nat := 2132097480228212056041679

theorem tailTrace_4152245 : CollatzResearch.WordTrace tailWord_4152245 prefixEnd_4152245 2132097480228212056041679 := by
  unfold tailWord_4152245
  simp only [CollatzResearch.WordTrace]
  refine ⟨151444816842132986833034189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100963211228088657888689459 151444816842132986833034189)
  ·
    refine ⟨56791806315799870062387821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151444816842132986833034189 56791806315799870062387821)
    ·
      refine ⟨21296927368424951273395433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56791806315799870062387821 21296927368424951273395433)
      ·
        refine ⟨15972695526318713455046575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21296927368424951273395433 15972695526318713455046575)
        ·
          refine ⟨23959043289478070182569863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15972695526318713455046575 23959043289478070182569863)
          ·
            refine ⟨35938564934217105273854795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23959043289478070182569863 35938564934217105273854795)
            ·
              refine ⟨53907847401325657910782193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35938564934217105273854795 53907847401325657910782193)
              ·
                refine ⟨40430885550994243433086645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53907847401325657910782193 40430885550994243433086645)
                ·
                  refine ⟨3790395520405710321851873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40430885550994243433086645 3790395520405710321851873)
                  ·
                    refine ⟨2842796640304282741388905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3790395520405710321851873 2842796640304282741388905)
                    ·
                      refine ⟨2132097480228212056041679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842796640304282741388905 2132097480228212056041679)
                      ·
                        rfl

theorem cell23_4152245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_4152245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152245 prefixEnd_4152245 := by exact prefixLift 4152245
  have htrace : WordTrace (prefixWord ++ tailWord_4152245) baseStart_4152245 baseEnd_4152245 := by
    simpa [prefixWord, tailWord_4152245, baseEnd_4152245] using wordTrace_append hprefix tailTrace_4152245
  have hstable : (prefixWord ++ tailWord_4152245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152245).length < 2 ^ (prefixWord ++ tailWord_4152245).sum := by decide
  have hdescent : baseEnd_4152245 < baseStart_4152245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152246 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_4152246 : Nat := 118140960795 + 4152246 * 2 ^ 59
def prefixEnd_4152246 : Nat := 4983230072969 + 3 ^ 40 * 4152246 * 2
def baseEnd_4152246 : Nat := 236899777078762950236575

theorem tailTrace_4152246 : CollatzResearch.WordTrace tailWord_4152246 prefixEnd_4152246 236899777078762950236575 := by
  unfold tailWord_4152246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9465303332195585250238787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100963235543419576002547061 9465303332195585250238787)
  ·
    refine ⟨14197954998293377875358181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9465303332195585250238787 14197954998293377875358181)
    ·
      refine ⟨2662116562180008351629659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14197954998293377875358181 2662116562180008351629659)
      ·
        refine ⟨3993174843270012527444489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662116562180008351629659 3993174843270012527444489)
        ·
          refine ⟨2994881132452509395583367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3993174843270012527444489 2994881132452509395583367)
          ·
            refine ⟨4492321698678764093375051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994881132452509395583367 4492321698678764093375051)
            ·
              refine ⟨6738482548018146140062577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492321698678764093375051 6738482548018146140062577)
              ·
                refine ⟨5053861911013609605046933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6738482548018146140062577 5053861911013609605046933)
                ·
                  refine ⟨236899777078762950236575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5053861911013609605046933 236899777078762950236575)
                  ·
                    rfl

theorem cell23_4152246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_4152246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152246 prefixEnd_4152246 := by exact prefixLift 4152246
  have htrace : WordTrace (prefixWord ++ tailWord_4152246) baseStart_4152246 baseEnd_4152246 := by
    simpa [prefixWord, tailWord_4152246, baseEnd_4152246] using wordTrace_append hprefix tailTrace_4152246
  have hstable : (prefixWord ++ tailWord_4152246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152246).length < 2 ^ (prefixWord ++ tailWord_4152246).sum := by decide
  have hdescent : baseEnd_4152246 < baseStart_4152246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152285 : List Nat := [1, 4, 3, 1, 2, 3, 2, 7]
def baseStart_4152285 : Nat := 118140960795 + 4152285 * 2 ^ 59
def prefixEnd_4152285 : Nat := 4983230072969 + 3 ^ 40 * 4152285 * 2
def baseEnd_4152285 : Nat := 78967334053866366649685

theorem tailTrace_4152285 : CollatzResearch.WordTrace tailWord_4152285 prefixEnd_4152285 78967334053866366649685 := by
  unfold tailWord_4152285
  simp only [CollatzResearch.WordTrace]
  refine ⟨151446275761988073664490309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100964183841325382442993539 151446275761988073664490309)
  ·
    refine ⟨28396176705372763812091933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151446275761988073664490309 28396176705372763812091933)
    ·
      refine ⟨10648566264514786429534475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28396176705372763812091933 10648566264514786429534475)
      ·
        refine ⟨15972849396772179644301713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10648566264514786429534475 15972849396772179644301713)
        ·
          refine ⟨11979637047579134733226285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15972849396772179644301713 11979637047579134733226285)
          ·
            refine ⟨4492363892842175524959857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11979637047579134733226285 4492363892842175524959857)
            ·
              refine ⟨3369272919631631643719893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4492363892842175524959857 3369272919631631643719893)
              ·
                refine ⟨78967334053866366649685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3369272919631631643719893 78967334053866366649685)
                ·
                  rfl

theorem cell23_4152285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 7].length) (baseStart_4152285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152285 prefixEnd_4152285 := by exact prefixLift 4152285
  have htrace : WordTrace (prefixWord ++ tailWord_4152285) baseStart_4152285 baseEnd_4152285 := by
    simpa [prefixWord, tailWord_4152285, baseEnd_4152285] using wordTrace_append hprefix tailTrace_4152285
  have hstable : (prefixWord ++ tailWord_4152285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152285).length < 2 ^ (prefixWord ++ tailWord_4152285).sum := by decide
  have hdescent : baseEnd_4152285 < baseStart_4152285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152291 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4152291 : Nat := 118140960795 + 4152291 * 2 ^ 59
def prefixEnd_4152291 : Nat := 4983230072969 + 3 ^ 40 * 4152291 * 2
def baseEnd_4152291 : Nat := 2132121100338318876066467

theorem tailTrace_4152291 : CollatzResearch.WordTrace tailWord_4152291 prefixEnd_4152291 2132121100338318876066467 := by
  unfold tailWord_4152291
  simp only [CollatzResearch.WordTrace]
  refine ⟨151446494599966336689208727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100964329733310891126139151 151446494599966336689208727)
  ·
    refine ⟨227169741899949505033813091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151446494599966336689208727 227169741899949505033813091)
    ·
      refine ⟨340754612849924257550719637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227169741899949505033813091 340754612849924257550719637)
      ·
        refine ⟨15972872477340199572689983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 340754612849924257550719637 15972872477340199572689983)
        ·
          refine ⟨23959308716010299359034975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15972872477340199572689983 23959308716010299359034975)
          ·
            refine ⟨35938963074015449038552463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23959308716010299359034975 35938963074015449038552463)
            ·
              refine ⟨53908444611023173557828695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35938963074015449038552463 53908444611023173557828695)
              ·
                refine ⟨80862666916534760336743043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53908444611023173557828695 80862666916534760336743043)
                ·
                  refine ⟨121294000374802140505114565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80862666916534760336743043 121294000374802140505114565)
                  ·
                    refine ⟨22742625070275401344708981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121294000374802140505114565 22742625070275401344708981)
                    ·
                      refine ⟨2132121100338318876066467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22742625070275401344708981 2132121100338318876066467)
                      ·
                        rfl

theorem cell23_4152291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4152291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152291 prefixEnd_4152291 := by exact prefixLift 4152291
  have htrace : WordTrace (prefixWord ++ tailWord_4152291) baseStart_4152291 baseEnd_4152291 := by
    simpa [prefixWord, tailWord_4152291, baseEnd_4152291] using wordTrace_append hprefix tailTrace_4152291
  have hstable : (prefixWord ++ tailWord_4152291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152291).length < 2 ^ (prefixWord ++ tailWord_4152291).sum := by decide
  have hdescent : baseEnd_4152291 < baseStart_4152291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152295 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_4152295 : Nat := 118140960795 + 4152295 * 2 ^ 59
def prefixEnd_4152295 : Nat := 4983230072969 + 3 ^ 40 * 4152295 * 2
def baseEnd_4152295 : Nat := 2132123154260936860416449

theorem tailTrace_4152295 : CollatzResearch.WordTrace tailWord_4152295 prefixEnd_4152295 2132123154260936860416449 := by
  unfold tailWord_4152295
  simp only [CollatzResearch.WordTrace]
  refine ⟨151446640491951845372354339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100964426994634563581569559 151446640491951845372354339)
  ·
    refine ⟨227169960737927768058531509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151446640491951845372354339 227169960737927768058531509)
    ·
      refine ⟨21297183819180728255487329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227169960737927768058531509 21297183819180728255487329)
      ·
        refine ⟨15972887864385546191615497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21297183819180728255487329 15972887864385546191615497)
        ·
          refine ⟨11979665898289159643711623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15972887864385546191615497 11979665898289159643711623)
          ·
            refine ⟨17969498847433739465567435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11979665898289159643711623 17969498847433739465567435)
            ·
              refine ⟨26954248271150609198351153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17969498847433739465567435 26954248271150609198351153)
              ·
                refine ⟨20215686203362956898763365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26954248271150609198351153 20215686203362956898763365)
                ·
                  refine ⟨3790441163130554418518131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20215686203362956898763365 3790441163130554418518131)
                  ·
                    refine ⟨5685661744695831627777197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3790441163130554418518131 5685661744695831627777197)
                    ·
                      refine ⟨2132123154260936860416449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5685661744695831627777197 2132123154260936860416449)
                      ·
                        rfl

theorem cell23_4152295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_4152295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152295 prefixEnd_4152295 := by exact prefixLift 4152295
  have htrace : WordTrace (prefixWord ++ tailWord_4152295) baseStart_4152295 baseEnd_4152295 := by
    simpa [prefixWord, tailWord_4152295, baseEnd_4152295] using wordTrace_append hprefix tailTrace_4152295
  have hstable : (prefixWord ++ tailWord_4152295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152295).length < 2 ^ (prefixWord ++ tailWord_4152295).sum := by decide
  have hdescent : baseEnd_4152295 < baseStart_4152295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152368 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 3]
def baseStart_4152368 : Nat := 118140960795 + 4152368 * 2 ^ 59
def prefixEnd_4152368 : Nat := 4983230072969 + 3 ^ 40 * 4152368 * 2
def baseEnd_4152368 : Nat := 2132160638348715074803613

theorem tailTrace_4152368 : CollatzResearch.WordTrace tailWord_4152368 prefixEnd_4152368 2132160638348715074803613 := by
  unfold tailWord_4152368
  simp only [CollatzResearch.WordTrace]
  refine ⟨75724651510343689419880879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100966202013791585893174505 75724651510343689419880879)
  ·
    refine ⟨113586977265515534129821319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75724651510343689419880879 113586977265515534129821319)
    ·
      refine ⟨170380465898273301194731979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113586977265515534129821319 170380465898273301194731979)
      ·
        refine ⟨255570698847409951792097969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170380465898273301194731979 255570698847409951792097969)
        ·
          refine ⟨191678024135557463844073477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255570698847409951792097969 191678024135557463844073477)
          ·
            refine ⟨35939629525417024470763777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191678024135557463844073477 35939629525417024470763777)
            ·
              refine ⟨26954722144062768353072833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35939629525417024470763777 26954722144062768353072833)
              ·
                refine ⟨20216041608047076264804625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26954722144062768353072833 20216041608047076264804625)
                ·
                  refine ⟨15162031206035307198603469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20216041608047076264804625 15162031206035307198603469)
                  ·
                    refine ⟨5685761702263240199476301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15162031206035307198603469 5685761702263240199476301)
                    ·
                      refine ⟨2132160638348715074803613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5685761702263240199476301 2132160638348715074803613)
                      ·
                        rfl

theorem cell23_4152368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 3].length) (baseStart_4152368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152368 prefixEnd_4152368 := by exact prefixLift 4152368
  have htrace : WordTrace (prefixWord ++ tailWord_4152368) baseStart_4152368 baseEnd_4152368 := by
    simpa [prefixWord, tailWord_4152368, baseEnd_4152368] using wordTrace_append hprefix tailTrace_4152368
  have hstable : (prefixWord ++ tailWord_4152368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152368).length < 2 ^ (prefixWord ++ tailWord_4152368).sum := by decide
  have hdescent : baseEnd_4152368 < baseStart_4152368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152371 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 3, 7]
def baseStart_4152371 : Nat := 118140960795 + 4152371 * 2 ^ 59
def prefixEnd_4152371 : Nat := 4983230072969 + 3 ^ 40 * 4152371 * 2
def baseEnd_4152371 : Nat := 710720726263559521022033

theorem tailTrace_4152371 : CollatzResearch.WordTrace tailWord_4152371 prefixEnd_4152371 710720726263559521022033 := by
  unfold tailWord_4152371
  simp only [CollatzResearch.WordTrace]
  refine ⟨151449412439676510352120967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100966274959784340234747311 151449412439676510352120967)
  ·
    refine ⟨227174118659514765528181451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151449412439676510352120967 227174118659514765528181451)
    ·
      refine ⟨340761177989272148292272177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227174118659514765528181451 340761177989272148292272177)
      ·
        refine ⟨255570883491954111219204133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340761177989272148292272177 255570883491954111219204133)
        ·
          refine ⟨47919540654741395853600775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255570883491954111219204133 47919540654741395853600775)
          ·
            refine ⟨71879310982112093780401163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47919540654741395853600775 71879310982112093780401163)
            ·
              refine ⟨107818966473168140670601745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71879310982112093780401163 107818966473168140670601745)
              ·
                refine ⟨80864224854876105502951309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107818966473168140670601745 80864224854876105502951309)
                ·
                  refine ⟨30324084320578539563606741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80864224854876105502951309 30324084320578539563606741)
                  ·
                    refine ⟨710720726263559521022033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30324084320578539563606741 710720726263559521022033)
                    ·
                      rfl

theorem cell23_4152371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 7].length) (baseStart_4152371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152371 prefixEnd_4152371 := by exact prefixLift 4152371
  have htrace : WordTrace (prefixWord ++ tailWord_4152371) baseStart_4152371 baseEnd_4152371 := by
    simpa [prefixWord, tailWord_4152371, baseEnd_4152371] using wordTrace_append hprefix tailTrace_4152371
  have hstable : (prefixWord ++ tailWord_4152371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152371).length < 2 ^ (prefixWord ++ tailWord_4152371).sum := by decide
  have hdescent : baseEnd_4152371 < baseStart_4152371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152408 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_4152408 : Nat := 118140960795 + 4152408 * 2 ^ 59
def prefixEnd_4152408 : Nat := 4983230072969 + 3 ^ 40 * 4152408 * 2
def baseEnd_4152408 : Nat := 2132181177574894918303429

theorem tailTrace_4152408 : CollatzResearch.WordTrace tailWord_4152408 prefixEnd_4152408 2132181177574894918303429 := by
  unfold tailWord_4152408
  simp only [CollatzResearch.WordTrace]
  refine ⟨75725380970271232835608939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100967174627028310447478585 75725380970271232835608939)
  ·
    refine ⟨113588071455406849253413409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75725380970271232835608939 113588071455406849253413409)
    ·
      refine ⟨85191053591555136940060057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113588071455406849253413409 85191053591555136940060057)
      ·
        refine ⟨63893290193666352705045043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85191053591555136940060057 63893290193666352705045043)
        ·
          refine ⟨95839935290499529057567565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63893290193666352705045043 95839935290499529057567565)
          ·
            refine ⟨35939975733937323396587837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95839935290499529057567565 35939975733937323396587837)
            ·
              refine ⟨13477490900226496273720439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35939975733937323396587837 13477490900226496273720439)
              ·
                refine ⟨20216236350339744410580659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13477490900226496273720439 20216236350339744410580659)
                ·
                  refine ⟨30324354525509616615870989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20216236350339744410580659 30324354525509616615870989)
                  ·
                    refine ⟨11371632947066106230951621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30324354525509616615870989 11371632947066106230951621)
                    ·
                      refine ⟨2132181177574894918303429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11371632947066106230951621 2132181177574894918303429)
                      ·
                        rfl

theorem cell23_4152408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_4152408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152408 prefixEnd_4152408 := by exact prefixLift 4152408
  have htrace : WordTrace (prefixWord ++ tailWord_4152408) baseStart_4152408 baseEnd_4152408 := by
    simpa [prefixWord, tailWord_4152408, baseEnd_4152408] using wordTrace_append hprefix tailTrace_4152408
  have hstable : (prefixWord ++ tailWord_4152408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152408).length < 2 ^ (prefixWord ++ tailWord_4152408).sum := by decide
  have hdescent : baseEnd_4152408 < baseStart_4152408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152425 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 2, 4, 2]
def baseStart_4152425 : Nat := 118140960795 + 4152425 * 2 ^ 59
def prefixEnd_4152425 : Nat := 4983230072969 + 3 ^ 40 * 4152425 * 2
def baseEnd_4152425 : Nat := 2132189906746021351790851

theorem tailTrace_4152425 : CollatzResearch.WordTrace tailWord_4152425 prefixEnd_4152425 2132189906746021351790851 := by
  unfold tailWord_4152425
  simp only [CollatzResearch.WordTrace]
  refine ⟨151451381981480877574586729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100967587987653918383057819 151451381981480877574586729)
  ·
    refine ⟨113588536486110658180940047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151451381981480877574586729 113588536486110658180940047)
    ·
      refine ⟨170382804729165987271410071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113588536486110658180940047 170382804729165987271410071)
      ·
        refine ⟨255574207093748980907115107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170382804729165987271410071 255574207093748980907115107)
        ·
          refine ⟨383361310640623471360672661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255574207093748980907115107 383361310640623471360672661)
          ·
            refine ⟨17970061436279225220031531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 383361310640623471360672661 17970061436279225220031531)
            ·
              refine ⟨26955092154418837830047297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17970061436279225220031531 26955092154418837830047297)
              ·
                refine ⟨20216319115814128372535473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26955092154418837830047297 20216319115814128372535473)
                ·
                  refine ⟨15162239336860596279401605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20216319115814128372535473 15162239336860596279401605)
                  ·
                    refine ⟨2842919875661361802387801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15162239336860596279401605 2842919875661361802387801)
                    ·
                      refine ⟨2132189906746021351790851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2842919875661361802387801 2132189906746021351790851)
                      ·
                        rfl

theorem cell23_4152425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 4, 2].length) (baseStart_4152425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152425 prefixEnd_4152425 := by exact prefixLift 4152425
  have htrace : WordTrace (prefixWord ++ tailWord_4152425) baseStart_4152425 baseEnd_4152425 := by
    simpa [prefixWord, tailWord_4152425, baseEnd_4152425] using wordTrace_append hprefix tailTrace_4152425
  have hstable : (prefixWord ++ tailWord_4152425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152425).length < 2 ^ (prefixWord ++ tailWord_4152425).sum := by decide
  have hdescent : baseEnd_4152425 < baseStart_4152425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152448 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 6]
def baseStart_4152448 : Nat := 118140960795 + 4152448 * 2 ^ 59
def prefixEnd_4152448 : Nat := 4983230072969 + 3 ^ 40 * 4152448 * 2
def baseEnd_4152448 : Nat := 236911301866786084644805

theorem tailTrace_4152448 : CollatzResearch.WordTrace tailWord_4152448 prefixEnd_4152448 236911301866786084644805 := by
  unfold tailWord_4152448
  simp only [CollatzResearch.WordTrace]
  refine ⟨75726110430198776251336999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100968147240265035001782665 75726110430198776251336999)
  ·
    refine ⟨113589165645298164377005499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75726110430198776251336999 113589165645298164377005499)
    ·
      refine ⟨170383748467947246565508249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113589165645298164377005499 170383748467947246565508249)
      ·
        refine ⟨127787811350960434924131187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170383748467947246565508249 127787811350960434924131187)
        ·
          refine ⟨191681717026440652386196781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127787811350960434924131187 191681717026440652386196781)
          ·
            refine ⟨71880643884915244644823793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191681717026440652386196781 71880643884915244644823793)
            ·
              refine ⟨53910482913686433483617845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71880643884915244644823793 53910482913686433483617845)
              ·
                refine ⟨5054107773158103139089173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53910482913686433483617845 5054107773158103139089173)
                ·
                  refine ⟨236911301866786084644805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5054107773158103139089173 236911301866786084644805)
                  ·
                    rfl

theorem cell23_4152448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 6].length) (baseStart_4152448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152448 prefixEnd_4152448 := by exact prefixLift 4152448
  have htrace : WordTrace (prefixWord ++ tailWord_4152448) baseStart_4152448 baseEnd_4152448 := by
    simpa [prefixWord, tailWord_4152448, baseEnd_4152448] using wordTrace_append hprefix tailTrace_4152448
  have hstable : (prefixWord ++ tailWord_4152448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152448).length < 2 ^ (prefixWord ++ tailWord_4152448).sum := by decide
  have hdescent : baseEnd_4152448 < baseStart_4152448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152515 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 4]
def baseStart_4152515 : Nat := 118140960795 + 4152515 * 2 ^ 59
def prefixEnd_4152515 : Nat := 4983230072969 + 3 ^ 40 * 4152515 * 2
def baseEnd_4152515 : Nat := 2132236120004925999665437

theorem tailTrace_4152515 : CollatzResearch.WordTrace tailWord_4152515 prefixEnd_4152515 2132236120004925999665437 := by
  unfold tailWord_4152515
  simp only [CollatzResearch.WordTrace]
  refine ⟨151454664551154822945362999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100969776367436548630241999 151454664551154822945362999)
  ·
    refine ⟨227181996826732234418044499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151454664551154822945362999 227181996826732234418044499)
    ·
      refine ⟨340772995240098351627066749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227181996826732234418044499 340772995240098351627066749)
      ·
        refine ⟨127789873215036881860150031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340772995240098351627066749 127789873215036881860150031)
        ·
          refine ⟨191684809822555322790225047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127789873215036881860150031 191684809822555322790225047)
          ·
            refine ⟨287527214733832984185337571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191684809822555322790225047 287527214733832984185337571)
            ·
              refine ⟨431290822100749476278006357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287527214733832984185337571 431290822100749476278006357)
              ·
                refine ⟨5054189321493157925132887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 431290822100749476278006357 5054189321493157925132887)
                ·
                  refine ⟨7581283982239736887699331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054189321493157925132887 7581283982239736887699331)
                  ·
                    refine ⟨11371925973359605331548997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7581283982239736887699331 11371925973359605331548997)
                    ·
                      refine ⟨2132236120004925999665437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11371925973359605331548997 2132236120004925999665437)
                      ·
                        rfl

theorem cell23_4152515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_4152515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152515 prefixEnd_4152515 := by exact prefixLift 4152515
  have htrace : WordTrace (prefixWord ++ tailWord_4152515) baseStart_4152515 baseEnd_4152515 := by
    simpa [prefixWord, tailWord_4152515, baseEnd_4152515] using wordTrace_append hprefix tailTrace_4152515
  have hstable : (prefixWord ++ tailWord_4152515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152515).length < 2 ^ (prefixWord ++ tailWord_4152515).sum := by decide
  have hdescent : baseEnd_4152515 < baseStart_4152515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152535 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 5]
def baseStart_4152535 : Nat := 118140960795 + 4152535 * 2 ^ 59
def prefixEnd_4152535 : Nat := 4983230072969 + 3 ^ 40 * 4152535 * 2
def baseEnd_4152535 : Nat := 2132246389618015921415345

theorem tailTrace_4152535 : CollatzResearch.WordTrace tailWord_4152535 prefixEnd_4152535 2132246389618015921415345 := by
  unfold tailWord_4152535
  simp only [CollatzResearch.WordTrace]
  refine ⟨151455394011082366361091059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100970262674054910907394039 151455394011082366361091059)
  ·
    refine ⟨227183091016623549541636589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151455394011082366361091059 227183091016623549541636589)
    ·
      refine ⟨85193659131233831078113721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227183091016623549541636589 85193659131233831078113721)
      ·
        refine ⟨63895244348425373308585291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85193659131233831078113721 63895244348425373308585291)
        ·
          refine ⟨95842866522638059962877937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63895244348425373308585291 95842866522638059962877937)
          ·
            refine ⟨71882149891978544972158453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95842866522638059962877937 71882149891978544972158453)
            ·
              refine ⟨6738951552372988591139855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71882149891978544972158453 6738951552372988591139855)
              ·
                refine ⟨10108427328559482886709783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6738951552372988591139855 10108427328559482886709783)
                ·
                  refine ⟨15162640992839224330064675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10108427328559482886709783 15162640992839224330064675)
                  ·
                    refine ⟨22743961489258836495097013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15162640992839224330064675 22743961489258836495097013)
                    ·
                      refine ⟨2132246389618015921415345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22743961489258836495097013 2132246389618015921415345)
                      ·
                        rfl

theorem cell23_4152535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_4152535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152535 prefixEnd_4152535 := by exact prefixLift 4152535
  have htrace : WordTrace (prefixWord ++ tailWord_4152535) baseStart_4152535 baseEnd_4152535 := by
    simpa [prefixWord, tailWord_4152535, baseEnd_4152535] using wordTrace_append hprefix tailTrace_4152535
  have hstable : (prefixWord ++ tailWord_4152535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152535).length < 2 ^ (prefixWord ++ tailWord_4152535).sum := by decide
  have hdescent : baseEnd_4152535 < baseStart_4152535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152555 : List Nat := [1, 1, 1, 1, 2, 8, 1, 8]
def baseStart_4152555 : Nat := 118140960795 + 4152555 * 2 ^ 59
def prefixEnd_4152555 : Nat := 4983230072969 + 3 ^ 40 * 4152555 * 2
def baseEnd_4152555 : Nat := 78972468860411327524639

theorem tailTrace_4152555 : CollatzResearch.WordTrace tailWord_4152555 prefixEnd_4152555 78972468860411327524639 := by
  unfold tailWord_4152555
  simp only [CollatzResearch.WordTrace]
  refine ⟨151456123471009909776819119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100970748980673273184546079 151456123471009909776819119)
  ·
    refine ⟨227184185206514864665228679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151456123471009909776819119 227184185206514864665228679)
    ·
      refine ⟨340776277809772296997843019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227184185206514864665228679 340776277809772296997843019)
      ·
        refine ⟨511164416714658445496764529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340776277809772296997843019 511164416714658445496764529)
        ·
          refine ⟨383373312535993834122573397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511164416714658445496764529 383373312535993834122573397)
          ·
            refine ⟨4492656006281177743623907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 383373312535993834122573397 4492656006281177743623907)
            ·
              refine ⟨6738984009421766615435861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492656006281177743623907 6738984009421766615435861)
              ·
                refine ⟨78972468860411327524639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6738984009421766615435861 78972468860411327524639)
                ·
                  rfl

theorem cell23_4152555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 8].length) (baseStart_4152555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152555 prefixEnd_4152555 := by exact prefixLift 4152555
  have htrace : WordTrace (prefixWord ++ tailWord_4152555) baseStart_4152555 baseEnd_4152555 := by
    simpa [prefixWord, tailWord_4152555, baseEnd_4152555] using wordTrace_append hprefix tailTrace_4152555
  have hstable : (prefixWord ++ tailWord_4152555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152555).length < 2 ^ (prefixWord ++ tailWord_4152555).sum := by decide
  have hdescent : baseEnd_4152555 < baseStart_4152555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152572 : List Nat := [2, 2, 2, 1, 5, 1, 3, 7]
def baseStart_4152572 : Nat := 118140960795 + 4152572 * 2 ^ 59
def prefixEnd_4152572 : Nat := 4983230072969 + 3 ^ 40 * 4152572 * 2
def baseEnd_4152572 : Nat := 78972792163045639876025

theorem tailTrace_4152572 : CollatzResearch.WordTrace tailWord_4152572 prefixEnd_4152572 78972792163045639876025 := by
  unfold tailWord_4152572
  simp only [CollatzResearch.WordTrace]
  refine ⟨75728371755974160840093985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100971162341298881120125313 75728371755974160840093985)
  ·
    refine ⟨56796278816980620630070489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75728371755974160840093985 56796278816980620630070489)
    ·
      refine ⟨42597209112735465472552867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56796278816980620630070489 42597209112735465472552867)
      ·
        refine ⟨63895813669103198208829301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42597209112735465472552867 63895813669103198208829301)
        ·
          refine ⟨5990232531478424832077747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63895813669103198208829301 5990232531478424832077747)
          ·
            refine ⟨8985348797217637248116621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5990232531478424832077747 8985348797217637248116621)
            ·
              refine ⟨3369505798956613968043733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8985348797217637248116621 3369505798956613968043733)
              ·
                refine ⟨78972792163045639876025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3369505798956613968043733 78972792163045639876025)
                ·
                  rfl

theorem cell23_4152572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 7].length) (baseStart_4152572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152572 prefixEnd_4152572 := by exact prefixLift 4152572
  have htrace : WordTrace (prefixWord ++ tailWord_4152572) baseStart_4152572 baseEnd_4152572 := by
    simpa [prefixWord, tailWord_4152572, baseEnd_4152572] using wordTrace_append hprefix tailTrace_4152572
  have hstable : (prefixWord ++ tailWord_4152572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152572).length < 2 ^ (prefixWord ++ tailWord_4152572).sum := by decide
  have hdescent : baseEnd_4152572 < baseStart_4152572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152626 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2]
def baseStart_4152626 : Nat := 118140960795 + 4152626 * 2 ^ 59
def prefixEnd_4152626 : Nat := 4983230072969 + 3 ^ 40 * 4152626 * 2
def baseEnd_4152626 : Nat := 2132293116357575065377427

theorem tailTrace_4152626 : CollatzResearch.WordTrace tailWord_4152626 prefixEnd_4152626 2132293116357575065377427 := by
  unfold tailWord_4152626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37864678263438172225663433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100972475369168459268435821 37864678263438172225663433)
  ·
    refine ⟨28398508697578629169247575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37864678263438172225663433 28398508697578629169247575)
    ·
      refine ⟨42597763046367943753871363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28398508697578629169247575 42597763046367943753871363)
      ·
        refine ⟨63896644569551915630807045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42597763046367943753871363 63896644569551915630807045)
        ·
          refine ⟨11980620856790984180776321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63896644569551915630807045 11980620856790984180776321)
          ·
            refine ⟨8985465642593238135582241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11980620856790984180776321 8985465642593238135582241)
            ·
              refine ⟨6739099231944928601686681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8985465642593238135582241 6739099231944928601686681)
              ·
                refine ⟨5054324423958696451265011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6739099231944928601686681 5054324423958696451265011)
                ·
                  refine ⟨7581486635938044676897517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054324423958696451265011 7581486635938044676897517)
                  ·
                    refine ⟨2843057488476766753836569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7581486635938044676897517 2843057488476766753836569)
                    ·
                      refine ⟨2132293116357575065377427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843057488476766753836569 2132293116357575065377427)
                      ·
                        rfl

theorem cell23_4152626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_4152626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152626 prefixEnd_4152626 := by exact prefixLift 4152626
  have htrace : WordTrace (prefixWord ++ tailWord_4152626) baseStart_4152626 baseEnd_4152626 := by
    simpa [prefixWord, tailWord_4152626, baseEnd_4152626] using wordTrace_append hprefix tailTrace_4152626
  have hstable : (prefixWord ++ tailWord_4152626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152626).length < 2 ^ (prefixWord ++ tailWord_4152626).sum := by decide
  have hdescent : baseEnd_4152626 < baseStart_4152626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152639 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 4, 2, 2]
def baseStart_4152639 : Nat := 118140960795 + 4152639 * 2 ^ 59
def prefixEnd_4152639 : Nat := 4983230072969 + 3 ^ 40 * 4152639 * 2
def baseEnd_4152639 : Nat := 2132299791606083514514867

theorem tailTrace_4152639 : CollatzResearch.WordTrace tailWord_4152639 prefixEnd_4152639 2132299791606083514514867 := by
  unfold tailWord_4152639
  simp only [CollatzResearch.WordTrace]
  refine ⟨151459187202705592122876971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100972791468470394748584647 151459187202705592122876971)
  ·
    refine ⟨227188780804058388184315457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151459187202705592122876971 227188780804058388184315457)
    ·
      refine ⟨170391585603043791138236593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227188780804058388184315457 170391585603043791138236593)
      ·
        refine ⟨127793689202282843353677445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170391585603043791138236593 127793689202282843353677445)
        ·
          refine ⟨23961316725428033128814521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127793689202282843353677445 23961316725428033128814521)
          ·
            refine ⟨17970987544071024846610891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23961316725428033128814521 17970987544071024846610891)
            ·
              refine ⟨26956481316106537269916337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17970987544071024846610891 26956481316106537269916337)
              ·
                refine ⟨20217360987079902952437253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26956481316106537269916337 20217360987079902952437253)
                ·
                  refine ⟨3790755185077481803581985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20217360987079902952437253 3790755185077481803581985)
                  ·
                    refine ⟨2843066388808111352686489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3790755185077481803581985 2843066388808111352686489)
                    ·
                      refine ⟨2132299791606083514514867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843066388808111352686489 2132299791606083514514867)
                      ·
                        rfl

theorem cell23_4152639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_4152639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152639 prefixEnd_4152639 := by exact prefixLift 4152639
  have htrace : WordTrace (prefixWord ++ tailWord_4152639) baseStart_4152639 baseEnd_4152639 := by
    simpa [prefixWord, tailWord_4152639, baseEnd_4152639] using wordTrace_append hprefix tailTrace_4152639
  have hstable : (prefixWord ++ tailWord_4152639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152639).length < 2 ^ (prefixWord ++ tailWord_4152639).sum := by decide
  have hdescent : baseEnd_4152639 < baseStart_4152639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152713 : List Nat := [1, 2, 1, 1, 8, 1, 2, 2, 5]
def baseStart_4152713 : Nat := 118140960795 + 4152713 * 2 ^ 59
def prefixEnd_4152713 : Nat := 4983230072969 + 3 ^ 40 * 4152713 * 2
def baseEnd_4152713 : Nat := 236926421019390691665503

theorem tailTrace_4152713 : CollatzResearch.WordTrace tailWord_4152713 prefixEnd_4152713 236926421019390691665503 := by
  unfold tailWord_4152713
  simp only [CollatzResearch.WordTrace]
  refine ⟨151461886204437502761070793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100974590802958335174047195 151461886204437502761070793)
  ·
    refine ⟨113596414653328127070803095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151461886204437502761070793 113596414653328127070803095)
    ·
      refine ⟨170394621979992190606204643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113596414653328127070803095 170394621979992190606204643)
      ·
        refine ⟨255591932969988285909306965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170394621979992190606204643 255591932969988285909306965)
        ·
          refine ⟨2995217964492050225499691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 255591932969988285909306965 2995217964492050225499691)
          ·
            refine ⟨4492826946738075338249537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995217964492050225499691 4492826946738075338249537)
            ·
              refine ⟨3369620210053556503687153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4492826946738075338249537 3369620210053556503687153)
              ·
                refine ⟨2527215157540167377765365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3369620210053556503687153 2527215157540167377765365)
                ·
                  refine ⟨236926421019390691665503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2527215157540167377765365 236926421019390691665503)
                  ·
                    rfl

theorem cell23_4152713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 5].length) (baseStart_4152713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152713 prefixEnd_4152713 := by exact prefixLift 4152713
  have htrace : WordTrace (prefixWord ++ tailWord_4152713) baseStart_4152713 baseEnd_4152713 := by
    simpa [prefixWord, tailWord_4152713, baseEnd_4152713] using wordTrace_append hprefix tailTrace_4152713
  have hstable : (prefixWord ++ tailWord_4152713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152713).length < 2 ^ (prefixWord ++ tailWord_4152713).sum := by decide
  have hdescent : baseEnd_4152713 < baseStart_4152713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152715 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 5]
def baseStart_4152715 : Nat := 118140960795 + 4152715 * 2 ^ 59
def prefixEnd_4152715 : Nat := 4983230072969 + 3 ^ 40 * 4152715 * 2
def baseEnd_4152715 : Nat := 2132338816135825217164517

theorem tailTrace_4152715 : CollatzResearch.WordTrace tailWord_4152715 prefixEnd_4152715 2132338816135825217164517 := by
  unfold tailWord_4152715
  simp only [CollatzResearch.WordTrace]
  refine ⟨151461959150430257102643599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100974639433620171401762399 151461959150430257102643599)
  ·
    refine ⟨227192938725645385653965399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151461959150430257102643599 227192938725645385653965399)
    ·
      refine ⟨340789408088468078480948099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227192938725645385653965399 340789408088468078480948099)
      ·
        refine ⟨511184112132702117721422149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340789408088468078480948099 511184112132702117721422149)
        ·
          refine ⟨95847021024881647072766653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 511184112132702117721422149 95847021024881647072766653)
          ·
            refine ⟨35942632884330617652287495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95847021024881647072766653 35942632884330617652287495)
            ·
              refine ⟨53913949326495926478431243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35942632884330617652287495 53913949326495926478431243)
              ·
                refine ⟨80870923989743889717646865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53913949326495926478431243 80870923989743889717646865)
                ·
                  refine ⟨60653192992307917288235149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80870923989743889717646865 60653192992307917288235149)
                  ·
                    refine ⟨22744947372115468983088181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60653192992307917288235149 22744947372115468983088181)
                    ·
                      refine ⟨2132338816135825217164517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22744947372115468983088181 2132338816135825217164517)
                      ·
                        rfl

theorem cell23_4152715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_4152715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152715 prefixEnd_4152715 := by exact prefixLift 4152715
  have htrace : WordTrace (prefixWord ++ tailWord_4152715) baseStart_4152715 baseEnd_4152715 := by
    simpa [prefixWord, tailWord_4152715, baseEnd_4152715] using wordTrace_append hprefix tailTrace_4152715
  have hstable : (prefixWord ++ tailWord_4152715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152715).length < 2 ^ (prefixWord ++ tailWord_4152715).sum := by decide
  have hdescent : baseEnd_4152715 < baseStart_4152715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152729 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 2, 4, 2]
def baseStart_4152729 : Nat := 118140960795 + 4152729 * 2 ^ 59
def prefixEnd_4152729 : Nat := 4983230072969 + 3 ^ 40 * 4152729 * 2
def baseEnd_4152729 : Nat := 2132346004864988162389453

theorem tailTrace_4152729 : CollatzResearch.WordTrace tailWord_4152729 prefixEnd_4152729 2132346004864988162389453 := by
  unfold tailWord_4152729
  simp only [CollatzResearch.WordTrace]
  refine ⟨151462469772379537493653241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100974979848253024995768827 151462469772379537493653241)
  ·
    refine ⟨113596852329284653120239931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151462469772379537493653241 113596852329284653120239931)
    ·
      refine ⟨170395278493926979680359897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113596852329284653120239931 170395278493926979680359897)
      ·
        refine ⟨127796458870445234760269923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170395278493926979680359897 127796458870445234760269923)
        ·
          refine ⟨191694688305667852140404885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127796458870445234760269923 191694688305667852140404885)
          ·
            refine ⟨8985688514328180569081479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191694688305667852140404885 8985688514328180569081479)
            ·
              refine ⟨13478532771492270853622219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8985688514328180569081479 13478532771492270853622219)
              ·
                refine ⟨20217799157238406280433329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13478532771492270853622219 20217799157238406280433329)
                ·
                  refine ⟨15163349367928804710324997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20217799157238406280433329 15163349367928804710324997)
                  ·
                    refine ⟨2843128006486650883185937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15163349367928804710324997 2843128006486650883185937)
                    ·
                      refine ⟨2132346004864988162389453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843128006486650883185937 2132346004864988162389453)
                      ·
                        rfl

theorem cell23_4152729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_4152729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152729 prefixEnd_4152729 := by exact prefixLift 4152729
  have htrace : WordTrace (prefixWord ++ tailWord_4152729) baseStart_4152729 baseEnd_4152729 := by
    simpa [prefixWord, tailWord_4152729, baseEnd_4152729] using wordTrace_append hprefix tailTrace_4152729
  have hstable : (prefixWord ++ tailWord_4152729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152729).length < 2 ^ (prefixWord ++ tailWord_4152729).sum := by decide
  have hdescent : baseEnd_4152729 < baseStart_4152729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152755 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 6]
def baseStart_4152755 : Nat := 118140960795 + 4152755 * 2 ^ 59
def prefixEnd_4152755 : Nat := 4983230072969 + 3 ^ 40 * 4152755 * 2
def baseEnd_4152755 : Nat := 2132359355362005060664333

theorem tailTrace_4152755 : CollatzResearch.WordTrace tailWord_4152755 prefixEnd_4152755 2132359355362005060664333 := by
  unfold tailWord_4152755
  simp only [CollatzResearch.WordTrace]
  refine ⟨151463418070285343934099719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100975612046856895956066479 151463418070285343934099719)
  ·
    refine ⟨227195127105428015901149579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151463418070285343934099719 227195127105428015901149579)
    ·
      refine ⟨340792690658142023851724369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227195127105428015901149579 340792690658142023851724369)
      ·
        refine ⟨255594517993606517888793277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340792690658142023851724369 255594517993606517888793277)
        ·
          refine ⟨95847944247602444208297479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255594517993606517888793277 95847944247602444208297479)
          ·
            refine ⟨143771916371403666312446219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95847944247602444208297479 143771916371403666312446219)
            ·
              refine ⟨215657874557105499468669329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143771916371403666312446219 215657874557105499468669329)
              ·
                refine ⟨161743405917829124601501997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215657874557105499468669329 161743405917829124601501997)
                ·
                  refine ⟨60653777219185921725563249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161743405917829124601501997 60653777219185921725563249)
                  ·
                    refine ⟨45490332914389441294172437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60653777219185921725563249 45490332914389441294172437)
                    ·
                      refine ⟨2132359355362005060664333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45490332914389441294172437 2132359355362005060664333)
                      ·
                        rfl

theorem cell23_4152755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_4152755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152755 prefixEnd_4152755 := by exact prefixLift 4152755
  have htrace : WordTrace (prefixWord ++ tailWord_4152755) baseStart_4152755 baseEnd_4152755 := by
    simpa [prefixWord, tailWord_4152755, baseEnd_4152755] using wordTrace_append hprefix tailTrace_4152755
  have hstable : (prefixWord ++ tailWord_4152755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152755).length < 2 ^ (prefixWord ++ tailWord_4152755).sum := by decide
  have hdescent : baseEnd_4152755 < baseStart_4152755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152779 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 3, 1, 3]
def baseStart_4152779 : Nat := 118140960795 + 4152779 * 2 ^ 59
def prefixEnd_4152779 : Nat := 4983230072969 + 3 ^ 40 * 4152779 * 2
def baseEnd_4152779 : Nat := 2132371678897712966764223

theorem tailTrace_4152779 : CollatzResearch.WordTrace tailWord_4152779 prefixEnd_4152779 2132371678897712966764223 := by
  unfold tailWord_4152779
  simp only [CollatzResearch.WordTrace]
  refine ⟨151464293422198396032973391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100976195614798930688648927 151464293422198396032973391)
  ·
    refine ⟨227196440133297594049460087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151464293422198396032973391 227196440133297594049460087)
    ·
      refine ⟨340794660199946391074190131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227196440133297594049460087 340794660199946391074190131)
      ·
        refine ⟨511191990299919586611285197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340794660199946391074190131 511191990299919586611285197)
        ·
          refine ⟨191696996362469844979231949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511191990299919586611285197 191696996362469844979231949)
          ·
            refine ⟨71886373635926191867211981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191696996362469844979231949 71886373635926191867211981)
            ·
              refine ⟨26957390113472321950204493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71886373635926191867211981 26957390113472321950204493)
              ·
                refine ⟨10109021292552120731326685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26957390113472321950204493 10109021292552120731326685)
                ·
                  refine ⟨3790882984707045274247507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10109021292552120731326685 3790882984707045274247507)
                  ·
                    refine ⟨5686324477060567911371261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3790882984707045274247507 5686324477060567911371261)
                    ·
                      refine ⟨2132371678897712966764223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5686324477060567911371261 2132371678897712966764223)
                      ·
                        rfl

theorem cell23_4152779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 1, 3].length) (baseStart_4152779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152779 prefixEnd_4152779 := by exact prefixLift 4152779
  have htrace : WordTrace (prefixWord ++ tailWord_4152779) baseStart_4152779 baseEnd_4152779 := by
    simpa [prefixWord, tailWord_4152779, baseEnd_4152779] using wordTrace_append hprefix tailTrace_4152779
  have hstable : (prefixWord ++ tailWord_4152779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152779).length < 2 ^ (prefixWord ++ tailWord_4152779).sum := by decide
  have hdescent : baseEnd_4152779 < baseStart_4152779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152782 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_4152782 : Nat := 118140960795 + 4152782 * 2 ^ 59
def prefixEnd_4152782 : Nat := 4983230072969 + 3 ^ 40 * 4152782 * 2
def baseEnd_4152782 : Nat := 710791073113225485008903

theorem tailTrace_4152782 : CollatzResearch.WordTrace tailWord_4152782 prefixEnd_4152782 710791073113225485008903 := by
  unfold tailWord_4152782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18933050355148440943166575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100976268560791685030221733 18933050355148440943166575)
  ·
    refine ⟨28399575532722661414749863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18933050355148440943166575 28399575532722661414749863)
    ·
      refine ⟨42599363299083992122124795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28399575532722661414749863 42599363299083992122124795)
      ·
        refine ⟨63899044948625988183187193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42599363299083992122124795 63899044948625988183187193)
        ·
          refine ⟨47924283711469491137390395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63899044948625988183187193 47924283711469491137390395)
          ·
            refine ⟨71886425567204236706085593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47924283711469491137390395 71886425567204236706085593)
            ·
              refine ⟨53914819175403177529564195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71886425567204236706085593 53914819175403177529564195)
              ·
                refine ⟨80872228763104766294346293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53914819175403177529564195 80872228763104766294346293)
                ·
                  refine ⟨7581771446541071840094965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80872228763104766294346293 7581771446541071840094965)
                  ·
                    refine ⟨710791073113225485008903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7581771446541071840094965 710791073113225485008903)
                    ·
                      rfl

theorem cell23_4152782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_4152782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152782 prefixEnd_4152782 := by exact prefixLift 4152782
  have htrace : WordTrace (prefixWord ++ tailWord_4152782) baseStart_4152782 baseEnd_4152782 := by
    simpa [prefixWord, tailWord_4152782, baseEnd_4152782] using wordTrace_append hprefix tailTrace_4152782
  have hstable : (prefixWord ++ tailWord_4152782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152782).length < 2 ^ (prefixWord ++ tailWord_4152782).sum := by decide
  have hdescent : baseEnd_4152782 < baseStart_4152782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152789 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 3, 5, 2]
def baseStart_4152789 : Nat := 118140960795 + 4152789 * 2 ^ 59
def prefixEnd_4152789 : Nat := 4983230072969 + 3 ^ 40 * 4152789 * 2
def baseEnd_4152789 : Nat := 2132376813704257927639177

theorem tailTrace_4152789 : CollatzResearch.WordTrace tailWord_4152789 prefixEnd_4152789 2132376813704257927639177 := by
  unfold tailWord_4152789
  simp only [CollatzResearch.WordTrace]
  refine ⟨151464658152162167740837421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100976438768108111827224947 151464658152162167740837421)
  ·
    refine ⟨56799246807060812902814033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151464658152162167740837421 56799246807060812902814033)
    ·
      refine ⟨42599435105295609677110525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56799246807060812902814033 42599435105295609677110525)
      ·
        refine ⟨15974788164485853628916447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42599435105295609677110525 15974788164485853628916447)
        ·
          refine ⟨23962182246728780443374671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15974788164485853628916447 23962182246728780443374671)
          ·
            refine ⟨35943273370093170665062007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23962182246728780443374671 35943273370093170665062007)
            ·
              refine ⟨53914910055139755997593011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35943273370093170665062007 53914910055139755997593011)
              ·
                refine ⟨80872365082709633996389517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53914910055139755997593011 80872365082709633996389517)
                ·
                  refine ⟨30327136906016112748646069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80872365082709633996389517 30327136906016112748646069)
                  ·
                    refine ⟨2843169084939010570185569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30327136906016112748646069 2843169084939010570185569)
                    ·
                      refine ⟨2132376813704257927639177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843169084939010570185569 2132376813704257927639177)
                      ·
                        rfl

theorem cell23_4152789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_4152789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152789 prefixEnd_4152789 := by exact prefixLift 4152789
  have htrace : WordTrace (prefixWord ++ tailWord_4152789) baseStart_4152789 baseEnd_4152789 := by
    simpa [prefixWord, tailWord_4152789, baseEnd_4152789] using wordTrace_append hprefix tailTrace_4152789
  have hstable : (prefixWord ++ tailWord_4152789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152789).length < 2 ^ (prefixWord ++ tailWord_4152789).sum := by decide
  have hdescent : baseEnd_4152789 < baseStart_4152789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152795 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 4, 10]
def baseStart_4152795 : Nat := 118140960795 + 4152795 * 2 ^ 59
def prefixEnd_4152795 : Nat := 4983230072969 + 3 ^ 40 * 4152795 * 2
def baseEnd_4152795 : Nat := 710793298196061634721383

theorem tailTrace_4152795 : CollatzResearch.WordTrace tailWord_4152795 prefixEnd_4152795 710793298196061634721383 := by
  unfold tailWord_4152795
  simp only [CollatzResearch.WordTrace]
  refine ⟨151464876990140430765555839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100976584660093620510370559 151464876990140430765555839)
  ·
    refine ⟨227197315485210646148333759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151464876990140430765555839 227197315485210646148333759)
    ·
      refine ⟨340795973227815969222500639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227197315485210646148333759 340795973227815969222500639)
      ·
        refine ⟨511193959841723953833750959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340795973227815969222500639 511193959841723953833750959)
        ·
          refine ⟨766790939762585930750626439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511193959841723953833750959 766790939762585930750626439)
          ·
            refine ⟨1150186409643878896125939659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766790939762585930750626439 1150186409643878896125939659)
            ·
              refine ⟨1725279614465818344188909489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150186409643878896125939659 1725279614465818344188909489)
              ·
                refine ⟨1293959710849363758141682117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725279614465818344188909489 1293959710849363758141682117)
                ·
                  refine ⟨242617445784255704651565397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293959710849363758141682117 242617445784255704651565397)
                  ·
                    refine ⟨710793298196061634721383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 242617445784255704651565397 710793298196061634721383)
                    ·
                      rfl

theorem cell23_4152795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 10].length) (baseStart_4152795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152795 prefixEnd_4152795 := by exact prefixLift 4152795
  have htrace : WordTrace (prefixWord ++ tailWord_4152795) baseStart_4152795 baseEnd_4152795 := by
    simpa [prefixWord, tailWord_4152795, baseEnd_4152795] using wordTrace_append hprefix tailTrace_4152795
  have hstable : (prefixWord ++ tailWord_4152795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152795).length < 2 ^ (prefixWord ++ tailWord_4152795).sum := by decide
  have hdescent : baseEnd_4152795 < baseStart_4152795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152799 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 1, 5]
def baseStart_4152799 : Nat := 118140960795 + 4152799 * 2 ^ 59
def prefixEnd_4152799 : Nat := 4983230072969 + 3 ^ 40 * 4152799 * 2
def baseEnd_4152799 : Nat := 710793982836934296171377

theorem tailTrace_4152799 : CollatzResearch.WordTrace tailWord_4152799 prefixEnd_4152799 710793982836934296171377 := by
  unfold tailWord_4152799
  simp only [CollatzResearch.WordTrace]
  refine ⟨151465022882125939448701451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100976681921417292965800967 151465022882125939448701451)
  ·
    refine ⟨227197534323188909173052177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151465022882125939448701451 227197534323188909173052177)
    ·
      refine ⟨170398150742391681879789133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227197534323188909173052177 170398150742391681879789133)
      ·
        refine ⟨63899306528396880704920925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170398150742391681879789133 63899306528396880704920925)
        ·
          refine ⟨23962239948148830264345347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63899306528396880704920925 23962239948148830264345347)
          ·
            refine ⟨35943359922223245396518021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23962239948148830264345347 35943359922223245396518021)
            ·
              refine ⟨6739379985416858511847129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35943359922223245396518021 6739379985416858511847129)
              ·
                refine ⟨5054534989062643883885347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6739379985416858511847129 5054534989062643883885347)
                ·
                  refine ⟨7581802483593965825828021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054534989062643883885347 7581802483593965825828021)
                  ·
                    refine ⟨710793982836934296171377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7581802483593965825828021 710793982836934296171377)
                    ·
                      rfl

theorem cell23_4152799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 5].length) (baseStart_4152799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152799 prefixEnd_4152799 := by exact prefixLift 4152799
  have htrace : WordTrace (prefixWord ++ tailWord_4152799) baseStart_4152799 baseEnd_4152799 := by
    simpa [prefixWord, tailWord_4152799, baseEnd_4152799] using wordTrace_append hprefix tailTrace_4152799
  have hstable : (prefixWord ++ tailWord_4152799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152799).length < 2 ^ (prefixWord ++ tailWord_4152799).sum := by decide
  have hdescent : baseEnd_4152799 < baseStart_4152799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152829 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_4152829 : Nat := 118140960795 + 4152829 * 2 ^ 59
def prefixEnd_4152829 : Nat := 4983230072969 + 3 ^ 40 * 4152829 * 2
def baseEnd_4152829 : Nat := 710799117643479257046331

theorem tailTrace_4152829 : CollatzResearch.WordTrace tailWord_4152829 prefixEnd_4152829 710799117643479257046331 := by
  unfold tailWord_4152829
  simp only [CollatzResearch.WordTrace]
  refine ⟨151466117072017254572293541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100977411381344836381529027 151466117072017254572293541)
  ·
    refine ⟨28399896951003235232305039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151466117072017254572293541 28399896951003235232305039)
    ·
      refine ⟨42599845426504852848457559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28399896951003235232305039 42599845426504852848457559)
      ·
        refine ⟨63899768139757279272686339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42599845426504852848457559 63899768139757279272686339)
        ·
          refine ⟨95849652209635918909029509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63899768139757279272686339 95849652209635918909029509)
          ·
            refine ⟨17971809789306734795443033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95849652209635918909029509 17971809789306734795443033)
            ·
              refine ⟨13478857341980051096582275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17971809789306734795443033 13478857341980051096582275)
              ·
                refine ⟨20218286012970076644873413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13478857341980051096582275 20218286012970076644873413)
                ·
                  refine ⟨3790928627431889370913765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20218286012970076644873413 3790928627431889370913765)
                  ·
                    refine ⟨710799117643479257046331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3790928627431889370913765 710799117643479257046331)
                    ·
                      rfl

theorem cell23_4152829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_4152829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152829 prefixEnd_4152829 := by exact prefixLift 4152829
  have htrace : WordTrace (prefixWord ++ tailWord_4152829) baseStart_4152829 baseEnd_4152829 := by
    simpa [prefixWord, tailWord_4152829, baseEnd_4152829] using wordTrace_append hprefix tailTrace_4152829
  have hstable : (prefixWord ++ tailWord_4152829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152829).length < 2 ^ (prefixWord ++ tailWord_4152829).sum := by decide
  have hdescent : baseEnd_4152829 < baseStart_4152829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152839 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_4152839 : Nat := 118140960795 + 4152839 * 2 ^ 59
def prefixEnd_4152839 : Nat := 4983230072969 + 3 ^ 40 * 4152839 * 2
def baseEnd_4152839 : Nat := 2132402487736982732013947

theorem tailTrace_4152839 : CollatzResearch.WordTrace tailWord_4152839 prefixEnd_4152839 2132402487736982732013947 := by
  unfold tailWord_4152839
  simp only [CollatzResearch.WordTrace]
  refine ⟨151466481801981026280157571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100977654534654017520105047 151466481801981026280157571)
  ·
    refine ⟨227199722702971539420236357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151466481801981026280157571 227199722702971539420236357)
    ·
      refine ⟨42599948006807163641294317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227199722702971539420236357 42599948006807163641294317)
      ·
        refine ⟨15974980502552686365485369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42599948006807163641294317 15974980502552686365485369)
        ·
          refine ⟨11981235376914514774114027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15974980502552686365485369 11981235376914514774114027)
          ·
            refine ⟨17971853065371772161171041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11981235376914514774114027 17971853065371772161171041)
            ·
              refine ⟨13478889799028829120878281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17971853065371772161171041 13478889799028829120878281)
              ·
                refine ⟨10109167349271621840658711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13478889799028829120878281 10109167349271621840658711)
                ·
                  refine ⟨15163751023907432760988067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10109167349271621840658711 15163751023907432760988067)
                  ·
                    refine ⟨22745626535861149141482101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15163751023907432760988067 22745626535861149141482101)
                    ·
                      refine ⟨2132402487736982732013947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22745626535861149141482101 2132402487736982732013947)
                      ·
                        rfl

theorem cell23_4152839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_4152839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152839 prefixEnd_4152839 := by exact prefixLift 4152839
  have htrace : WordTrace (prefixWord ++ tailWord_4152839) baseStart_4152839 baseEnd_4152839 := by
    simpa [prefixWord, tailWord_4152839, baseEnd_4152839] using wordTrace_append hprefix tailTrace_4152839
  have hstable : (prefixWord ++ tailWord_4152839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152839).length < 2 ^ (prefixWord ++ tailWord_4152839).sum := by decide
  have hdescent : baseEnd_4152839 < baseStart_4152839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152842 : List Nat := [3, 1, 2, 2, 2, 2, 1, 10]
def baseStart_4152842 : Nat := 118140960795 + 4152842 * 2 ^ 59
def prefixEnd_4152842 : Nat := 4983230072969 + 3 ^ 40 * 4152842 * 2
def baseEnd_4152842 : Nat := 78977926969590600750979

theorem tailTrace_4152842 : CollatzResearch.WordTrace tailWord_4152842 prefixEnd_4152842 78977926969590600750979 := by
  unfold tailWord_4152842
  simp only [CollatzResearch.WordTrace]
  refine ⟨37866647805242539448129195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100977727480646771861677853 37866647805242539448129195)
  ·
    refine ⟨56799971707863809172193793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37866647805242539448129195 56799971707863809172193793)
    ·
      refine ⟨42599978780897856879145345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56799971707863809172193793 42599978780897856879145345)
      ·
        refine ⟨31949984085673392659359009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42599978780897856879145345 31949984085673392659359009)
        ·
          refine ⟨23962488064255044494519257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31949984085673392659359009 23962488064255044494519257)
          ·
            refine ⟨17971866048191283370889443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23962488064255044494519257 17971866048191283370889443)
            ·
              refine ⟨26957799072286925056334165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17971866048191283370889443 26957799072286925056334165)
              ·
                refine ⟨78977926969590600750979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26957799072286925056334165 78977926969590600750979)
                ·
                  rfl

theorem cell23_4152842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 10].length) (baseStart_4152842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152842 prefixEnd_4152842 := by exact prefixLift 4152842
  have htrace : WordTrace (prefixWord ++ tailWord_4152842) baseStart_4152842 baseEnd_4152842 := by
    simpa [prefixWord, tailWord_4152842, baseEnd_4152842] using wordTrace_append hprefix tailTrace_4152842
  have hstable : (prefixWord ++ tailWord_4152842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152842).length < 2 ^ (prefixWord ++ tailWord_4152842).sum := by decide
  have hdescent : baseEnd_4152842 < baseStart_4152842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152856 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 3, 2, 3]
def baseStart_4152856 : Nat := 118140960795 + 4152856 * 2 ^ 59
def prefixEnd_4152856 : Nat := 4983230072969 + 3 ^ 40 * 4152856 * 2
def baseEnd_4152856 : Nat := 2132411216908109165501369

theorem tailTrace_4152856 : CollatzResearch.WordTrace tailWord_4152856 prefixEnd_4152856 2132411216908109165501369 := by
  unfold tailWord_4152856
  simp only [CollatzResearch.WordTrace]
  refine ⟨75733550921459719091763211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100978067895279625455684281 75733550921459719091763211)
  ·
    refine ⟨113600326382189578637644817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75733550921459719091763211 113600326382189578637644817)
    ·
      refine ⟨85200244786642183978233613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113600326382189578637644817 85200244786642183978233613)
      ·
        refine ⟨31950091794990818991837605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85200244786642183978233613 31950091794990818991837605)
        ·
          refine ⟨5990642211560778560969551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31950091794990818991837605 5990642211560778560969551)
          ·
            refine ⟨8985963317341167841454327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5990642211560778560969551 8985963317341167841454327)
            ·
              refine ⟨13478944976011751762181491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8985963317341167841454327 13478944976011751762181491)
              ·
                refine ⟨20218417464017627643272237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13478944976011751762181491 20218417464017627643272237)
                ·
                  refine ⟨7581906549006610366227089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20218417464017627643272237 7581906549006610366227089)
                  ·
                    refine ⟨5686429911754957774670317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7581906549006610366227089 5686429911754957774670317)
                    ·
                      refine ⟨2132411216908109165501369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5686429911754957774670317 2132411216908109165501369)
                      ·
                        rfl

theorem cell23_4152856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_4152856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152856 prefixEnd_4152856 := by exact prefixLift 4152856
  have htrace : WordTrace (prefixWord ++ tailWord_4152856) baseStart_4152856 baseEnd_4152856 := by
    simpa [prefixWord, tailWord_4152856, baseEnd_4152856] using wordTrace_append hprefix tailTrace_4152856
  have hstable : (prefixWord ++ tailWord_4152856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152856).length < 2 ^ (prefixWord ++ tailWord_4152856).sum := by decide
  have hdescent : baseEnd_4152856 < baseStart_4152856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152887 : List Nat := [1, 1, 3, 1, 2, 6, 2, 2, 1, 2, 2]
def baseStart_4152887 : Nat := 118140960795 + 4152887 * 2 ^ 59
def prefixEnd_4152887 : Nat := 4983230072969 + 3 ^ 40 * 4152887 * 2
def baseEnd_4152887 : Nat := 2132427134808398544213727

theorem tailTrace_4152887 : CollatzResearch.WordTrace tailWord_4152887 prefixEnd_4152887 2132427134808398544213727 := by
  unfold tailWord_4152887
  simp only [CollatzResearch.WordTrace]
  refine ⟨151468232505807130477904915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100978821670538086985269943 151468232505807130477904915)
  ·
    refine ⟨227202348758710695716857373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151468232505807130477904915 227202348758710695716857373)
    ·
      refine ⟨85200880784516510893821515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227202348758710695716857373 85200880784516510893821515)
      ·
        refine ⟨127801321176774766340732273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85200880784516510893821515 127801321176774766340732273)
        ·
          refine ⟨95850990882581074755549205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127801321176774766340732273 95850990882581074755549205)
          ·
            refine ⟨4493015197620987879166369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95850990882581074755549205 4493015197620987879166369)
            ·
              refine ⟨3369761398215740909374777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4493015197620987879166369 3369761398215740909374777)
              ·
                refine ⟨2527321048661805682031083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3369761398215740909374777 2527321048661805682031083)
                ·
                  refine ⟨3790981572992708523046625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527321048661805682031083 3790981572992708523046625)
                  ·
                    refine ⟨2843236179744531392284969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3790981572992708523046625 2843236179744531392284969)
                    ·
                      refine ⟨2132427134808398544213727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843236179744531392284969 2132427134808398544213727)
                      ·
                        rfl

theorem cell23_4152887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 1, 2, 2].length) (baseStart_4152887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152887 prefixEnd_4152887 := by exact prefixLift 4152887
  have htrace : WordTrace (prefixWord ++ tailWord_4152887) baseStart_4152887 baseEnd_4152887 := by
    simpa [prefixWord, tailWord_4152887, baseEnd_4152887] using wordTrace_append hprefix tailTrace_4152887
  have hstable : (prefixWord ++ tailWord_4152887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152887).length < 2 ^ (prefixWord ++ tailWord_4152887).sum := by decide
  have hdescent : baseEnd_4152887 < baseStart_4152887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152952 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_4152952 : Nat := 118140960795 + 4152952 * 2 ^ 59
def prefixEnd_4152952 : Nat := 4983230072969 + 3 ^ 40 * 4152952 * 2
def baseEnd_4152952 : Nat := 2132460511050940789900927

theorem tailTrace_4152952 : CollatzResearch.WordTrace tailWord_4152952 prefixEnd_4152952 2132460511050940789900927 := by
  unfold tailWord_4152952
  simp only [CollatzResearch.WordTrace]
  refine ⟨75735301625285823289510555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100980402167047764386014073 75735301625285823289510555)
  ·
    refine ⟨113602952437928734934265833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75735301625285823289510555 113602952437928734934265833)
    ·
      refine ⟨85202214328446551200699375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113602952437928734934265833 85202214328446551200699375)
      ·
        refine ⟨127803321492669826801049063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85202214328446551200699375 127803321492669826801049063)
        ·
          refine ⟨191704982239004740201573595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127803321492669826801049063 191704982239004740201573595)
          ·
            refine ⟨287557473358507110302360393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191704982239004740201573595 287557473358507110302360393)
            ·
              refine ⟨215668105018880332726770295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287557473358507110302360393 215668105018880332726770295)
              ·
                refine ⟨323502157528320499090155443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215668105018880332726770295 323502157528320499090155443)
                ·
                  refine ⟨485253236292480748635233165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323502157528320499090155443 485253236292480748635233165)
                  ·
                    refine ⟨181969963609680280738212437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485253236292480748635233165 181969963609680280738212437)
                    ·
                      refine ⟨2132460511050940789900927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 181969963609680280738212437 2132460511050940789900927)
                      ·
                        rfl

theorem cell23_4152952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_4152952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152952 prefixEnd_4152952 := by exact prefixLift 4152952
  have htrace : WordTrace (prefixWord ++ tailWord_4152952) baseStart_4152952 baseEnd_4152952 := by
    simpa [prefixWord, tailWord_4152952, baseEnd_4152952] using wordTrace_append hprefix tailTrace_4152952
  have hstable : (prefixWord ++ tailWord_4152952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152952).length < 2 ^ (prefixWord ++ tailWord_4152952).sum := by decide
  have hdescent : baseEnd_4152952 < baseStart_4152952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152960 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 2, 2, 2]
def baseStart_4152960 : Nat := 118140960795 + 4152960 * 2 ^ 59
def prefixEnd_4152960 : Nat := 4983230072969 + 3 ^ 40 * 4152960 * 2
def baseEnd_4152960 : Nat := 2132464618896176758600891

theorem tailTrace_4152960 : CollatzResearch.WordTrace tailWord_4152960 prefixEnd_4152960 2132464618896176758600891 := by
  unfold tailWord_4152960
  simp only [CollatzResearch.WordTrace]
  refine ⟨75735447517271331972656167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100980596689695109296874889 75735447517271331972656167)
  ·
    refine ⟨113603171275906997958984251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75735447517271331972656167 113603171275906997958984251)
    ·
      refine ⟨170404756913860496938476377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113603171275906997958984251 170404756913860496938476377)
      ·
        refine ⟨127803567685395372703857283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170404756913860496938476377 127803567685395372703857283)
        ·
          refine ⟨191705351528093059055785925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127803567685395372703857283 191705351528093059055785925)
          ·
            refine ⟨35944753411517448572959861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191705351528093059055785925 35944753411517448572959861)
            ·
              refine ⟨3369820632329760803714987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35944753411517448572959861 3369820632329760803714987)
              ·
                refine ⟨5054730948494641205572481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369820632329760803714987 5054730948494641205572481)
                ·
                  refine ⟨3791048211370980904179361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5054730948494641205572481 3791048211370980904179361)
                  ·
                    refine ⟨2843286158528235678134521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3791048211370980904179361 2843286158528235678134521)
                    ·
                      refine ⟨2132464618896176758600891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843286158528235678134521 2132464618896176758600891)
                      ·
                        rfl

theorem cell23_4152960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_4152960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152960 prefixEnd_4152960 := by exact prefixLift 4152960
  have htrace : WordTrace (prefixWord ++ tailWord_4152960) baseStart_4152960 baseEnd_4152960 := by
    simpa [prefixWord, tailWord_4152960, baseEnd_4152960] using wordTrace_append hprefix tailTrace_4152960
  have hstable : (prefixWord ++ tailWord_4152960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152960).length < 2 ^ (prefixWord ++ tailWord_4152960).sum := by decide
  have hdescent : baseEnd_4152960 < baseStart_4152960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152983 : List Nat := [1, 1, 3, 3, 2, 4, 1, 3, 5]
def baseStart_4152983 : Nat := 118140960795 + 4152983 * 2 ^ 59
def prefixEnd_4152983 : Nat := 4983230072969 + 3 ^ 40 * 4152983 * 2
def baseEnd_4152983 : Nat := 236941825439025574290365

theorem tailTrace_4152983 : CollatzResearch.WordTrace tailWord_4152983 prefixEnd_4152983 236941825439025574290365 := by
  unfold tailWord_4152983
  simp only [CollatzResearch.WordTrace]
  refine ⟨151471733913459338873399603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100981155942306225915599735 151471733913459338873399603)
  ·
    refine ⟨227207600870189008310099405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151471733913459338873399603 227207600870189008310099405)
    ·
      refine ⟨85202850326320878116287277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227207600870189008310099405 85202850326320878116287277)
      ·
        refine ⟨31951068872370329293607729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85202850326320878116287277 31951068872370329293607729)
        ·
          refine ⟨23963301654277746970205797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31951068872370329293607729 23963301654277746970205797)
          ·
            refine ⟨4493119060177077556913587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23963301654277746970205797 4493119060177077556913587)
            ·
              refine ⟨6739678590265616335370381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4493119060177077556913587 6739678590265616335370381)
              ·
                refine ⟨2527379471349606125763893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6739678590265616335370381 2527379471349606125763893)
                ·
                  refine ⟨236941825439025574290365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2527379471349606125763893 236941825439025574290365)
                  ·
                    rfl

theorem cell23_4152983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 5].length) (baseStart_4152983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152983 prefixEnd_4152983 := by exact prefixLift 4152983
  have htrace : WordTrace (prefixWord ++ tailWord_4152983) baseStart_4152983 baseEnd_4152983 := by
    simpa [prefixWord, tailWord_4152983, baseEnd_4152983] using wordTrace_append hprefix tailTrace_4152983
  have hstable : (prefixWord ++ tailWord_4152983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152983).length < 2 ^ (prefixWord ++ tailWord_4152983).sum := by decide
  have hdescent : baseEnd_4152983 < baseStart_4152983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152989 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_4152989 : Nat := 118140960795 + 4152989 * 2 ^ 59
def prefixEnd_4152989 : Nat := 4983230072969 + 3 ^ 40 * 4152989 * 2
def baseEnd_4152989 : Nat := 2132479509835157145138257

theorem tailTrace_4152989 : CollatzResearch.WordTrace tailWord_4152989 prefixEnd_4152989 2132479509835157145138257 := by
  unfold tailWord_4152989
  simp only [CollatzResearch.WordTrace]
  refine ⟨151471952751437601898118021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100981301834291734598745347 151471952751437601898118021)
  ·
    refine ⟨28400991140894550355897129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151471952751437601898118021 28400991140894550355897129)
    ·
      refine ⟨21300743355670912766922847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28400991140894550355897129 21300743355670912766922847)
      ·
        refine ⟨31951115033506369150384271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21300743355670912766922847 31951115033506369150384271)
        ·
          refine ⟨47926672550259553725576407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31951115033506369150384271 47926672550259553725576407)
          ·
            refine ⟨71890008825389330588364611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47926672550259553725576407 71890008825389330588364611)
            ·
              refine ⟨107835013238083995882546917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71890008825389330588364611 107835013238083995882546917)
              ·
                refine ⟨20219064982140749227977547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107835013238083995882546917 20219064982140749227977547)
                ·
                  refine ⟨30328597473211123841966321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20219064982140749227977547 30328597473211123841966321)
                  ·
                    refine ⟨22746448104908342881474741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30328597473211123841966321 22746448104908342881474741)
                    ·
                      refine ⟨2132479509835157145138257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22746448104908342881474741 2132479509835157145138257)
                      ·
                        rfl

theorem cell23_4152989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_4152989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152989 prefixEnd_4152989 := by exact prefixLift 4152989
  have htrace : WordTrace (prefixWord ++ tailWord_4152989) baseStart_4152989 baseEnd_4152989 := by
    simpa [prefixWord, tailWord_4152989, baseEnd_4152989] using wordTrace_append hprefix tailTrace_4152989
  have hstable : (prefixWord ++ tailWord_4152989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152989).length < 2 ^ (prefixWord ++ tailWord_4152989).sum := by decide
  have hdescent : baseEnd_4152989 < baseStart_4152989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4152996 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_4152996 : Nat := 118140960795 + 4152996 * 2 ^ 59
def prefixEnd_4152996 : Nat := 4983230072969 + 3 ^ 40 * 4152996 * 2
def baseEnd_4152996 : Nat := 710827701399912872583575

theorem tailTrace_4152996 : CollatzResearch.WordTrace tailWord_4152996 prefixEnd_4152996 710827701399912872583575 := by
  unfold tailWord_4152996
  simp only [CollatzResearch.WordTrace]
  refine ⟨75736104031206121046811421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100981472041608161395748561 75736104031206121046811421)
  ·
    refine ⟨28401039011702295392554283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75736104031206121046811421 28401039011702295392554283)
    ·
      refine ⟨42601558517553443088831425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28401039011702295392554283 42601558517553443088831425)
      ·
        refine ⟨31951168888165082316623569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42601558517553443088831425 31951168888165082316623569)
        ·
          refine ⟨23963376666123811737467677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31951168888165082316623569 23963376666123811737467677)
          ·
            refine ⟨8986266249796429401550379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23963376666123811737467677 8986266249796429401550379)
            ·
              refine ⟨13479399374694644102325569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986266249796429401550379 13479399374694644102325569)
              ·
                refine ⟨10109549531020983076744177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13479399374694644102325569 10109549531020983076744177)
                ·
                  refine ⟨7582162148265737307558133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10109549531020983076744177 7582162148265737307558133)
                  ·
                    refine ⟨710827701399912872583575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7582162148265737307558133 710827701399912872583575)
                    ·
                      rfl

theorem cell23_4152996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_4152996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4152996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4152996 prefixEnd_4152996 := by exact prefixLift 4152996
  have htrace : WordTrace (prefixWord ++ tailWord_4152996) baseStart_4152996 baseEnd_4152996 := by
    simpa [prefixWord, tailWord_4152996, baseEnd_4152996] using wordTrace_append hprefix tailTrace_4152996
  have hstable : (prefixWord ++ tailWord_4152996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4152996).length < 2 ^ (prefixWord ++ tailWord_4152996).sum := by decide
  have hdescent : baseEnd_4152996 < baseStart_4152996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4152996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153016 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 2, 4, 2]
def baseStart_4153016 : Nat := 118140960795 + 4153016 * 2 ^ 59
def prefixEnd_4153016 : Nat := 4983230072969 + 3 ^ 40 * 4153016 * 2
def baseEnd_4153016 : Nat := 2132493373812828539500633

theorem tailTrace_4153016 : CollatzResearch.WordTrace tailWord_4153016 prefixEnd_4153016 2132493373812828539500633 := by
  unfold tailWord_4153016
  simp only [CollatzResearch.WordTrace]
  refine ⟨75736468761169892754675451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100981958348226523672900601 75736468761169892754675451)
  ·
    refine ⟨113604703141754839132013177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75736468761169892754675451 113604703141754839132013177)
    ·
      refine ⟨85203527356316129349009883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113604703141754839132013177 85203527356316129349009883)
      ·
        refine ⟨127805291034474194023514825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85203527356316129349009883 127805291034474194023514825)
        ·
          refine ⟨95853968275855645517636119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127805291034474194023514825 95853968275855645517636119)
          ·
            refine ⟨143780952413783468276454179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95853968275855645517636119 143780952413783468276454179)
            ·
              refine ⟨215671428620675202414681269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143780952413783468276454179 215671428620675202414681269)
              ·
                refine ⟨20219196433188300226376369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215671428620675202414681269 20219196433188300226376369)
                ·
                  refine ⟨15164397324891225169782277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20219196433188300226376369 15164397324891225169782277)
                  ·
                    refine ⟨2843324498417104719334177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15164397324891225169782277 2843324498417104719334177)
                    ·
                      refine ⟨2132493373812828539500633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843324498417104719334177 2132493373812828539500633)
                      ·
                        rfl

theorem cell23_4153016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_4153016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153016 prefixEnd_4153016 := by exact prefixLift 4153016
  have htrace : WordTrace (prefixWord ++ tailWord_4153016) baseStart_4153016 baseEnd_4153016 := by
    simpa [prefixWord, tailWord_4153016, baseEnd_4153016] using wordTrace_append hprefix tailTrace_4153016
  have hstable : (prefixWord ++ tailWord_4153016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153016).length < 2 ^ (prefixWord ++ tailWord_4153016).sum := by decide
  have hdescent : baseEnd_4153016 < baseStart_4153016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153019 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 3]
def baseStart_4153019 : Nat := 118140960795 + 4153019 * 2 ^ 59
def prefixEnd_4153019 : Nat := 4983230072969 + 3 ^ 40 * 4153019 * 2
def baseEnd_4153019 : Nat := 2132494914254792027763119

theorem tailTrace_4153019 : CollatzResearch.WordTrace tailWord_4153019 prefixEnd_4153019 2132494914254792027763119 := by
  unfold tailWord_4153019
  simp only [CollatzResearch.WordTrace]
  refine ⟨151473046941328917021710111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100982031294219278014473407 151473046941328917021710111)
  ·
    refine ⟨227209570411993375532565167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151473046941328917021710111 227209570411993375532565167)
    ·
      refine ⟨340814355617990063298847751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227209570411993375532565167 340814355617990063298847751)
      ·
        refine ⟨511221533426985094948271627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340814355617990063298847751 511221533426985094948271627)
        ·
          refine ⟨766832300140477642422407441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511221533426985094948271627 766832300140477642422407441)
          ·
            refine ⟨575124225105358231816805581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766832300140477642422407441 575124225105358231816805581)
            ·
              refine ⟨215671584414509336931302093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575124225105358231816805581 215671584414509336931302093)
              ·
                refine ⟨80876844155441001349238285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215671584414509336931302093 80876844155441001349238285)
                ·
                  refine ⟨30328816558290375505964357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80876844155441001349238285 30328816558290375505964357)
                  ·
                    refine ⟨5686653104679445407368317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30328816558290375505964357 5686653104679445407368317)
                    ·
                      refine ⟨2132494914254792027763119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5686653104679445407368317 2132494914254792027763119)
                      ·
                        rfl

theorem cell23_4153019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 3].length) (baseStart_4153019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153019 prefixEnd_4153019 := by exact prefixLift 4153019
  have htrace : WordTrace (prefixWord ++ tailWord_4153019) baseStart_4153019 baseEnd_4153019 := by
    simpa [prefixWord, tailWord_4153019, baseEnd_4153019] using wordTrace_append hprefix tailTrace_4153019
  have hstable : (prefixWord ++ tailWord_4153019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153019).length < 2 ^ (prefixWord ++ tailWord_4153019).sum := by decide
  have hdescent : baseEnd_4153019 < baseStart_4153019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153030 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4153030 : Nat := 118140960795 + 4153030 * 2 ^ 59
def prefixEnd_4153030 : Nat := 4983230072969 + 3 ^ 40 * 4153030 * 2
def baseEnd_4153030 : Nat := 710833520847330494908523

theorem tailTrace_4153030 : CollatzResearch.WordTrace tailWord_4153030 prefixEnd_4153030 710833520847330494908523 := by
  unfold tailWord_4153030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4733545254509033309386267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100982298762859377266907029 4733545254509033309386267)
  ·
    refine ⟨7100317881763549964079401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4733545254509033309386267 7100317881763549964079401)
    ·
      refine ⟨5325238411322662473059551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7100317881763549964079401 5325238411322662473059551)
      ·
        refine ⟨7987857616983993709589327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5325238411322662473059551 7987857616983993709589327)
        ·
          refine ⟨11981786425475990564383991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7987857616983993709589327 11981786425475990564383991)
          ·
            refine ⟨17972679638213985846575987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11981786425475990564383991 17972679638213985846575987)
            ·
              refine ⟨26959019457320978769863981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17972679638213985846575987 26959019457320978769863981)
              ·
                refine ⟨10109632296495367038698993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26959019457320978769863981 10109632296495367038698993)
                ·
                  refine ⟨7582224222371525279024245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10109632296495367038698993 7582224222371525279024245)
                  ·
                    refine ⟨710833520847330494908523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7582224222371525279024245 710833520847330494908523)
                    ·
                      rfl

theorem cell23_4153030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4153030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153030 prefixEnd_4153030 := by exact prefixLift 4153030
  have htrace : WordTrace (prefixWord ++ tailWord_4153030) baseStart_4153030 baseEnd_4153030 := by
    simpa [prefixWord, tailWord_4153030, baseEnd_4153030] using wordTrace_append hprefix tailTrace_4153030
  have hstable : (prefixWord ++ tailWord_4153030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153030).length < 2 ^ (prefixWord ++ tailWord_4153030).sum := by decide
  have hdescent : baseEnd_4153030 < baseStart_4153030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153100 : List Nat := [2, 2, 1, 2, 2, 1, 3, 5, 1, 1, 3]
def baseStart_4153100 : Nat := 118140960795 + 4153100 * 2 ^ 59
def prefixEnd_4153100 : Nat := 4983230072969 + 3 ^ 40 * 4153100 * 2
def baseEnd_4153100 : Nat := 2132536506187806210850247

theorem tailTrace_4153100 : CollatzResearch.WordTrace tailWord_4153100 prefixEnd_4153100 2132536506187806210850247 := by
  unfold tailWord_4153100
  simp only [CollatzResearch.WordTrace]
  refine ⟨75738000627017733927704377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100984000836023645236939169 75738000627017733927704377)
  ·
    refine ⟨56803500470263300445778283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75738000627017733927704377 56803500470263300445778283)
    ·
      refine ⟨85205250705394950668667425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56803500470263300445778283 85205250705394950668667425)
      ·
        refine ⟨63903938029046213001500569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85205250705394950668667425 63903938029046213001500569)
        ·
          refine ⟨47927953521784659751125427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63903938029046213001500569 47927953521784659751125427)
          ·
            refine ⟨71891930282676989626688141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47927953521784659751125427 71891930282676989626688141)
            ·
              refine ⟨26959473856003871110008053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71891930282676989626688141 26959473856003871110008053)
              ·
                refine ⟨2527450674000362916563255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26959473856003871110008053 2527450674000362916563255)
                ·
                  refine ⟨3791176011000544374844883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527450674000362916563255 3791176011000544374844883)
                  ·
                    refine ⟨5686764016500816562267325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3791176011000544374844883 5686764016500816562267325)
                    ·
                      refine ⟨2132536506187806210850247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5686764016500816562267325 2132536506187806210850247)
                      ·
                        rfl

theorem cell23_4153100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_4153100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153100 prefixEnd_4153100 := by exact prefixLift 4153100
  have htrace : WordTrace (prefixWord ++ tailWord_4153100) baseStart_4153100 baseEnd_4153100 := by
    simpa [prefixWord, tailWord_4153100, baseEnd_4153100] using wordTrace_append hprefix tailTrace_4153100
  have hstable : (prefixWord ++ tailWord_4153100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153100).length < 2 ^ (prefixWord ++ tailWord_4153100).sum := by decide
  have hdescent : baseEnd_4153100 < baseStart_4153100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153140 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_4153140 : Nat := 118140960795 + 4153140 * 2 ^ 59
def prefixEnd_4153140 : Nat := 4983230072969 + 3 ^ 40 * 4153140 * 2
def baseEnd_4153140 : Nat := 2132557045413986054350063

theorem tailTrace_4153140 : CollatzResearch.WordTrace tailWord_4153140 prefixEnd_4153140 2132557045413986054350063 := by
  unfold tailWord_4153140
  simp only [CollatzResearch.WordTrace]
  refine ⟨75738730086945277343432437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100984973449260369791243249 75738730086945277343432437)
  ·
    refine ⟨7100505945651119750946791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75738730086945277343432437 7100505945651119750946791)
    ·
      refine ⟨10650758918476679626420187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7100505945651119750946791 10650758918476679626420187)
      ·
        refine ⟨15976138377715019439630281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10650758918476679626420187 15976138377715019439630281)
        ·
          refine ⟨11982103783286264579722711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15976138377715019439630281 11982103783286264579722711)
          ·
            refine ⟨17973155674929396869584067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11982103783286264579722711 17973155674929396869584067)
            ·
              refine ⟨26959733512394095304376101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17973155674929396869584067 26959733512394095304376101)
              ·
                refine ⟨5054950033573892869570519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26959733512394095304376101 5054950033573892869570519)
                ·
                  refine ⟨7582425050360839304355779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054950033573892869570519 7582425050360839304355779)
                  ·
                    refine ⟨11373637575541258956533669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7582425050360839304355779 11373637575541258956533669)
                    ·
                      refine ⟨2132557045413986054350063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11373637575541258956533669 2132557045413986054350063)
                      ·
                        rfl

theorem cell23_4153140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_4153140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153140 prefixEnd_4153140 := by exact prefixLift 4153140
  have htrace : WordTrace (prefixWord ++ tailWord_4153140) baseStart_4153140 baseEnd_4153140 := by
    simpa [prefixWord, tailWord_4153140, baseEnd_4153140] using wordTrace_append hprefix tailTrace_4153140
  have hstable : (prefixWord ++ tailWord_4153140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153140).length < 2 ^ (prefixWord ++ tailWord_4153140).sum := by decide
  have hdescent : baseEnd_4153140 < baseStart_4153140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153146 : List Nat := [3, 1, 1, 1, 5, 2, 1, 9]
def baseStart_4153146 : Nat := 118140960795 + 4153146 * 2 ^ 59
def prefixEnd_4153146 : Nat := 4983230072969 + 3 ^ 40 * 4153146 * 2
def baseEnd_4153146 : Nat := 78983708381404186328705

theorem tailTrace_4153146 : CollatzResearch.WordTrace tailWord_4153146 prefixEnd_4153146 78983708381404186328705 := by
  unfold tailWord_4153146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37869419752967204427895823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100985119341245878474388861 37869419752967204427895823)
  ·
    refine ⟨56804129629450806641843735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37869419752967204427895823 56804129629450806641843735)
    ·
      refine ⟨85206194444176209962765603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56804129629450806641843735 85206194444176209962765603)
      ·
        refine ⟨127809291666264314944148405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85206194444176209962765603 127809291666264314944148405)
        ·
          refine ⟨11982121093712279526013913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127809291666264314944148405 11982121093712279526013913)
          ·
            refine ⟨8986590820284209644510435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11982121093712279526013913 8986590820284209644510435)
            ·
              refine ⟨13479886230426314466765653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986590820284209644510435 13479886230426314466765653)
              ·
                refine ⟨78983708381404186328705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13479886230426314466765653 78983708381404186328705)
                ·
                  rfl

theorem cell23_4153146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 9].length) (baseStart_4153146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153146 prefixEnd_4153146 := by exact prefixLift 4153146
  have htrace : WordTrace (prefixWord ++ tailWord_4153146) baseStart_4153146 baseEnd_4153146 := by
    simpa [prefixWord, tailWord_4153146, baseEnd_4153146] using wordTrace_append hprefix tailTrace_4153146
  have hstable : (prefixWord ++ tailWord_4153146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153146).length < 2 ^ (prefixWord ++ tailWord_4153146).sum := by decide
  have hdescent : baseEnd_4153146 < baseStart_4153146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153194 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4153194 : Nat := 118140960795 + 4153194 * 2 ^ 59
def prefixEnd_4153194 : Nat := 4983230072969 + 3 ^ 40 * 4153194 * 2
def baseEnd_4153194 : Nat := 2132584773369328843074815

theorem tailTrace_4153194 : CollatzResearch.WordTrace tailWord_4153194 prefixEnd_4153194 2132584773369328843074815 := by
  unfold tailWord_4153194
  simp only [CollatzResearch.WordTrace]
  refine ⟨37869857428923730477332659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100986286477129947939553757 37869857428923730477332659)
  ·
    refine ⟨56804786143385595715998989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37869857428923730477332659 56804786143385595715998989)
    ·
      refine ⟨21301794803769598393499621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56804786143385595715998989 21301794803769598393499621)
      ·
        refine ⟨3994086525706799698781179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21301794803769598393499621 3994086525706799698781179)
        ·
          refine ⟨5991129788560199548171769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3994086525706799698781179 5991129788560199548171769)
          ·
            refine ⟨4493347341420149661128827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5991129788560199548171769 4493347341420149661128827)
            ·
              refine ⟨6740021012130224491693241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4493347341420149661128827 6740021012130224491693241)
              ·
                refine ⟨5055015759097668368769931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6740021012130224491693241 5055015759097668368769931)
                ·
                  refine ⟨7582523638646502553154897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055015759097668368769931 7582523638646502553154897)
                  ·
                    refine ⟨5686892728984876914866173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7582523638646502553154897 5686892728984876914866173)
                    ·
                      refine ⟨2132584773369328843074815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5686892728984876914866173 2132584773369328843074815)
                      ·
                        rfl

theorem cell23_4153194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4153194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153194 prefixEnd_4153194 := by exact prefixLift 4153194
  have htrace : WordTrace (prefixWord ++ tailWord_4153194) baseStart_4153194 baseEnd_4153194 := by
    simpa [prefixWord, tailWord_4153194, baseEnd_4153194] using wordTrace_append hprefix tailTrace_4153194
  have hstable : (prefixWord ++ tailWord_4153194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153194).length < 2 ^ (prefixWord ++ tailWord_4153194).sum := by decide
  have hdescent : baseEnd_4153194 < baseStart_4153194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153216 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_4153216 : Nat := 118140960795 + 4153216 * 2 ^ 59
def prefixEnd_4153216 : Nat := 4983230072969 + 3 ^ 40 * 4153216 * 2
def baseEnd_4153216 : Nat := 2132596069943727756999713

theorem tailTrace_4153216 : CollatzResearch.WordTrace tailWord_4153216 prefixEnd_4153216 2132596069943727756999713 := by
  unfold tailWord_4153216
  simp only [CollatzResearch.WordTrace]
  refine ⟨75740116060807609833315751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100986821414410146444421001 75740116060807609833315751)
  ·
    refine ⟨113610174091211414749973627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75740116060807609833315751 113610174091211414749973627)
    ·
      refine ⟨170415261136817122124960441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113610174091211414749973627 170415261136817122124960441)
      ·
        refine ⟨127811445852612841593720331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170415261136817122124960441 127811445852612841593720331)
        ·
          refine ⟨191717168778919262390580497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127811445852612841593720331 191717168778919262390580497)
          ·
            refine ⟨143787876584189446792935373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191717168778919262390580497 143787876584189446792935373)
            ·
              refine ⟨53920453719071042547350765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143787876584189446792935373 53920453719071042547350765)
              ·
                refine ⟨20220170144651640955256537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53920453719071042547350765 20220170144651640955256537)
                ·
                  refine ⟨15165127608488730716442403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20220170144651640955256537 15165127608488730716442403)
                  ·
                    refine ⟨22747691412733096074663605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15165127608488730716442403 22747691412733096074663605)
                    ·
                      refine ⟨2132596069943727756999713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22747691412733096074663605 2132596069943727756999713)
                      ·
                        rfl

theorem cell23_4153216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_4153216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153216 prefixEnd_4153216 := by exact prefixLift 4153216
  have htrace : WordTrace (prefixWord ++ tailWord_4153216) baseStart_4153216 baseEnd_4153216 := by
    simpa [prefixWord, tailWord_4153216, baseEnd_4153216] using wordTrace_append hprefix tailTrace_4153216
  have hstable : (prefixWord ++ tailWord_4153216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153216).length < 2 ^ (prefixWord ++ tailWord_4153216).sum := by decide
  have hdescent : baseEnd_4153216 < baseStart_4153216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153240 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 2, 6]
def baseStart_4153240 : Nat := 118140960795 + 4153240 * 2 ^ 59
def prefixEnd_4153240 : Nat := 4983230072969 + 3 ^ 40 * 4153240 * 2
def baseEnd_4153240 : Nat := 710869464493145221033201

theorem tailTrace_4153240 : CollatzResearch.WordTrace tailWord_4153240 prefixEnd_4153240 710869464493145221033201 := by
  unfold tailWord_4153240
  simp only [CollatzResearch.WordTrace]
  refine ⟨75740553736764135882752587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100987404982352181177003449 75740553736764135882752587)
  ·
    refine ⟨113610830605146203824128881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75740553736764135882752587 113610830605146203824128881)
    ·
      refine ⟨85208122953859652868096661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113610830605146203824128881 85208122953859652868096661)
      ·
        refine ⟨3994130763462171228192031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85208122953859652868096661 3994130763462171228192031)
        ·
          refine ⟨5991196145193256842288047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3994130763462171228192031 5991196145193256842288047)
          ·
            refine ⟨8986794217789885263432071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991196145193256842288047 8986794217789885263432071)
            ·
              refine ⟨13480191326684827895148107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986794217789885263432071 13480191326684827895148107)
              ·
                refine ⟨20220286990027241842722161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13480191326684827895148107 20220286990027241842722161)
                ·
                  refine ⟨15165215242520431382041621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20220286990027241842722161 15165215242520431382041621)
                  ·
                    refine ⟨710869464493145221033201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15165215242520431382041621 710869464493145221033201)
                    ·
                      rfl

theorem cell23_4153240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_4153240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153240 prefixEnd_4153240 := by exact prefixLift 4153240
  have htrace : WordTrace (prefixWord ++ tailWord_4153240) baseStart_4153240 baseEnd_4153240 := by
    simpa [prefixWord, tailWord_4153240, baseEnd_4153240] using wordTrace_append hprefix tailTrace_4153240
  have hstable : (prefixWord ++ tailWord_4153240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153240).length < 2 ^ (prefixWord ++ tailWord_4153240).sum := by decide
  have hdescent : baseEnd_4153240 < baseStart_4153240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153247 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 1, 4, 2]
def baseStart_4153247 : Nat := 118140960795 + 4153247 * 2 ^ 59
def prefixEnd_4153247 : Nat := 4983230072969 + 3 ^ 40 * 4153247 * 2
def baseEnd_4153247 : Nat := 2132611987844017135712071

theorem tailTrace_4153247 : CollatzResearch.WordTrace tailWord_4153247 prefixEnd_4153247 2132611987844017135712071 := by
  unfold tailWord_4153247
  simp only [CollatzResearch.WordTrace]
  refine ⟨151481362784502911961009995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100987575189668607974006663 151481362784502911961009995)
  ·
    refine ⟨227222044176754367941514993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151481362784502911961009995 227222044176754367941514993)
    ·
      refine ⟨170416533132565775956136245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227222044176754367941514993 170416533132565775956136245)
      ·
        refine ⟨15976549981178041495887773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170416533132565775956136245 15976549981178041495887773)
        ·
          refine ⟨5991206242941765560957915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15976549981178041495887773 5991206242941765560957915)
          ·
            refine ⟨8986809364412648341436873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991206242941765560957915 8986809364412648341436873)
            ·
              refine ⟨6740107023309486256077655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8986809364412648341436873 6740107023309486256077655)
              ·
                refine ⟨10110160534964229384116483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6740107023309486256077655 10110160534964229384116483)
                ·
                  refine ⟨15165240802446344076174725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10110160534964229384116483 15165240802446344076174725)
                  ·
                    refine ⟨2843482650458689514282761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15165240802446344076174725 2843482650458689514282761)
                    ·
                      refine ⟨2132611987844017135712071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843482650458689514282761 2132611987844017135712071)
                      ·
                        rfl

theorem cell23_4153247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_4153247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153247 prefixEnd_4153247 := by exact prefixLift 4153247
  have htrace : WordTrace (prefixWord ++ tailWord_4153247) baseStart_4153247 baseEnd_4153247 := by
    simpa [prefixWord, tailWord_4153247, baseEnd_4153247] using wordTrace_append hprefix tailTrace_4153247
  have hstable : (prefixWord ++ tailWord_4153247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153247).length < 2 ^ (prefixWord ++ tailWord_4153247).sum := by decide
  have hdescent : baseEnd_4153247 < baseStart_4153247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153268 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_4153268 : Nat := 118140960795 + 4153268 * 2 ^ 59
def prefixEnd_4153268 : Nat := 4983230072969 + 3 ^ 40 * 4153268 * 2
def baseEnd_4153268 : Nat := 2132622770937761553549475

theorem tailTrace_4153268 : CollatzResearch.WordTrace tailWord_4153268 prefixEnd_4153268 2132622770937761553549475 := by
  unfold tailWord_4153268
  simp only [CollatzResearch.WordTrace]
  refine ⟨75741064358713416273762229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100988085811617888365016305 75741064358713416273762229)
  ·
    refine ⟨7100724783629382775665209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75741064358713416273762229 7100724783629382775665209)
    ·
      refine ⟨5325543587722037081748907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7100724783629382775665209 5325543587722037081748907)
      ·
        refine ⟨7988315381583055622623361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5325543587722037081748907 7988315381583055622623361)
        ·
          refine ⟨5991236536187291716967521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7988315381583055622623361 5991236536187291716967521)
          ·
            refine ⟨4493427402140468787725641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5991236536187291716967521 4493427402140468787725641)
            ·
              refine ⟨3370070551605351590794231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4493427402140468787725641 3370070551605351590794231)
              ·
                refine ⟨5055105827408027386191347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370070551605351590794231 5055105827408027386191347)
                ·
                  refine ⟨7582658741112041079287021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055105827408027386191347 7582658741112041079287021)
                  ·
                    refine ⟨2843497027917015404732633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7582658741112041079287021 2843497027917015404732633)
                    ·
                      refine ⟨2132622770937761553549475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843497027917015404732633 2132622770937761553549475)
                      ·
                        rfl

theorem cell23_4153268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_4153268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153268 prefixEnd_4153268 := by exact prefixLift 4153268
  have htrace : WordTrace (prefixWord ++ tailWord_4153268) baseStart_4153268 baseEnd_4153268 := by
    simpa [prefixWord, tailWord_4153268, baseEnd_4153268] using wordTrace_append hprefix tailTrace_4153268
  have hstable : (prefixWord ++ tailWord_4153268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153268).length < 2 ^ (prefixWord ++ tailWord_4153268).sum := by decide
  have hdescent : baseEnd_4153268 < baseStart_4153268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153323 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 3]
def baseStart_4153323 : Nat := 118140960795 + 4153323 * 2 ^ 59
def prefixEnd_4153323 : Nat := 4983230072969 + 3 ^ 40 * 4153323 * 2
def baseEnd_4153323 : Nat := 2132651012373758838361721

theorem tailTrace_4153323 : CollatzResearch.WordTrace tailWord_4153323 prefixEnd_4153323 2132651012373758838361721 := by
  unfold tailWord_4153323
  simp only [CollatzResearch.WordTrace]
  refine ⟨151484134732227576940776623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100989423154818384627184415 151484134732227576940776623)
  ·
    refine ⟨227226202098341365411164935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151484134732227576940776623 227226202098341365411164935)
    ·
      refine ⟨340839303147512048116747403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227226202098341365411164935 340839303147512048116747403)
      ·
        refine ⟨511258954721268072175121105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340839303147512048116747403 511258954721268072175121105)
        ·
          refine ⟨383444216040951054131340829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511258954721268072175121105 383444216040951054131340829)
          ·
            refine ⟨143791581015356645299252811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383444216040951054131340829 143791581015356645299252811)
            ·
              refine ⟨215687371523034967948879217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143791581015356645299252811 215687371523034967948879217)
              ·
                refine ⟨161765528642276225961659413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215687371523034967948879217 161765528642276225961659413)
                ·
                  refine ⟨7582759155106698091952785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161765528642276225961659413 7582759155106698091952785)
                  ·
                    refine ⟨5687069366330023568964589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7582759155106698091952785 5687069366330023568964589)
                    ·
                      refine ⟨2132651012373758838361721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5687069366330023568964589 2132651012373758838361721)
                      ·
                        rfl

theorem cell23_4153323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 3].length) (baseStart_4153323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153323 prefixEnd_4153323 := by exact prefixLift 4153323
  have htrace : WordTrace (prefixWord ++ tailWord_4153323) baseStart_4153323 baseEnd_4153323 := by
    simpa [prefixWord, tailWord_4153323, baseEnd_4153323] using wordTrace_append hprefix tailTrace_4153323
  have hstable : (prefixWord ++ tailWord_4153323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153323).length < 2 ^ (prefixWord ++ tailWord_4153323).sum := by decide
  have hdescent : baseEnd_4153323 < baseStart_4153323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153340 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_4153340 : Nat := 118140960795 + 4153340 * 2 ^ 59
def prefixEnd_4153340 : Nat := 4983230072969 + 3 ^ 40 * 4153340 * 2
def baseEnd_4153340 : Nat := 2132659741544885271849143

theorem tailTrace_4153340 : CollatzResearch.WordTrace tailWord_4153340 prefixEnd_4153340 2132659741544885271849143 := by
  unfold tailWord_4153340
  simp only [CollatzResearch.WordTrace]
  refine ⟨75742377386582994422072737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100989836515443992562763649 75742377386582994422072737)
  ·
    refine ⟨56806783039937245816554553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75742377386582994422072737 56806783039937245816554553)
    ·
      refine ⟨42605087279952934362415915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56806783039937245816554553 42605087279952934362415915)
      ·
        refine ⟨63907630919929401543623873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42605087279952934362415915 63907630919929401543623873)
        ·
          refine ⟨47930723189947051157717905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63907630919929401543623873 47930723189947051157717905)
          ·
            refine ⟨35948042392460288368288429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47930723189947051157717905 35948042392460288368288429)
            ·
              refine ⟨13480515897172608138108161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35948042392460288368288429 13480515897172608138108161)
              ·
                refine ⟨10110386922879456103581121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13480515897172608138108161 10110386922879456103581121)
                ·
                  refine ⟨7582790192159592077685841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10110386922879456103581121 7582790192159592077685841)
                  ·
                    refine ⟨5687092644119694058264381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7582790192159592077685841 5687092644119694058264381)
                    ·
                      refine ⟨2132659741544885271849143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5687092644119694058264381 2132659741544885271849143)
                      ·
                        rfl

theorem cell23_4153340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_4153340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153340 prefixEnd_4153340 := by exact prefixLift 4153340
  have htrace : WordTrace (prefixWord ++ tailWord_4153340) baseStart_4153340 baseEnd_4153340 := by
    simpa [prefixWord, tailWord_4153340, baseEnd_4153340] using wordTrace_append hprefix tailTrace_4153340
  have hstable : (prefixWord ++ tailWord_4153340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153340).length < 2 ^ (prefixWord ++ tailWord_4153340).sum := by decide
  have hdescent : baseEnd_4153340 < baseStart_4153340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153397 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_4153397 : Nat := 118140960795 + 4153397 * 2 ^ 59
def prefixEnd_4153397 : Nat := 4983230072969 + 3 ^ 40 * 4153397 * 2
def baseEnd_4153397 : Nat := 2132689009942191548836381

theorem tailTrace_4153397 : CollatzResearch.WordTrace tailWord_4153397 prefixEnd_4153397 2132689009942191548836381 := by
  unfold tailWord_4153397
  simp only [CollatzResearch.WordTrace]
  refine ⟨151486833733959487578970445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100991222489306325052646963 151486833733959487578970445)
  ·
    refine ⟨56807562650234807842113917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151486833733959487578970445 56807562650234807842113917)
    ·
      refine ⟨21302835993838052940792719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56807562650234807842113917 21302835993838052940792719)
      ·
        refine ⟨31954253990757079411189079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21302835993838052940792719 31954253990757079411189079)
        ·
          refine ⟨47931380986135619116783619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31954253990757079411189079 47931380986135619116783619)
          ·
            refine ⟨71897071479203428675175429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47931380986135619116783619 71897071479203428675175429)
            ·
              refine ⟨13480700902350642876595393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71897071479203428675175429 13480700902350642876595393)
              ·
                refine ⟨10110525676762982157446545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13480700902350642876595393 10110525676762982157446545)
                ·
                  refine ⟨7582894257572236618084909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10110525676762982157446545 7582894257572236618084909)
                  ·
                    refine ⟨2843585346589588731781841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7582894257572236618084909 2843585346589588731781841)
                    ·
                      refine ⟨2132689009942191548836381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843585346589588731781841 2132689009942191548836381)
                      ·
                        rfl

theorem cell23_4153397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_4153397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153397 prefixEnd_4153397 := by exact prefixLift 4153397
  have htrace : WordTrace (prefixWord ++ tailWord_4153397) baseStart_4153397 baseEnd_4153397 := by
    simpa [prefixWord, tailWord_4153397, baseEnd_4153397] using wordTrace_append hprefix tailTrace_4153397
  have hstable : (prefixWord ++ tailWord_4153397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153397).length < 2 ^ (prefixWord ++ tailWord_4153397).sum := by decide
  have hdescent : baseEnd_4153397 < baseStart_4153397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153404 : List Nat := [2, 2, 2, 2, 2, 1, 3, 4, 1, 1, 3]
def baseStart_4153404 : Nat := 118140960795 + 4153404 * 2 ^ 59
def prefixEnd_4153404 : Nat := 4983230072969 + 3 ^ 40 * 4153404 * 2
def baseEnd_4153404 : Nat := 2132692604306773021448849

theorem tailTrace_4153404 : CollatzResearch.WordTrace tailWord_4153404 prefixEnd_4153404 2132692604306773021448849 := by
  unfold tailWord_4153404
  simp only [CollatzResearch.WordTrace]
  refine ⟨75743544522467063887237633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100991392696622751849650177 75743544522467063887237633)
  ·
    refine ⟨56807658391850297915428225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75743544522467063887237633 56807658391850297915428225)
    ·
      refine ⟨42605743793887723436571169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56807658391850297915428225 42605743793887723436571169)
      ·
        refine ⟨31954307845415792577428377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42605743793887723436571169 31954307845415792577428377)
        ·
          refine ⟨23965730884061844433071283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31954307845415792577428377 23965730884061844433071283)
          ·
            refine ⟨35948596326092766649606925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23965730884061844433071283 35948596326092766649606925)
            ·
              refine ⟨13480723622284787493602597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35948596326092766649606925 13480723622284787493602597)
              ·
                refine ⟨2527635679178397655050487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13480723622284787493602597 2527635679178397655050487)
                ·
                  refine ⟨3791453518767596482575731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527635679178397655050487 3791453518767596482575731)
                  ·
                    refine ⟨5687180278151394723863597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3791453518767596482575731 5687180278151394723863597)
                    ·
                      refine ⟨2132692604306773021448849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5687180278151394723863597 2132692604306773021448849)
                      ·
                        rfl

theorem cell23_4153404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_4153404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153404 prefixEnd_4153404 := by exact prefixLift 4153404
  have htrace : WordTrace (prefixWord ++ tailWord_4153404) baseStart_4153404 baseEnd_4153404 := by
    simpa [prefixWord, tailWord_4153404, baseEnd_4153404] using wordTrace_append hprefix tailTrace_4153404
  have hstable : (prefixWord ++ tailWord_4153404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153404).length < 2 ^ (prefixWord ++ tailWord_4153404).sum := by decide
  have hdescent : baseEnd_4153404 < baseStart_4153404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153413 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_4153413 : Nat := 118140960795 + 4153413 * 2 ^ 59
def prefixEnd_4153413 : Nat := 4983230072969 + 3 ^ 40 * 4153413 * 2
def baseEnd_4153413 : Nat := 2132697225632663486236307

theorem tailTrace_4153413 : CollatzResearch.WordTrace tailWord_4153413 prefixEnd_4153413 2132697225632663486236307 := by
  unfold tailWord_4153413
  simp only [CollatzResearch.WordTrace]
  refine ⟨151487417301901522311552893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100991611534601014874368595 151487417301901522311552893)
  ·
    refine ⟨56807781488213070866832335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151487417301901522311552893 56807781488213070866832335)
    ·
      refine ⟨85211672232319606300248503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56807781488213070866832335 85211672232319606300248503)
      ·
        refine ⟨127817508348479409450372755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85211672232319606300248503 127817508348479409450372755)
        ·
          refine ⟨191726262522719114175559133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127817508348479409450372755 191726262522719114175559133)
          ·
            refine ⟨71897348446019667815834675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191726262522719114175559133 71897348446019667815834675)
            ·
              refine ⟨107846022669029501723752013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71897348446019667815834675 107846022669029501723752013)
              ·
                refine ⟨40442258500886063146407005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107846022669029501723752013 40442258500886063146407005)
                ·
                  refine ⟨15165846937832273679902627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40442258500886063146407005 15165846937832273679902627)
                  ·
                    refine ⟨22748770406748410519853941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15165846937832273679902627 22748770406748410519853941)
                    ·
                      refine ⟨2132697225632663486236307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22748770406748410519853941 2132697225632663486236307)
                      ·
                        rfl

theorem cell23_4153413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_4153413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153413 prefixEnd_4153413 := by exact prefixLift 4153413
  have htrace : WordTrace (prefixWord ++ tailWord_4153413) baseStart_4153413 baseEnd_4153413 := by
    simpa [prefixWord, tailWord_4153413, baseEnd_4153413] using wordTrace_append hprefix tailTrace_4153413
  have hstable : (prefixWord ++ tailWord_4153413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153413).length < 2 ^ (prefixWord ++ tailWord_4153413).sum := by decide
  have hdescent : baseEnd_4153413 < baseStart_4153413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153414 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_4153414 : Nat := 118140960795 + 4153414 * 2 ^ 59
def prefixEnd_4153414 : Nat := 4983230072969 + 3 ^ 40 * 4153414 * 2
def baseEnd_4153414 : Nat := 2132697739113317982323803

theorem tailTrace_4153414 : CollatzResearch.WordTrace tailWord_4153414 prefixEnd_4153414 2132697739113317982323803 := by
  unfold tailWord_4153414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4733982930465559358823103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100991635849931932988226197 4733982930465559358823103)
  ·
    refine ⟨7100974395698339038234655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4733982930465559358823103 7100974395698339038234655)
    ·
      refine ⟨10651461593547508557351983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7100974395698339038234655 10651461593547508557351983)
      ·
        refine ⟨15977192390321262836027975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10651461593547508557351983 15977192390321262836027975)
        ·
          refine ⟨23965788585481894254041963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15977192390321262836027975 23965788585481894254041963)
          ·
            refine ⟨35948682878222841381062945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23965788585481894254041963 35948682878222841381062945)
            ·
              refine ⟨26961512158667131035797209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35948682878222841381062945 26961512158667131035797209)
              ·
                refine ⟨20221134119000348276847907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26961512158667131035797209 20221134119000348276847907)
                ·
                  refine ⟨30331701178500522415271861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20221134119000348276847907 30331701178500522415271861)
                  ·
                    refine ⟨2843596985484423976431737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30331701178500522415271861 2843596985484423976431737)
                    ·
                      refine ⟨2132697739113317982323803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843596985484423976431737 2132697739113317982323803)
                      ·
                        rfl

theorem cell23_4153414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_4153414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153414 prefixEnd_4153414 := by exact prefixLift 4153414
  have htrace : WordTrace (prefixWord ++ tailWord_4153414) baseStart_4153414 baseEnd_4153414 := by
    simpa [prefixWord, tailWord_4153414, baseEnd_4153414] using wordTrace_append hprefix tailTrace_4153414
  have hstable : (prefixWord ++ tailWord_4153414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153414).length < 2 ^ (prefixWord ++ tailWord_4153414).sum := by decide
  have hdescent : baseEnd_4153414 < baseStart_4153414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153423 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_4153423 : Nat := 118140960795 + 4153423 * 2 ^ 59
def prefixEnd_4153423 : Nat := 4983230072969 + 3 ^ 40 * 4153423 * 2
def baseEnd_4153423 : Nat := 2132702360439208447111261

theorem tailTrace_4153423 : CollatzResearch.WordTrace tailWord_4153423 prefixEnd_4153423 2132702360439208447111261 := by
  unfold tailWord_4153423
  simp only [CollatzResearch.WordTrace]
  refine ⟨151487782031865294019416923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100991854687910196012944615 151487782031865294019416923)
  ·
    refine ⟨227231673047797941029125385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151487782031865294019416923 227231673047797941029125385)
    ·
      refine ⟨170423754785848455771844039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227231673047797941029125385 170423754785848455771844039)
      ·
        refine ⟨255635632178772683657766059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170423754785848455771844039 255635632178772683657766059)
        ·
          refine ⟨383453448268159025486649089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255635632178772683657766059 383453448268159025486649089)
          ·
            refine ⟨287590086201119269114986817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383453448268159025486649089 287590086201119269114986817)
            ·
              refine ⟨215692564650839451836240113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287590086201119269114986817 215692564650839451836240113)
              ·
                refine ⟨161769423488129588877180085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215692564650839451836240113 161769423488129588877180085)
                ·
                  refine ⟨15165883452012148957235633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161769423488129588877180085 15165883452012148957235633)
                  ·
                    refine ⟨11374412589009111717926725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15165883452012148957235633 11374412589009111717926725)
                    ·
                      refine ⟨2132702360439208447111261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11374412589009111717926725 2132702360439208447111261)
                      ·
                        rfl

theorem cell23_4153423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_4153423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153423 prefixEnd_4153423 := by exact prefixLift 4153423
  have htrace : WordTrace (prefixWord ++ tailWord_4153423) baseStart_4153423 baseEnd_4153423 := by
    simpa [prefixWord, tailWord_4153423, baseEnd_4153423] using wordTrace_append hprefix tailTrace_4153423
  have hstable : (prefixWord ++ tailWord_4153423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153423).length < 2 ^ (prefixWord ++ tailWord_4153423).sum := by decide
  have hdescent : baseEnd_4153423 < baseStart_4153423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153437 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_4153437 : Nat := 118140960795 + 4153437 * 2 ^ 59
def prefixEnd_4153437 : Nat := 4983230072969 + 3 ^ 40 * 4153437 * 2
def baseEnd_4153437 : Nat := 710903183056123797445399

theorem tailTrace_4153437 : CollatzResearch.WordTrace tailWord_4153437 prefixEnd_4153437 710903183056123797445399 := by
  unfold tailWord_4153437
  simp only [CollatzResearch.WordTrace]
  refine ⟨151488292653814574410426565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100992195102543049606951043 151488292653814574410426565)
  ·
    refine ⟨28404054872590232701954981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151488292653814574410426565 28404054872590232701954981)
    ·
      refine ⟨5325760288610668631616559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28404054872590232701954981 5325760288610668631616559)
      ·
        refine ⟨7988640432916002947424839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5325760288610668631616559 7988640432916002947424839)
        ·
          refine ⟨11982960649374004421137259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7988640432916002947424839 11982960649374004421137259)
          ·
            refine ⟨17974440974061006631705889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11982960649374004421137259 17974440974061006631705889)
            ·
              refine ⟨13480830730545754973779417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17974440974061006631705889 13480830730545754973779417)
              ·
                refine ⟨10110623047909316230334563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13480830730545754973779417 10110623047909316230334563)
                ·
                  refine ⟨15165934571863974345501845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10110623047909316230334563 15165934571863974345501845)
                  ·
                    refine ⟨710903183056123797445399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15165934571863974345501845 710903183056123797445399)
                    ·
                      rfl

theorem cell23_4153437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_4153437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153437 prefixEnd_4153437 := by exact prefixLift 4153437
  have htrace : WordTrace (prefixWord ++ tailWord_4153437) baseStart_4153437 baseEnd_4153437 := by
    simpa [prefixWord, tailWord_4153437, baseEnd_4153437] using wordTrace_append hprefix tailTrace_4153437
  have hstable : (prefixWord ++ tailWord_4153437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153437).length < 2 ^ (prefixWord ++ tailWord_4153437).sum := by decide
  have hdescent : baseEnd_4153437 < baseStart_4153437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153440 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 4]
def baseStart_4153440 : Nat := 118140960795 + 4153440 * 2 ^ 59
def prefixEnd_4153440 : Nat := 4983230072969 + 3 ^ 40 * 4153440 * 2
def baseEnd_4153440 : Nat := 2132711089610334880598683

theorem tailTrace_4153440 : CollatzResearch.WordTrace tailWord_4153440 prefixEnd_4153440 2132711089610334880598683 := by
  unfold tailWord_4153440
  simp only [CollatzResearch.WordTrace]
  refine ⟨75744201036401852961392887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100992268048535803948523849 75744201036401852961392887)
  ·
    refine ⟨113616301554602779442089331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75744201036401852961392887 113616301554602779442089331)
    ·
      refine ⟨170424452331904169163133997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113616301554602779442089331 170424452331904169163133997)
      ·
        refine ⟨63909169624464063436175249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170424452331904169163133997 63909169624464063436175249)
        ·
          refine ⟨47931877218348047577131437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63909169624464063436175249 47931877218348047577131437)
          ·
            refine ⟨17974453956880517841424289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47931877218348047577131437 17974453956880517841424289)
            ·
              refine ⟨13480840467660388381068217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17974453956880517841424289 13480840467660388381068217)
              ·
                refine ⟨10110630350745291285801163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13480840467660388381068217 10110630350745291285801163)
                ·
                  refine ⟨15165945526117936928701745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10110630350745291285801163 15165945526117936928701745)
                  ·
                    refine ⟨11374459144588452696526309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15165945526117936928701745 11374459144588452696526309)
                    ·
                      refine ⟨2132711089610334880598683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11374459144588452696526309 2132711089610334880598683)
                      ·
                        rfl

theorem cell23_4153440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_4153440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153440 prefixEnd_4153440 := by exact prefixLift 4153440
  have htrace : WordTrace (prefixWord ++ tailWord_4153440) baseStart_4153440 baseEnd_4153440 := by
    simpa [prefixWord, tailWord_4153440, baseEnd_4153440] using wordTrace_append hprefix tailTrace_4153440
  have hstable : (prefixWord ++ tailWord_4153440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153440).length < 2 ^ (prefixWord ++ tailWord_4153440).sum := by decide
  have hdescent : baseEnd_4153440 < baseStart_4153440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153447 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_4153447 : Nat := 118140960795 + 4153447 * 2 ^ 59
def prefixEnd_4153447 : Nat := 4983230072969 + 3 ^ 40 * 4153447 * 2
def baseEnd_4153447 : Nat := 2132714683974916353211151

theorem tailTrace_4153447 : CollatzResearch.WordTrace tailWord_4153447 prefixEnd_4153447 2132714683974916353211151 := by
  unfold tailWord_4153447
  simp only [CollatzResearch.WordTrace]
  refine ⟨151488657383778346118290595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100992438255852230745527063 151488657383778346118290595)
  ·
    refine ⟨227232986075667519177435893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151488657383778346118290595 227232986075667519177435893)
    ·
      refine ⟨21303092444593829922884615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227232986075667519177435893 21303092444593829922884615)
      ·
        refine ⟨31954638666890744884326923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21303092444593829922884615 31954638666890744884326923)
        ·
          refine ⟨47931958000336117326490385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31954638666890744884326923 47931958000336117326490385)
          ·
            refine ⟨35948968500252087994867789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47931958000336117326490385 35948968500252087994867789)
            ·
              refine ⟨13480863187594532998075421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35948968500252087994867789 13480863187594532998075421)
              ·
                refine ⟨5055323695347949874278283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13480863187594532998075421 5055323695347949874278283)
                ·
                  refine ⟨7582985543021924811417425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055323695347949874278283 7582985543021924811417425)
                  ·
                    refine ⟨5687239157266443608563069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7582985543021924811417425 5687239157266443608563069)
                    ·
                      refine ⟨2132714683974916353211151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5687239157266443608563069 2132714683974916353211151)
                      ·
                        rfl

theorem cell23_4153447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_4153447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153447 prefixEnd_4153447 := by exact prefixLift 4153447
  have htrace : WordTrace (prefixWord ++ tailWord_4153447) baseStart_4153447 baseEnd_4153447 := by
    simpa [prefixWord, tailWord_4153447, baseEnd_4153447] using wordTrace_append hprefix tailTrace_4153447
  have hstable : (prefixWord ++ tailWord_4153447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153447).length < 2 ^ (prefixWord ++ tailWord_4153447).sum := by decide
  have hdescent : baseEnd_4153447 < baseStart_4153447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153450 : List Nat := [3, 1, 3, 2, 3, 1, 10]
def baseStart_4153450 : Nat := 118140960795 + 4153450 * 2 ^ 59
def prefixEnd_4153450 : Nat := 4983230072969 + 3 ^ 40 * 4153450 * 2
def baseEnd_4153450 : Nat := 26329829931072590635477

theorem tailTrace_4153450 : CollatzResearch.WordTrace tailWord_4153450 prefixEnd_4153450 26329829931072590635477 := by
  unfold tailWord_4153450
  simp only [CollatzResearch.WordTrace]
  refine ⟨37872191700691869407662451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100992511201844985087099869 37872191700691869407662451)
  ·
    refine ⟨56808287551037804111493677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37872191700691869407662451 56808287551037804111493677)
    ·
      refine ⟨21303107831639176541810129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56808287551037804111493677 21303107831639176541810129)
      ·
        refine ⟨15977330873729382406357597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21303107831639176541810129 15977330873729382406357597)
        ·
          refine ⟨5991499077648518402384099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15977330873729382406357597 5991499077648518402384099)
          ·
            refine ⟨8987248616472777603576149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991499077648518402384099 8987248616472777603576149)
            ·
              refine ⟨26329829931072590635477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8987248616472777603576149 26329829931072590635477)
              ·
                rfl

theorem cell23_4153450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 10].length) (baseStart_4153450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153450 prefixEnd_4153450 := by exact prefixLift 4153450
  have htrace : WordTrace (prefixWord ++ tailWord_4153450) baseStart_4153450 baseEnd_4153450 := by
    simpa [prefixWord, tailWord_4153450, baseEnd_4153450] using wordTrace_append hprefix tailTrace_4153450
  have hstable : (prefixWord ++ tailWord_4153450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153450).length < 2 ^ (prefixWord ++ tailWord_4153450).sum := by decide
  have hdescent : baseEnd_4153450 < baseStart_4153450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153477 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 1, 3, 3]
def baseStart_4153477 : Nat := 118140960795 + 4153477 * 2 ^ 59
def prefixEnd_4153477 : Nat := 4983230072969 + 3 ^ 40 * 4153477 * 2
def baseEnd_4153477 : Nat := 2132730088394551235836013

theorem tailTrace_4153477 : CollatzResearch.WordTrace tailWord_4153477 prefixEnd_4153477 2132730088394551235836013 := by
  unfold tailWord_4153477
  simp only [CollatzResearch.WordTrace]
  refine ⟨151489751573669661241882685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100993167715779774161255123 151489751573669661241882685)
  ·
    refine ⟨56808656840126122965706007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151489751573669661241882685 56808656840126122965706007)
    ·
      refine ⟨85212985260189184448559011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56808656840126122965706007 85212985260189184448559011)
      ·
        refine ⟨127819477890283776672838517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85212985260189184448559011 127819477890283776672838517)
        ·
          refine ⟨11983076052214104063078611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127819477890283776672838517 11983076052214104063078611)
          ·
            refine ⟨17974614078321156094617917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11983076052214104063078611 17974614078321156094617917)
            ·
              refine ⟨6740480279370433535481719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17974614078321156094617917 6740480279370433535481719)
              ·
                refine ⟨10110720419055650303222579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6740480279370433535481719 10110720419055650303222579)
                ·
                  refine ⟨15166080628583475454833869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10110720419055650303222579 15166080628583475454833869)
                  ·
                    refine ⟨5687280235718803295562701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15166080628583475454833869 5687280235718803295562701)
                    ·
                      refine ⟨2132730088394551235836013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5687280235718803295562701 2132730088394551235836013)
                      ·
                        rfl

theorem cell23_4153477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_4153477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153477 prefixEnd_4153477 := by exact prefixLift 4153477
  have htrace : WordTrace (prefixWord ++ tailWord_4153477) baseStart_4153477 baseEnd_4153477 := by
    simpa [prefixWord, tailWord_4153477, baseEnd_4153477] using wordTrace_append hprefix tailTrace_4153477
  have hstable : (prefixWord ++ tailWord_4153477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153477).length < 2 ^ (prefixWord ++ tailWord_4153477).sum := by decide
  have hdescent : baseEnd_4153477 < baseStart_4153477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153490 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4153490 : Nat := 118140960795 + 4153490 * 2 ^ 59
def prefixEnd_4153490 : Nat := 4983230072969 + 3 ^ 40 * 4153490 * 2
def baseEnd_4153490 : Nat := 2132736763643059684973453

theorem tailTrace_4153490 : CollatzResearch.WordTrace tailWord_4153490 prefixEnd_4153490 2132736763643059684973453 := by
  unfold tailWord_4153490
  simp only [CollatzResearch.WordTrace]
  refine ⟨37872556430655641115526481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100993483815081709641403949 37872556430655641115526481)
  ·
    refine ⟨28404417322991730836644861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37872556430655641115526481 28404417322991730836644861)
    ·
      refine ⟨10651656496121899063741823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28404417322991730836644861 10651656496121899063741823)
      ·
        refine ⟨15977484744182848595612735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10651656496121899063741823 15977484744182848595612735)
        ·
          refine ⟨23966227116274272893419103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15977484744182848595612735 23966227116274272893419103)
          ·
            refine ⟨35949340674411409340128655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23966227116274272893419103 35949340674411409340128655)
            ·
              refine ⟨53924011011617114010192983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35949340674411409340128655 53924011011617114010192983)
              ·
                refine ⟨80886016517425671015289475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53924011011617114010192983 80886016517425671015289475)
                ·
                  refine ⟨121329024776138506522934213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80886016517425671015289475 121329024776138506522934213)
                  ·
                    refine ⟨22749192145525969973050165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121329024776138506522934213 22749192145525969973050165)
                    ·
                      refine ⟨2132736763643059684973453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22749192145525969973050165 2132736763643059684973453)
                      ·
                        rfl

theorem cell23_4153490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4153490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153490 prefixEnd_4153490 := by exact prefixLift 4153490
  have htrace : WordTrace (prefixWord ++ tailWord_4153490) baseStart_4153490 baseEnd_4153490 := by
    simpa [prefixWord, tailWord_4153490, baseEnd_4153490] using wordTrace_append hprefix tailTrace_4153490
  have hstable : (prefixWord ++ tailWord_4153490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153490).length < 2 ^ (prefixWord ++ tailWord_4153490).sum := by decide
  have hdescent : baseEnd_4153490 < baseStart_4153490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153495 : List Nat := [1, 1, 3, 3, 5, 1, 1, 3, 1, 2, 2]
def baseStart_4153495 : Nat := 118140960795 + 4153495 * 2 ^ 59
def prefixEnd_4153495 : Nat := 4983230072969 + 3 ^ 40 * 4153495 * 2
def baseEnd_4153495 : Nat := 2132739331046332165410931

theorem tailTrace_4153495 : CollatzResearch.WordTrace tailWord_4153495 prefixEnd_4153495 2132739331046332165410931 := by
  unfold tailWord_4153495
  simp only [CollatzResearch.WordTrace]
  refine ⟨151490408087604450316037939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100993605391736300210691959 151490408087604450316037939)
  ·
    refine ⟨227235612131406675474056909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151490408087604450316037939 227235612131406675474056909)
    ·
      refine ⟨85213354549277503302771341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227235612131406675474056909 85213354549277503302771341)
      ·
        refine ⟨31955007955979063738539253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85213354549277503302771341 31955007955979063738539253)
        ·
          refine ⟨2995781995873037225488055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31955007955979063738539253 2995781995873037225488055)
          ·
            refine ⟨4493672993809555838232083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995781995873037225488055 4493672993809555838232083)
            ·
              refine ⟨6740509490714333757348125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4493672993809555838232083 6740509490714333757348125)
              ·
                refine ⟨2527691059017875159005547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6740509490714333757348125 2527691059017875159005547)
                ·
                  refine ⟨3791536588526812738508321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527691059017875159005547 3791536588526812738508321)
                  ·
                    refine ⟨2843652441395109553881241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3791536588526812738508321 2843652441395109553881241)
                    ·
                      refine ⟨2132739331046332165410931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843652441395109553881241 2132739331046332165410931)
                      ·
                        rfl

theorem cell23_4153495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_4153495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153495 prefixEnd_4153495 := by exact prefixLift 4153495
  have htrace : WordTrace (prefixWord ++ tailWord_4153495) baseStart_4153495 baseEnd_4153495 := by
    simpa [prefixWord, tailWord_4153495, baseEnd_4153495] using wordTrace_append hprefix tailTrace_4153495
  have hstable : (prefixWord ++ tailWord_4153495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153495).length < 2 ^ (prefixWord ++ tailWord_4153495).sum := by decide
  have hdescent : baseEnd_4153495 < baseStart_4153495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153504 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 1, 3, 2]
def baseStart_4153504 : Nat := 118140960795 + 4153504 * 2 ^ 59
def prefixEnd_4153504 : Nat := 4983230072969 + 3 ^ 40 * 4153504 * 2
def baseEnd_4153504 : Nat := 2132743952372222630198389

theorem tailTrace_4153504 : CollatzResearch.WordTrace tailWord_4153504 prefixEnd_4153504 2132743952372222630198389 := by
  unfold tailWord_4153504
  simp only [CollatzResearch.WordTrace]
  refine ⟨75745368172285922426557783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100993824229714563235410377 75745368172285922426557783)
  ·
    refine ⟨113618052258428883639836675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75745368172285922426557783 113618052258428883639836675)
    ·
      refine ⟨170427078387643325459755013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113618052258428883639836675 170427078387643325459755013)
      ·
        refine ⟨31955077197683123523704065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170427078387643325459755013 31955077197683123523704065)
        ·
          refine ⟨23966307898262342642778049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31955077197683123523704065 23966307898262342642778049)
          ·
            refine ⟨17974730923696756982083537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23966307898262342642778049 17974730923696756982083537)
            ·
              refine ⟨13481048192772567736562653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17974730923696756982083537 13481048192772567736562653)
              ·
                refine ⟨5055393072289712901210995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13481048192772567736562653 5055393072289712901210995)
                ·
                  refine ⟨7583089608434569351816493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055393072289712901210995 7583089608434569351816493)
                  ·
                    refine ⟨2843658603162963506931185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7583089608434569351816493 2843658603162963506931185)
                    ·
                      refine ⟨2132743952372222630198389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843658603162963506931185 2132743952372222630198389)
                      ·
                        rfl

theorem cell23_4153504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_4153504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153504 prefixEnd_4153504 := by exact prefixLift 4153504
  have htrace : WordTrace (prefixWord ++ tailWord_4153504) baseStart_4153504 baseEnd_4153504 := by
    simpa [prefixWord, tailWord_4153504, baseEnd_4153504] using wordTrace_append hprefix tailTrace_4153504
  have hstable : (prefixWord ++ tailWord_4153504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153504).length < 2 ^ (prefixWord ++ tailWord_4153504).sum := by decide
  have hdescent : baseEnd_4153504 < baseStart_4153504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153530 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_4153530 : Nat := 118140960795 + 4153530 * 2 ^ 59
def prefixEnd_4153530 : Nat := 4983230072969 + 3 ^ 40 * 4153530 * 2
def baseEnd_4153530 : Nat := 2132757302869239528473269

theorem tailTrace_4153530 : CollatzResearch.WordTrace tailWord_4153530 prefixEnd_4153530 2132757302869239528473269 := by
  unfold tailWord_4153530
  simp only [CollatzResearch.WordTrace]
  refine ⟨37872921160619412823390511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100994456428318434195708029 37872921160619412823390511)
  ·
    refine ⟨56809381740929119235085767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37872921160619412823390511 56809381740929119235085767)
    ·
      refine ⟨85214072611393678852628651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56809381740929119235085767 85214072611393678852628651)
      ·
        refine ⟨127821108917090518278942977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85214072611393678852628651 127821108917090518278942977)
        ·
          refine ⟨95865831687817888709207233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127821108917090518278942977 95865831687817888709207233)
          ·
            refine ⟨71899373765863416531905425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95865831687817888709207233 71899373765863416531905425)
            ·
              refine ⟨53924530324397562398929069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71899373765863416531905425 53924530324397562398929069)
              ·
                refine ⟨20221698871649085899598401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53924530324397562398929069 20221698871649085899598401)
                ·
                  refine ⟨15166274153736814424698801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20221698871649085899598401 15166274153736814424698801)
                  ·
                    refine ⟨11374705615302610818524101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15166274153736814424698801 11374705615302610818524101)
                    ·
                      refine ⟨2132757302869239528473269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11374705615302610818524101 2132757302869239528473269)
                      ·
                        rfl

theorem cell23_4153530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_4153530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153530 prefixEnd_4153530 := by exact prefixLift 4153530
  have htrace : WordTrace (prefixWord ++ tailWord_4153530) baseStart_4153530 baseEnd_4153530 := by
    simpa [prefixWord, tailWord_4153530, baseEnd_4153530] using wordTrace_append hprefix tailTrace_4153530
  have hstable : (prefixWord ++ tailWord_4153530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153530).length < 2 ^ (prefixWord ++ tailWord_4153530).sum := by decide
  have hdescent : baseEnd_4153530 < baseStart_4153530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153538 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_4153538 : Nat := 118140960795 + 4153538 * 2 ^ 59
def prefixEnd_4153538 : Nat := 4983230072969 + 3 ^ 40 * 4153538 * 2
def baseEnd_4153538 : Nat := 2132761410714475497173233

theorem tailTrace_4153538 : CollatzResearch.WordTrace tailWord_4153538 prefixEnd_4153538 2132761410714475497173233 := by
  unfold tailWord_4153538
  simp only [CollatzResearch.WordTrace]
  refine ⟨37872994106612167164963317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100994650950965779106568845 37872994106612167164963317)
  ·
    refine ⟨3550593197494890671715311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37872994106612167164963317 3550593197494890671715311)
    ·
      refine ⟨5325889796242336007572967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3550593197494890671715311 5325889796242336007572967)
      ·
        refine ⟨7988834694363504011359451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5325889796242336007572967 7988834694363504011359451)
        ·
          refine ⟨11983252041545256017039177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7988834694363504011359451 11983252041545256017039177)
          ·
            refine ⟨8987439031158942012779383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11983252041545256017039177 8987439031158942012779383)
            ·
              refine ⟨13481158546738413019169075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8987439031158942012779383 13481158546738413019169075)
              ·
                refine ⟨20221737820107619528753613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13481158546738413019169075 20221737820107619528753613)
                ·
                  refine ⟨7583151682540357323282605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20221737820107619528753613 7583151682540357323282605)
                  ·
                    refine ⟨2843681880952633996230977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7583151682540357323282605 2843681880952633996230977)
                    ·
                      refine ⟨2132761410714475497173233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843681880952633996230977 2132761410714475497173233)
                      ·
                        rfl

theorem cell23_4153538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_4153538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153538 prefixEnd_4153538 := by exact prefixLift 4153538
  have htrace : WordTrace (prefixWord ++ tailWord_4153538) baseStart_4153538 baseEnd_4153538 := by
    simpa [prefixWord, tailWord_4153538, baseEnd_4153538] using wordTrace_append hprefix tailTrace_4153538
  have hstable : (prefixWord ++ tailWord_4153538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153538).length < 2 ^ (prefixWord ++ tailWord_4153538).sum := by decide
  have hdescent : baseEnd_4153538 < baseStart_4153538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153580 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_4153580 : Nat := 118140960795 + 4153580 * 2 ^ 59
def prefixEnd_4153580 : Nat := 4983230072969 + 3 ^ 40 * 4153580 * 2
def baseEnd_4153580 : Nat := 2132782976901964332848039

theorem tailTrace_4153580 : CollatzResearch.WordTrace tailWord_4153580 prefixEnd_4153580 2132782976901964332848039 := by
  unfold tailWord_4153580
  simp only [CollatzResearch.WordTrace]
  refine ⟨75746754146148254916441097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100995672194864339888588129 75746754146148254916441097)
  ·
    refine ⟨56810065609611191187330823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75746754146148254916441097 56810065609611191187330823)
    ·
      refine ⟨85215098414416786780996235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56810065609611191187330823 85215098414416786780996235)
      ·
        refine ⟨127822647621625180171494353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85215098414416786780996235 127822647621625180171494353)
        ·
          refine ⟨95866985716218885128620765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127822647621625180171494353 95866985716218885128620765)
          ·
            refine ⟨35950119643582081923232787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95866985716218885128620765 35950119643582081923232787)
            ·
              refine ⟨53925179465373122884849181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35950119643582081923232787 53925179465373122884849181)
              ·
                refine ⟨20221942299514921081818443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53925179465373122884849181 20221942299514921081818443)
                ·
                  refine ⟨30332913449272381622727665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20221942299514921081818443 30332913449272381622727665)
                  ·
                    refine ⟨22749685086954286217045749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30332913449272381622727665 22749685086954286217045749)
                    ·
                      refine ⟨2132782976901964332848039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22749685086954286217045749 2132782976901964332848039)
                      ·
                        rfl

theorem cell23_4153580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_4153580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153580 prefixEnd_4153580 := by exact prefixLift 4153580
  have htrace : WordTrace (prefixWord ++ tailWord_4153580) baseStart_4153580 baseEnd_4153580 := by
    simpa [prefixWord, tailWord_4153580, baseEnd_4153580] using wordTrace_append hprefix tailTrace_4153580
  have hstable : (prefixWord ++ tailWord_4153580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153580).length < 2 ^ (prefixWord ++ tailWord_4153580).sum := by decide
  have hdescent : baseEnd_4153580 < baseStart_4153580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153627 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 3]
def baseStart_4153627 : Nat := 118140960795 + 4153627 * 2 ^ 59
def prefixEnd_4153627 : Nat := 4983230072969 + 3 ^ 40 * 4153627 * 2
def baseEnd_4153627 : Nat := 2132807110492725648960323

theorem tailTrace_4153627 : CollatzResearch.WordTrace tailWord_4153627 prefixEnd_4153627 2132807110492725648960323 := by
  unfold tailWord_4153627
  simp only [CollatzResearch.WordTrace]
  refine ⟨151495222523126236859843135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100996815015417491239895423 151495222523126236859843135)
  ·
    refine ⟨227242833784689355289764703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151495222523126236859843135 227242833784689355289764703)
    ·
      refine ⟨340864250677034032934647055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227242833784689355289764703 340864250677034032934647055)
      ·
        refine ⟨511296376015551049401970583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340864250677034032934647055 511296376015551049401970583)
        ·
          refine ⟨766944564023326574102955875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511296376015551049401970583 766944564023326574102955875)
          ·
            refine ⟨1150416846034989861154433813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766944564023326574102955875 1150416846034989861154433813)
            ·
              refine ⟨53925789657890149741614085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1150416846034989861154433813 53925789657890149741614085)
              ·
                refine ⟨10111085560854403076552641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53925789657890149741614085 10111085560854403076552641)
                ·
                  refine ⟨7583314170640802307414481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10111085560854403076552641 7583314170640802307414481)
                  ·
                    refine ⟨5687485627980601730560861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7583314170640802307414481 5687485627980601730560861)
                    ·
                      refine ⟨2132807110492725648960323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5687485627980601730560861 2132807110492725648960323)
                      ·
                        rfl

theorem cell23_4153627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 3].length) (baseStart_4153627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153627 prefixEnd_4153627 := by exact prefixLift 4153627
  have htrace : WordTrace (prefixWord ++ tailWord_4153627) baseStart_4153627 baseEnd_4153627 := by
    simpa [prefixWord, tailWord_4153627, baseEnd_4153627] using wordTrace_append hprefix tailTrace_4153627
  have hstable : (prefixWord ++ tailWord_4153627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153627).length < 2 ^ (prefixWord ++ tailWord_4153627).sum := by decide
  have hdescent : baseEnd_4153627 < baseStart_4153627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153634 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_4153634 : Nat := 118140960795 + 4153634 * 2 ^ 59
def prefixEnd_4153634 : Nat := 4983230072969 + 3 ^ 40 * 4153634 * 2
def baseEnd_4153634 : Nat := 710936901619102373857597

theorem tailTrace_4153634 : CollatzResearch.WordTrace tailWord_4153634 prefixEnd_4153634 710936901619102373857597 := by
  unfold tailWord_4153634
  simp only [CollatzResearch.WordTrace]
  refine ⟨37873869458525219263836989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100996985222733918036898637 37873869458525219263836989)
  ·
    refine ⟨14202701046946957223938871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37873869458525219263836989 14202701046946957223938871)
    ·
      refine ⟨21304051570420435835908307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14202701046946957223938871 21304051570420435835908307)
      ·
        refine ⟨31956077355630653753862461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21304051570420435835908307 31956077355630653753862461)
        ·
          refine ⟨11983529008361495157698423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31956077355630653753862461 11983529008361495157698423)
          ·
            refine ⟨17975293512542242736547635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11983529008361495157698423 17975293512542242736547635)
            ·
              refine ⟨26962940268813364104821453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17975293512542242736547635 26962940268813364104821453)
              ·
                refine ⟨10111102600805011539308045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26962940268813364104821453 10111102600805011539308045)
                ·
                  refine ⟨3791663475301879327240517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10111102600805011539308045 3791663475301879327240517)
                  ·
                    refine ⟨710936901619102373857597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3791663475301879327240517 710936901619102373857597)
                    ·
                      rfl

theorem cell23_4153634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_4153634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153634 prefixEnd_4153634 := by exact prefixLift 4153634
  have htrace : WordTrace (prefixWord ++ tailWord_4153634) baseStart_4153634 baseEnd_4153634 := by
    simpa [prefixWord, tailWord_4153634, baseEnd_4153634] using wordTrace_append hprefix tailTrace_4153634
  have hstable : (prefixWord ++ tailWord_4153634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153634).length < 2 ^ (prefixWord ++ tailWord_4153634).sum := by decide
  have hdescent : baseEnd_4153634 < baseStart_4153634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153714 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_4153714 : Nat := 118140960795 + 4153714 * 2 ^ 59
def prefixEnd_4153714 : Nat := 4983230072969 + 3 ^ 40 * 4153714 * 2
def baseEnd_4153714 : Nat := 2132851783309666808572423

theorem tailTrace_4153714 : CollatzResearch.WordTrace tailWord_4153714 prefixEnd_4153714 2132851783309666808572423 := by
  unfold tailWord_4153714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37874598918452762679565049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100998930449207367145506797 37874598918452762679565049)
  ·
    refine ⟨28405949188839572009673787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37874598918452762679565049 28405949188839572009673787)
    ·
      refine ⟨42608923783259358014510681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28405949188839572009673787 42608923783259358014510681)
      ·
        refine ⟨31956692837444518510883011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42608923783259358014510681 31956692837444518510883011)
        ·
          refine ⟨47935039256166777766324517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31956692837444518510883011 47935039256166777766324517)
          ·
            refine ⟨8987819860531270831185847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47935039256166777766324517 8987819860531270831185847)
            ·
              refine ⟨13481729790796906246778771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8987819860531270831185847 13481729790796906246778771)
              ·
                refine ⟨20222594686195359370168157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13481729790796906246778771 20222594686195359370168157)
                ·
                  refine ⟨7583473007323259763813059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20222594686195359370168157 7583473007323259763813059)
                  ·
                    refine ⟨11375209510984889645719589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7583473007323259763813059 11375209510984889645719589)
                    ·
                      refine ⟨2132851783309666808572423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11375209510984889645719589 2132851783309666808572423)
                      ·
                        rfl

theorem cell23_4153714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_4153714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153714 prefixEnd_4153714 := by exact prefixLift 4153714
  have htrace : WordTrace (prefixWord ++ tailWord_4153714) baseStart_4153714 baseEnd_4153714 := by
    simpa [prefixWord, tailWord_4153714, baseEnd_4153714] using wordTrace_append hprefix tailTrace_4153714
  have hstable : (prefixWord ++ tailWord_4153714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153714).length < 2 ^ (prefixWord ++ tailWord_4153714).sum := by decide
  have hdescent : baseEnd_4153714 < baseStart_4153714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153727 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 4]
def baseStart_4153727 : Nat := 118140960795 + 4153727 * 2 ^ 59
def prefixEnd_4153727 : Nat := 4983230072969 + 3 ^ 40 * 4153727 * 2
def baseEnd_4153727 : Nat := 2132858458558175257709863

theorem tailTrace_4153727 : CollatzResearch.WordTrace tailWord_4153727 prefixEnd_4153727 2132858458558175257709863 := by
  unfold tailWord_4153727
  simp only [CollatzResearch.WordTrace]
  refine ⟨151498869822763953938483435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100999246548509302625655623 151498869822763953938483435)
  ·
    refine ⟨227248304734145930907725153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151498869822763953938483435 227248304734145930907725153)
    ·
      refine ⟨170436228550609448180793865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227248304734145930907725153 170436228550609448180793865)
      ·
        refine ⟨127827171412957086135595399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170436228550609448180793865 127827171412957086135595399)
        ·
          refine ⟨191740757119435629203393099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127827171412957086135595399 191740757119435629203393099)
          ·
            refine ⟨287611135679153443805089649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191740757119435629203393099 287611135679153443805089649)
            ·
              refine ⟨215708351759365082853817237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287611135679153443805089649 215708351759365082853817237)
              ·
                refine ⟨10111328988720238258772683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215708351759365082853817237 10111328988720238258772683)
                ·
                  refine ⟨15166993483080357388159025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10111328988720238258772683 15166993483080357388159025)
                  ·
                    refine ⟨11375245112310268041119269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15166993483080357388159025 11375245112310268041119269)
                    ·
                      refine ⟨2132858458558175257709863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11375245112310268041119269 2132858458558175257709863)
                      ·
                        rfl

theorem cell23_4153727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_4153727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153727 prefixEnd_4153727 := by exact prefixLift 4153727
  have htrace : WordTrace (prefixWord ++ tailWord_4153727) baseStart_4153727 baseEnd_4153727 := by
    simpa [prefixWord, tailWord_4153727, baseEnd_4153727] using wordTrace_append hprefix tailTrace_4153727
  have hstable : (prefixWord ++ tailWord_4153727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153727).length < 2 ^ (prefixWord ++ tailWord_4153727).sum := by decide
  have hdescent : baseEnd_4153727 < baseStart_4153727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153742 : List Nat := [4, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4153742 : Nat := 118140960795 + 4153742 * 2 ^ 59
def prefixEnd_4153742 : Nat := 4983230072969 + 3 ^ 40 * 4153742 * 2
def baseEnd_4153742 : Nat := 2132866160767992699022295

theorem tailTrace_4153742 : CollatzResearch.WordTrace tailWord_4153742 prefixEnd_4153742 2132866160767992699022295 := by
  unfold tailWord_4153742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18937427114713701437534935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100999611278473074333519653 18937427114713701437534935)
  ·
    refine ⟨28406140672070552156302403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18937427114713701437534935 28406140672070552156302403)
    ·
      refine ⟨42609211008105828234453605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28406140672070552156302403 42609211008105828234453605)
      ·
        refine ⟨7989227064019842793960051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42609211008105828234453605 7989227064019842793960051)
        ·
          refine ⟨11983840596029764190940077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7989227064019842793960051 11983840596029764190940077)
          ·
            refine ⟨4493940223511161571602529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11983840596029764190940077 4493940223511161571602529)
            ·
              refine ⟨3370455167633371178701897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4493940223511161571602529 3370455167633371178701897)
              ·
                refine ⟨2527841375725028384026423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3370455167633371178701897 2527841375725028384026423)
                ·
                  refine ⟨3791762063587542576039635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527841375725028384026423 3791762063587542576039635)
                  ·
                    refine ⟨5687643095381313864059453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3791762063587542576039635 5687643095381313864059453)
                    ·
                      refine ⟨2132866160767992699022295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5687643095381313864059453 2132866160767992699022295)
                      ·
                        rfl

theorem cell23_4153742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4153742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153742 prefixEnd_4153742 := by exact prefixLift 4153742
  have htrace : WordTrace (prefixWord ++ tailWord_4153742) baseStart_4153742 baseEnd_4153742 := by
    simpa [prefixWord, tailWord_4153742, baseEnd_4153742] using wordTrace_append hprefix tailTrace_4153742
  have hstable : (prefixWord ++ tailWord_4153742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153742).length < 2 ^ (prefixWord ++ tailWord_4153742).sum := by decide
  have hdescent : baseEnd_4153742 < baseStart_4153742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153754 : List Nat := [3, 1, 1, 4, 1, 4, 1, 8]
def baseStart_4153754 : Nat := 118140960795 + 4153754 * 2 ^ 59
def prefixEnd_4153754 : Nat := 4983230072969 + 3 ^ 40 * 4153754 * 2
def baseEnd_4153754 : Nat := 78995271205031357484157

theorem tailTrace_4153754 : CollatzResearch.WordTrace tailWord_4153754 prefixEnd_4153754 78995271205031357484157 := by
  unfold tailWord_4153754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37874963648416534387429079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100999903062444091699810877 37874963648416534387429079)
  ·
    refine ⟨56812445472624801581143619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37874963648416534387429079 56812445472624801581143619)
    ·
      refine ⟨85218668208937202371715429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56812445472624801581143619 85218668208937202371715429)
      ·
        refine ⟨15978500289175725444696643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85218668208937202371715429 15978500289175725444696643)
        ·
          refine ⟨23967750433763588167044965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15978500289175725444696643 23967750433763588167044965)
          ·
            refine ⟨4493953206330672781320931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23967750433763588167044965 4493953206330672781320931)
            ·
              refine ⟨6740929809496009171981397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4493953206330672781320931 6740929809496009171981397)
              ·
                refine ⟨78995271205031357484157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6740929809496009171981397 78995271205031357484157)
                ·
                  rfl

theorem cell23_4153754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 8].length) (baseStart_4153754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153754 prefixEnd_4153754 := by exact prefixLift 4153754
  have htrace : WordTrace (prefixWord ++ tailWord_4153754) baseStart_4153754 baseEnd_4153754 := by
    simpa [prefixWord, tailWord_4153754, baseEnd_4153754] using wordTrace_append hprefix tailTrace_4153754
  have hstable : (prefixWord ++ tailWord_4153754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153754).length < 2 ^ (prefixWord ++ tailWord_4153754).sum := by decide
  have hdescent : baseEnd_4153754 < baseStart_4153754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153758 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_4153758 : Nat := 118140960795 + 4153758 * 2 ^ 59
def prefixEnd_4153758 : Nat := 4983230072969 + 3 ^ 40 * 4153758 * 2
def baseEnd_4153758 : Nat := 710958125486154878807407

theorem tailTrace_4153758 : CollatzResearch.WordTrace tailWord_4153758 prefixEnd_4153758 710958125486154878807407 := by
  unfold tailWord_4153758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18937500060706455779107741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101000000323767764155241285 18937500060706455779107741)
  ·
    refine ⟨7101562522764920917165403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18937500060706455779107741 7101562522764920917165403)
    ·
      refine ⟨10652343784147381375748105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7101562522764920917165403 10652343784147381375748105)
      ·
        refine ⟨7989257838110536031811079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10652343784147381375748105 7989257838110536031811079)
        ·
          refine ⟨11983886757165804047716619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7989257838110536031811079 11983886757165804047716619)
          ·
            refine ⟨17975830135748706071574929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11983886757165804047716619 17975830135748706071574929)
            ·
              refine ⟨13481872601811529553681197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17975830135748706071574929 13481872601811529553681197)
              ·
                refine ⟨5055702225679323582630449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13481872601811529553681197 5055702225679323582630449)
                ·
                  refine ⟨3791776669259492686972837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5055702225679323582630449 3791776669259492686972837)
                  ·
                    refine ⟨710958125486154878807407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3791776669259492686972837 710958125486154878807407)
                    ·
                      rfl

theorem cell23_4153758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_4153758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153758 prefixEnd_4153758 := by exact prefixLift 4153758
  have htrace : WordTrace (prefixWord ++ tailWord_4153758) baseStart_4153758 baseEnd_4153758 := by
    simpa [prefixWord, tailWord_4153758, baseEnd_4153758] using wordTrace_append hprefix tailTrace_4153758
  have hstable : (prefixWord ++ tailWord_4153758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153758).length < 2 ^ (prefixWord ++ tailWord_4153758).sum := by decide
  have hdescent : baseEnd_4153758 < baseStart_4153758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153764 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_4153764 : Nat := 118140960795 + 4153764 * 2 ^ 59
def prefixEnd_4153764 : Nat := 4983230072969 + 3 ^ 40 * 4153764 * 2
def baseEnd_4153764 : Nat := 2132877457342391612947193

theorem tailTrace_4153764 : CollatzResearch.WordTrace tailWord_4153764 prefixEnd_4153764 2132877457342391612947193 := by
  unfold tailWord_4153764
  simp only [CollatzResearch.WordTrace]
  refine ⟨75750109661814954628790173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101000146215753272838386897 75750109661814954628790173)
  ·
    refine ⟨28406291123180607985796315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75750109661814954628790173 28406291123180607985796315)
    ·
      refine ⟨42609436684770911978694473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28406291123180607985796315 42609436684770911978694473)
      ·
        refine ⟨31957077513578183984020855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42609436684770911978694473 31957077513578183984020855)
        ·
          refine ⟨47935616270367275976031283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31957077513578183984020855 47935616270367275976031283)
          ·
            refine ⟨71903424405550913964046925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47935616270367275976031283 71903424405550913964046925)
            ·
              refine ⟨26963784152081592736517597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71903424405550913964046925 26963784152081592736517597)
              ·
                refine ⟨10111419057030597276194099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26963784152081592736517597 10111419057030597276194099)
                ·
                  refine ⟨15167128585545895914291149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10111419057030597276194099 15167128585545895914291149)
                  ·
                    refine ⟨5687673219579710967859181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15167128585545895914291149 5687673219579710967859181)
                    ·
                      refine ⟨2132877457342391612947193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5687673219579710967859181 2132877457342391612947193)
                      ·
                        rfl

theorem cell23_4153764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_4153764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153764 prefixEnd_4153764 := by exact prefixLift 4153764
  have htrace : WordTrace (prefixWord ++ tailWord_4153764) baseStart_4153764 baseEnd_4153764 := by
    simpa [prefixWord, tailWord_4153764, baseEnd_4153764] using wordTrace_append hprefix tailTrace_4153764
  have hstable : (prefixWord ++ tailWord_4153764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153764).length < 2 ^ (prefixWord ++ tailWord_4153764).sum := by decide
  have hdescent : baseEnd_4153764 < baseStart_4153764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153807 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_4153807 : Nat := 118140960795 + 4153807 * 2 ^ 59
def prefixEnd_4153807 : Nat := 4983230072969 + 3 ^ 40 * 4153807 * 2
def baseEnd_4153807 : Nat := 2132899537010534944709495

theorem tailTrace_4153807 : CollatzResearch.WordTrace tailWord_4153807 prefixEnd_4153807 2132899537010534944709495 := by
  unfold tailWord_4153807
  simp only [CollatzResearch.WordTrace]
  refine ⟨151501787662474127601395675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101001191774982751734263783 151501787662474127601395675)
  ·
    refine ⟨227252681493711191402093513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151501787662474127601395675 227252681493711191402093513)
    ·
      refine ⟨170439511120283393551570135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227252681493711191402093513 170439511120283393551570135)
      ·
        refine ⟨255659266680425090327355203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170439511120283393551570135 255659266680425090327355203)
        ·
          refine ⟨383488900020637635491032805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255659266680425090327355203 383488900020637635491032805)
          ·
            refine ⟨71904168753869556654568651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383488900020637635491032805 71904168753869556654568651)
            ·
              refine ⟨107856253130804334981852977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71904168753869556654568651 107856253130804334981852977)
              ·
                refine ⟨80892189848103251236389733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107856253130804334981852977 80892189848103251236389733)
                ·
                  refine ⟨15167285596519359606823075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80892189848103251236389733 15167285596519359606823075)
                  ·
                    refine ⟨22750928394779039410234613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15167285596519359606823075 22750928394779039410234613)
                    ·
                      refine ⟨2132899537010534944709495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22750928394779039410234613 2132899537010534944709495)
                      ·
                        rfl

theorem cell23_4153807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_4153807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153807 prefixEnd_4153807 := by exact prefixLift 4153807
  have htrace : WordTrace (prefixWord ++ tailWord_4153807) baseStart_4153807 baseEnd_4153807 := by
    simpa [prefixWord, tailWord_4153807, baseEnd_4153807] using wordTrace_append hprefix tailTrace_4153807
  have hstable : (prefixWord ++ tailWord_4153807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153807).length < 2 ^ (prefixWord ++ tailWord_4153807).sum := by decide
  have hdescent : baseEnd_4153807 < baseStart_4153807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153838 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_4153838 : Nat := 118140960795 + 4153838 * 2 ^ 59
def prefixEnd_4153838 : Nat := 4983230072969 + 3 ^ 40 * 4153838 * 2
def baseEnd_4153838 : Nat := 2132915454910824323421853

theorem tailTrace_4153838 : CollatzResearch.WordTrace tailWord_4153838 prefixEnd_4153838 2132915454910824323421853 := by
  unfold tailWord_4153838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18937864790670227486971771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101001945550241213263849445 18937864790670227486971771)
  ·
    refine ⟨28406797186005341230457657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18937864790670227486971771 28406797186005341230457657)
    ·
      refine ⟨21305097889504005922843243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28406797186005341230457657 21305097889504005922843243)
      ·
        refine ⟨31957646834256008884264865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21305097889504005922843243 31957646834256008884264865)
        ·
          refine ⟨23968235125692006663198649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31957646834256008884264865 23968235125692006663198649)
          ·
            refine ⟨17976176344269004997398987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23968235125692006663198649 17976176344269004997398987)
            ·
              refine ⟨26964264516403507496098481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17976176344269004997398987 26964264516403507496098481)
              ·
                refine ⟨20223198387302630622073861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26964264516403507496098481 20223198387302630622073861)
                ·
                  refine ⟨3791849697619243241638849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20223198387302630622073861 3791849697619243241638849)
                  ·
                    refine ⟨2843887273214432431229137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3791849697619243241638849 2843887273214432431229137)
                    ·
                      refine ⟨2132915454910824323421853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843887273214432431229137 2132915454910824323421853)
                      ·
                        rfl

theorem cell23_4153838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_4153838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153838 prefixEnd_4153838 := by exact prefixLift 4153838
  have htrace : WordTrace (prefixWord ++ tailWord_4153838) baseStart_4153838 baseEnd_4153838 := by
    simpa [prefixWord, tailWord_4153838, baseEnd_4153838] using wordTrace_append hprefix tailTrace_4153838
  have hstable : (prefixWord ++ tailWord_4153838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153838).length < 2 ^ (prefixWord ++ tailWord_4153838).sum := by decide
  have hdescent : baseEnd_4153838 < baseStart_4153838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153891 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 2, 5]
def baseStart_4153891 : Nat := 118140960795 + 4153891 * 2 ^ 59
def prefixEnd_4153891 : Nat := 4983230072969 + 3 ^ 40 * 4153891 * 2
def baseEnd_4153891 : Nat := 710980889795170872019703

theorem tailTrace_4153891 : CollatzResearch.WordTrace tailWord_4153891 prefixEnd_4153891 710980889795170872019703 := by
  unfold tailWord_4153891
  simp only [CollatzResearch.WordTrace]
  refine ⟨151504851394169809947453527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101003234262779873298302351 151504851394169809947453527)
  ·
    refine ⟨227257277091254714921180291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151504851394169809947453527 227257277091254714921180291)
    ·
      refine ⟨340885915636882072381770437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227257277091254714921180291 340885915636882072381770437)
      ·
        refine ⟨63916109181915388571581957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340885915636882072381770437 63916109181915388571581957)
        ·
          refine ⟨11984270471609135357171617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63916109181915388571581957 11984270471609135357171617)
          ·
            refine ⟨8988202853706851517878713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11984270471609135357171617 8988202853706851517878713)
            ·
              refine ⟨6741152140280138638409035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8988202853706851517878713 6741152140280138638409035)
              ·
                refine ⟨10111728210420207957613553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741152140280138638409035 10111728210420207957613553)
                ·
                  refine ⟨7583796157815155968210165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10111728210420207957613553 7583796157815155968210165)
                  ·
                    refine ⟨710980889795170872019703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7583796157815155968210165 710980889795170872019703)
                    ·
                      rfl

theorem cell23_4153891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 5].length) (baseStart_4153891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153891 prefixEnd_4153891 := by exact prefixLift 4153891
  have htrace : WordTrace (prefixWord ++ tailWord_4153891) baseStart_4153891 baseEnd_4153891 := by
    simpa [prefixWord, tailWord_4153891, baseEnd_4153891] using wordTrace_append hprefix tailTrace_4153891
  have hstable : (prefixWord ++ tailWord_4153891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153891).length < 2 ^ (prefixWord ++ tailWord_4153891).sum := by decide
  have hdescent : baseEnd_4153891 < baseStart_4153891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153911 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 2, 4, 2]
def baseStart_4153911 : Nat := 118140960795 + 4153911 * 2 ^ 59
def prefixEnd_4153911 : Nat := 4983230072969 + 3 ^ 40 * 4153911 * 2
def baseEnd_4153911 : Nat := 2132952938998602537809017

theorem tailTrace_4153911 : CollatzResearch.WordTrace tailWord_4153911 prefixEnd_4153911 2132952938998602537809017 := by
  unfold tailWord_4153911
  simp only [CollatzResearch.WordTrace]
  refine ⟨151505580854097353363181587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101003720569398235575454391 151505580854097353363181587)
  ·
    refine ⟨227258371281146030044772381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151505580854097353363181587 227258371281146030044772381)
    ·
      refine ⟨85221889230429761266789643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227258371281146030044772381 85221889230429761266789643)
      ·
        refine ⟨127832833845644641900184465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85221889230429761266789643 127832833845644641900184465)
        ·
          refine ⟨95874625384233481425138349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127832833845644641900184465 95874625384233481425138349)
          ·
            refine ⟨35952984519087555534426881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95874625384233481425138349 35952984519087555534426881)
            ·
              refine ⟨26964738389315666650820161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35952984519087555534426881 26964738389315666650820161)
              ·
                refine ⟨20223553791986749988115121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26964738389315666650820161 20223553791986749988115121)
                ·
                  refine ⟨15167665343990062491086341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20223553791986749988115121 15167665343990062491086341)
                  ·
                    refine ⟨2843937251998136717078689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15167665343990062491086341 2843937251998136717078689)
                    ·
                      refine ⟨2132952938998602537809017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843937251998136717078689 2132952938998602537809017)
                      ·
                        rfl

theorem cell23_4153911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_4153911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153911 prefixEnd_4153911 := by exact prefixLift 4153911
  have htrace : WordTrace (prefixWord ++ tailWord_4153911) baseStart_4153911 baseEnd_4153911 := by
    simpa [prefixWord, tailWord_4153911, baseEnd_4153911] using wordTrace_append hprefix tailTrace_4153911
  have hstable : (prefixWord ++ tailWord_4153911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153911).length < 2 ^ (prefixWord ++ tailWord_4153911).sum := by decide
  have hdescent : baseEnd_4153911 < baseStart_4153911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153948 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_4153948 : Nat := 118140960795 + 4153948 * 2 ^ 59
def prefixEnd_4153948 : Nat := 4983230072969 + 3 ^ 40 * 4153948 * 2
def baseEnd_4153948 : Nat := 2132971937782818893046347

theorem tailTrace_4153948 : CollatzResearch.WordTrace tailWord_4153948 prefixEnd_4153948 2132971937782818893046347 := by
  unfold tailWord_4153948
  simp only [CollatzResearch.WordTrace]
  refine ⟨75753465177481654341139249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101004620236642205788185665 75753465177481654341139249)
  ·
    refine ⟨56815098883111240755854437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75753465177481654341139249 56815098883111240755854437)
    ·
      refine ⟨10652831040583357641722707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56815098883111240755854437 10652831040583357641722707)
      ·
        refine ⟨15979246560875036462584061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10652831040583357641722707 15979246560875036462584061)
        ·
          refine ⟨5992217460328138673469023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15979246560875036462584061 5992217460328138673469023)
          ·
            refine ⟨8988326190492208010203535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5992217460328138673469023 8988326190492208010203535)
            ·
              refine ⟨13482489285738312015305303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8988326190492208010203535 13482489285738312015305303)
              ·
                refine ⟨20223733928607468022957955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13482489285738312015305303 20223733928607468022957955)
                ·
                  refine ⟨30335600892911202034436933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20223733928607468022957955 30335600892911202034436933)
                  ·
                    refine ⟨5687925167420850381456925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30335600892911202034436933 5687925167420850381456925)
                    ·
                      refine ⟨2132971937782818893046347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5687925167420850381456925 2132971937782818893046347)
                      ·
                        rfl

theorem cell23_4153948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_4153948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153948 prefixEnd_4153948 := by exact prefixLift 4153948
  have htrace : WordTrace (prefixWord ++ tailWord_4153948) baseStart_4153948 baseEnd_4153948 := by
    simpa [prefixWord, tailWord_4153948, baseEnd_4153948] using wordTrace_append hprefix tailTrace_4153948
  have hstable : (prefixWord ++ tailWord_4153948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153948).length < 2 ^ (prefixWord ++ tailWord_4153948).sum := by decide
  have hdescent : baseEnd_4153948 < baseStart_4153948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153961 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 7, 1, 3]
def baseStart_4153961 : Nat := 118140960795 + 4153961 * 2 ^ 59
def prefixEnd_4153961 : Nat := 4983230072969 + 3 ^ 40 * 4153961 * 2
def baseEnd_4153961 : Nat := 2132978613031327342183787

theorem tailTrace_4153961 : CollatzResearch.WordTrace tailWord_4153961 prefixEnd_4153961 2132978613031327342183787 := by
  unfold tailWord_4153961
  simp only [CollatzResearch.WordTrace]
  refine ⟨151507404503916211902501737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101004936335944141268334491 151507404503916211902501737)
  ·
    refine ⟨113630553377937158926876303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151507404503916211902501737 113630553377937158926876303)
    ·
      refine ⟨170445830066905738390314455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113630553377937158926876303 170445830066905738390314455)
      ·
        refine ⟨255668745100358607585471683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170445830066905738390314455 255668745100358607585471683)
        ·
          refine ⟨383503117650537911378207525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255668745100358607585471683 383503117650537911378207525)
          ·
            refine ⟨71906834559475858383413911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383503117650537911378207525 71906834559475858383413911)
            ·
              refine ⟨107860251839213787575120867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71906834559475858383413911 107860251839213787575120867)
              ·
                refine ⟨161790377758820681362681301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107860251839213787575120867 161790377758820681362681301)
                ·
                  refine ⟨3791961978722359719437843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 161790377758820681362681301 3791961978722359719437843)
                  ·
                    refine ⟨5687942968083539579156765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3791961978722359719437843 5687942968083539579156765)
                    ·
                      refine ⟨2132978613031327342183787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5687942968083539579156765 2132978613031327342183787)
                      ·
                        rfl

theorem cell23_4153961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 1, 3].length) (baseStart_4153961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153961 prefixEnd_4153961 := by exact prefixLift 4153961
  have htrace : WordTrace (prefixWord ++ tailWord_4153961) baseStart_4153961 baseEnd_4153961 := by
    simpa [prefixWord, tailWord_4153961, baseEnd_4153961] using wordTrace_append hprefix tailTrace_4153961
  have hstable : (prefixWord ++ tailWord_4153961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153961).length < 2 ^ (prefixWord ++ tailWord_4153961).sum := by decide
  have hdescent : baseEnd_4153961 < baseStart_4153961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153968 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 6]
def baseStart_4153968 : Nat := 118140960795 + 4153968 * 2 ^ 59
def prefixEnd_4153968 : Nat := 4983230072969 + 3 ^ 40 * 4153968 * 2
def baseEnd_4153968 : Nat := 236998023043989868310695

theorem tailTrace_4153968 : CollatzResearch.WordTrace tailWord_4153968 prefixEnd_4153968 236998023043989868310695 := by
  unfold tailWord_4153968
  simp only [CollatzResearch.WordTrace]
  refine ⟨75753829907445426049003279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101005106543260568065337705 75753829907445426049003279)
  ·
    refine ⟨113630744861168139073504919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75753829907445426049003279 113630744861168139073504919)
    ·
      refine ⟨170446117291752208610257379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113630744861168139073504919 170446117291752208610257379)
      ·
        refine ⟨255669175937628312915386069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170446117291752208610257379 255669175937628312915386069)
        ·
          refine ⟨5992246311038163583954361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 255669175937628312915386069 5992246311038163583954361)
          ·
            refine ⟨4494184733278622687965771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5992246311038163583954361 4494184733278622687965771)
            ·
              refine ⟨6741277099917934031948657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494184733278622687965771 6741277099917934031948657)
              ·
                refine ⟨5055957824938450523961493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6741277099917934031948657 5055957824938450523961493)
                ·
                  refine ⟨236998023043989868310695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5055957824938450523961493 236998023043989868310695)
                  ·
                    rfl

theorem cell23_4153968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 6].length) (baseStart_4153968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153968 prefixEnd_4153968 := by exact prefixLift 4153968
  have htrace : WordTrace (prefixWord ++ tailWord_4153968) baseStart_4153968 baseEnd_4153968 := by
    simpa [prefixWord, tailWord_4153968, baseEnd_4153968] using wordTrace_append hprefix tailTrace_4153968
  have hstable : (prefixWord ++ tailWord_4153968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153968).length < 2 ^ (prefixWord ++ tailWord_4153968).sum := by decide
  have hdescent : baseEnd_4153968 < baseStart_4153968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153988 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_4153988 : Nat := 118140960795 + 4153988 * 2 ^ 59
def prefixEnd_4153988 : Nat := 4983230072969 + 3 ^ 40 * 4153988 * 2
def baseEnd_4153988 : Nat := 2132992477008998736546163

theorem tailTrace_4153988 : CollatzResearch.WordTrace tailWord_4153988 prefixEnd_4153988 2132992477008998736546163 := by
  unfold tailWord_4153988
  simp only [CollatzResearch.WordTrace]
  refine ⟨75754194637409197756867309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101005592849878930342489745 75754194637409197756867309)
  ·
    refine ⟨28407822989028449158825241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75754194637409197756867309 28407822989028449158825241)
    ·
      refine ⟨21305867241771336869118931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28407822989028449158825241 21305867241771336869118931)
      ·
        refine ⟨31958800862657005303678397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21305867241771336869118931 31958800862657005303678397)
        ·
          refine ⟨11984550323496376988879399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31958800862657005303678397 11984550323496376988879399)
          ·
            refine ⟨17976825485244565483319099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11984550323496376988879399 17976825485244565483319099)
            ·
              refine ⟨26965238227866848224978649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17976825485244565483319099 26965238227866848224978649)
              ·
                refine ⟨20223928670900136168733987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26965238227866848224978649 20223928670900136168733987)
                ·
                  refine ⟨30335893006350204253100981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20223928670900136168733987 30335893006350204253100981)
                  ·
                    refine ⟨2843989969345331648728217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30335893006350204253100981 2843989969345331648728217)
                    ·
                      refine ⟨2132992477008998736546163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2843989969345331648728217 2132992477008998736546163)
                      ·
                        rfl

theorem cell23_4153988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_4153988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153988 prefixEnd_4153988 := by exact prefixLift 4153988
  have htrace : WordTrace (prefixWord ++ tailWord_4153988) baseStart_4153988 baseEnd_4153988 := by
    simpa [prefixWord, tailWord_4153988, baseEnd_4153988] using wordTrace_append hprefix tailTrace_4153988
  have hstable : (prefixWord ++ tailWord_4153988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153988).length < 2 ^ (prefixWord ++ tailWord_4153988).sum := by decide
  have hdescent : baseEnd_4153988 < baseStart_4153988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4153998 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_4153998 : Nat := 118140960795 + 4153998 * 2 ^ 59
def prefixEnd_4153998 : Nat := 4983230072969 + 3 ^ 40 * 4153998 * 2
def baseEnd_4153998 : Nat := 710999203938514565807039

theorem tailTrace_4153998 : CollatzResearch.WordTrace tailWord_4153998 prefixEnd_4153998 710999203938514565807039 := by
  unfold tailWord_4153998
  simp only [CollatzResearch.WordTrace]
  refine ⟨18938594250597770902699831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101005836003188111481065765 18938594250597770902699831)
  ·
    refine ⟨28407891375896656354049747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18938594250597770902699831 28407891375896656354049747)
    ·
      refine ⟨42611837063844984531074621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28407891375896656354049747 42611837063844984531074621)
      ·
        refine ⟨15979438898941869199152983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42611837063844984531074621 15979438898941869199152983)
        ·
          refine ⟨23969158348412803798729475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15979438898941869199152983 23969158348412803798729475)
          ·
            refine ⟨35953737522619205698094213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23969158348412803798729475 35953737522619205698094213)
            ·
              refine ⟨6741325785491101068392665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35953737522619205698094213 6741325785491101068392665)
              ·
                refine ⟨5055994339118325801294499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6741325785491101068392665 5055994339118325801294499)
                ·
                  refine ⟨7583991508677488701941749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055994339118325801294499 7583991508677488701941749)
                  ·
                    refine ⟨710999203938514565807039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7583991508677488701941749 710999203938514565807039)
                    ·
                      rfl

theorem cell23_4153998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_4153998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4153998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4153998 prefixEnd_4153998 := by exact prefixLift 4153998
  have htrace : WordTrace (prefixWord ++ tailWord_4153998) baseStart_4153998 baseEnd_4153998 := by
    simpa [prefixWord, tailWord_4153998, baseEnd_4153998] using wordTrace_append hprefix tailTrace_4153998
  have hstable : (prefixWord ++ tailWord_4153998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4153998).length < 2 ^ (prefixWord ++ tailWord_4153998).sum := by decide
  have hdescent : baseEnd_4153998 < baseStart_4153998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4153998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154012 : List Nat := [2, 2, 3, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_4154012 : Nat := 118140960795 + 4154012 * 2 ^ 59
def prefixEnd_4154012 : Nat := 4983230072969 + 3 ^ 40 * 4154012 * 2
def baseEnd_4154012 : Nat := 2133004800544706642646053

theorem tailTrace_4154012 : CollatzResearch.WordTrace tailWord_4154012 prefixEnd_4154012 2133004800544706642646053 := by
  unfold tailWord_4154012
  simp only [CollatzResearch.WordTrace]
  refine ⟨75754632313365723806304145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101006176417820965075072193 75754632313365723806304145)
  ·
    refine ⟨56815974235024292854728109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75754632313365723806304145 56815974235024292854728109)
    ·
      refine ⟨21305990338134109820523041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56815974235024292854728109 21305990338134109820523041)
      ·
        refine ⟨15979492753600582365392281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21305990338134109820523041 15979492753600582365392281)
        ·
          refine ⟨11984619565200436774044211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15979492753600582365392281 11984619565200436774044211)
          ·
            refine ⟨17976929347800655161066317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11984619565200436774044211 17976929347800655161066317)
            ·
              refine ⟨6741348505425245685399869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17976929347800655161066317 6741348505425245685399869)
              ·
                refine ⟨2528005689534467132024951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6741348505425245685399869 2528005689534467132024951)
                ·
                  refine ⟨3792008534301700698037427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528005689534467132024951 3792008534301700698037427)
                  ·
                    refine ⟨5688012801452551047056141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792008534301700698037427 5688012801452551047056141)
                    ·
                      refine ⟨2133004800544706642646053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5688012801452551047056141 2133004800544706642646053)
                      ·
                        rfl

theorem cell23_4154012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_4154012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154012 prefixEnd_4154012 := by exact prefixLift 4154012
  have htrace : WordTrace (prefixWord ++ tailWord_4154012) baseStart_4154012 baseEnd_4154012 := by
    simpa [prefixWord, tailWord_4154012, baseEnd_4154012] using wordTrace_append hprefix tailTrace_4154012
  have hstable : (prefixWord ++ tailWord_4154012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154012).length < 2 ^ (prefixWord ++ tailWord_4154012).sum := by decide
  have hdescent : baseEnd_4154012 < baseStart_4154012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154021 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 5, 2, 3]
def baseStart_4154021 : Nat := 118140960795 + 4154021 * 2 ^ 59
def prefixEnd_4154021 : Nat := 4983230072969 + 3 ^ 40 * 4154021 * 2
def baseEnd_4154021 : Nat := 2133009421870597107433511

theorem tailTrace_4154021 : CollatzResearch.WordTrace tailWord_4154021 prefixEnd_4154021 2133009421870597107433511 := by
  unfold tailWord_4154021
  simp only [CollatzResearch.WordTrace]
  refine ⟨151509592883698842149685917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101006395255799228099790611 151509592883698842149685917)
  ·
    refine ⟨56816097331387065806132219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151509592883698842149685917 56816097331387065806132219)
    ·
      refine ⟨85224145997080598709198329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56816097331387065806132219 85224145997080598709198329)
      ·
        refine ⟨63918109497810449031898747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85224145997080598709198329 63918109497810449031898747)
        ·
          refine ⟨95877164246715673547848121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63918109497810449031898747 95877164246715673547848121)
          ·
            refine ⟨71907873185036755160886091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95877164246715673547848121 71907873185036755160886091)
            ·
              refine ⟨107861809777555132741329137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71907873185036755160886091 107861809777555132741329137)
              ·
                refine ⟨80896357333166349555996853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107861809777555132741329137 80896357333166349555996853)
                ·
                  refine ⟨7584033499984345270874705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80896357333166349555996853 7584033499984345270874705)
                  ·
                    refine ⟨5688025124988258953156029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7584033499984345270874705 5688025124988258953156029)
                    ·
                      refine ⟨2133009421870597107433511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5688025124988258953156029 2133009421870597107433511)
                      ·
                        rfl

theorem cell23_4154021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_4154021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154021 prefixEnd_4154021 := by exact prefixLift 4154021
  have htrace : WordTrace (prefixWord ++ tailWord_4154021) baseStart_4154021 baseEnd_4154021 := by
    simpa [prefixWord, tailWord_4154021, baseEnd_4154021] using wordTrace_append hprefix tailTrace_4154021
  have hstable : (prefixWord ++ tailWord_4154021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154021).length < 2 ^ (prefixWord ++ tailWord_4154021).sum := by decide
  have hdescent : baseEnd_4154021 < baseStart_4154021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154029 : List Nat := [1, 5, 2, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_4154029 : Nat := 118140960795 + 4154029 * 2 ^ 59
def prefixEnd_4154029 : Nat := 4983230072969 + 3 ^ 40 * 4154029 * 2
def baseEnd_4154029 : Nat := 2133013529715833076133475

theorem tailTrace_4154029 : CollatzResearch.WordTrace tailWord_4154029 prefixEnd_4154029 2133013529715833076133475 := by
  unfold tailWord_4154029
  simp only [CollatzResearch.WordTrace]
  refine ⟨151509884667669859515977141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101006589778446573010651427 151509884667669859515977141)
  ·
    refine ⟨14204051687594049329622857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151509884667669859515977141 14204051687594049329622857)
    ·
      refine ⟨10653038765695536997217143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14204051687594049329622857 10653038765695536997217143)
      ·
        refine ⟨15979558148543305495825715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10653038765695536997217143 15979558148543305495825715)
        ·
          refine ⟨23969337222814958243738573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15979558148543305495825715 23969337222814958243738573)
          ·
            refine ⟨8988501458555609341401965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23969337222814958243738573 8988501458555609341401965)
            ·
              refine ⟨3370688046958353503025737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8988501458555609341401965 3370688046958353503025737)
              ·
                refine ⟨2528016035218765127269303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3370688046958353503025737 2528016035218765127269303)
                ·
                  refine ⟨3792024052828147690903955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528016035218765127269303 3792024052828147690903955)
                  ·
                    refine ⟨5688036079242221536355933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792024052828147690903955 5688036079242221536355933)
                    ·
                      refine ⟨2133013529715833076133475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5688036079242221536355933 2133013529715833076133475)
                      ·
                        rfl

theorem cell23_4154029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_4154029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154029 prefixEnd_4154029 := by exact prefixLift 4154029
  have htrace : WordTrace (prefixWord ++ tailWord_4154029) baseStart_4154029 baseEnd_4154029 := by
    simpa [prefixWord, tailWord_4154029, baseEnd_4154029] using wordTrace_append hprefix tailTrace_4154029
  have hstable : (prefixWord ++ tailWord_4154029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154029).length < 2 ^ (prefixWord ++ tailWord_4154029).sum := by decide
  have hdescent : baseEnd_4154029 < baseStart_4154029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154035 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 3, 2, 2]
def baseStart_4154035 : Nat := 118140960795 + 4154035 * 2 ^ 59
def prefixEnd_4154035 : Nat := 4983230072969 + 3 ^ 40 * 4154035 * 2
def baseEnd_4154035 : Nat := 2133016610599760052658447

theorem tailTrace_4154035 : CollatzResearch.WordTrace tailWord_4154035 prefixEnd_4154035 2133016610599760052658447 := by
  unfold tailWord_4154035
  simp only [CollatzResearch.WordTrace]
  refine ⟨151510103505648122540695559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101006735670432081693797039 151510103505648122540695559)
  ·
    refine ⟨227265155258472183811043339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151510103505648122540695559 227265155258472183811043339)
    ·
      refine ⟨340897732887708275716565009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227265155258472183811043339 340897732887708275716565009)
      ·
        refine ⟨255673299665781206787423757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340897732887708275716565009 255673299665781206787423757)
        ·
          refine ⟨95877487374667952545283909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255673299665781206787423757 95877487374667952545283909)
          ·
            refine ⟨17977028882750241102240733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95877487374667952545283909 17977028882750241102240733)
            ·
              refine ⟨6741385831031340413340275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17977028882750241102240733 6741385831031340413340275)
              ·
                refine ⟨10112078746547010620010413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741385831031340413340275 10112078746547010620010413)
                ·
                  refine ⟨3792029529955128982503905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10112078746547010620010413 3792029529955128982503905)
                  ·
                    refine ⟨2844022147466346736877929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3792029529955128982503905 2844022147466346736877929)
                    ·
                      refine ⟨2133016610599760052658447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2844022147466346736877929 2133016610599760052658447)
                      ·
                        rfl

theorem cell23_4154035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 2, 2].length) (baseStart_4154035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154035 prefixEnd_4154035 := by exact prefixLift 4154035
  have htrace : WordTrace (prefixWord ++ tailWord_4154035) baseStart_4154035 baseEnd_4154035 := by
    simpa [prefixWord, tailWord_4154035, baseEnd_4154035] using wordTrace_append hprefix tailTrace_4154035
  have hstable : (prefixWord ++ tailWord_4154035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154035).length < 2 ^ (prefixWord ++ tailWord_4154035).sum := by decide
  have hdescent : baseEnd_4154035 < baseStart_4154035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154045 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_4154045 : Nat := 118140960795 + 4154045 * 2 ^ 59
def prefixEnd_4154045 : Nat := 4983230072969 + 3 ^ 40 * 4154045 * 2
def baseEnd_4154045 : Nat := 711007248468768337844467

theorem tailTrace_4154045 : CollatzResearch.WordTrace tailWord_4154045 prefixEnd_4154045 711007248468768337844467 := by
  unfold tailWord_4154045
  simp only [CollatzResearch.WordTrace]
  refine ⟨151510468235611894248559589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101006978823741262832373059 151510468235611894248559589)
  ·
    refine ⟨28408212794177230171604923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151510468235611894248559589 28408212794177230171604923)
    ·
      refine ⟨42612319191265845257407385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28408212794177230171604923 42612319191265845257407385)
      ·
        refine ⟨31959239393449383943055539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42612319191265845257407385 31959239393449383943055539)
        ·
          refine ⟨47938859090174075914583309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31959239393449383943055539 47938859090174075914583309)
          ·
            refine ⟨17977072158815278467968741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47938859090174075914583309 17977072158815278467968741)
            ·
              refine ⟨3370701029777864712744139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17977072158815278467968741 3370701029777864712744139)
              ·
                refine ⟨5056051544666797069116209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370701029777864712744139 5056051544666797069116209)
                ·
                  refine ⟨3792038658500097801837157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5056051544666797069116209 3792038658500097801837157)
                  ·
                    refine ⟨711007248468768337844467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3792038658500097801837157 711007248468768337844467)
                    ·
                      rfl

theorem cell23_4154045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_4154045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154045 prefixEnd_4154045 := by exact prefixLift 4154045
  have htrace : WordTrace (prefixWord ++ tailWord_4154045) baseStart_4154045 baseEnd_4154045 := by
    simpa [prefixWord, tailWord_4154045, baseEnd_4154045] using wordTrace_append hprefix tailTrace_4154045
  have hstable : (prefixWord ++ tailWord_4154045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154045).length < 2 ^ (prefixWord ++ tailWord_4154045).sum := by decide
  have hdescent : baseEnd_4154045 < baseStart_4154045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154049 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4154049 : Nat := 118140960795 + 4154049 * 2 ^ 59
def prefixEnd_4154049 : Nat := 4983230072969 + 3 ^ 40 * 4154049 * 2
def baseEnd_4154049 : Nat := 711007933109640999294461

theorem tailTrace_4154049 : CollatzResearch.WordTrace tailWord_4154049 prefixEnd_4154049 711007933109640999294461 := by
  unfold tailWord_4154049
  simp only [CollatzResearch.WordTrace]
  refine ⟨151510614127597402931705201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101007076085064935287803467 151510614127597402931705201)
  ·
    refine ⟨113632960595698052198778901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151510614127597402931705201 113632960595698052198778901)
    ·
      refine ⟨5326545027923346196817761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113632960595698052198778901 5326545027923346196817761)
      ·
        refine ⟨3994908770942509647613321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5326545027923346196817761 3994908770942509647613321)
        ·
          refine ⟨2996181578206882235709991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3994908770942509647613321 2996181578206882235709991)
          ·
            refine ⟨4494272367310323353564987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996181578206882235709991 4494272367310323353564987)
            ·
              refine ⟨6741408550965485030347481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494272367310323353564987 6741408550965485030347481)
              ·
                refine ⟨5056056413224113772760611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6741408550965485030347481 5056056413224113772760611)
                ·
                  refine ⟨7584084619836170659140917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5056056413224113772760611 7584084619836170659140917)
                  ·
                    refine ⟨711007933109640999294461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7584084619836170659140917 711007933109640999294461)
                    ·
                      rfl

theorem cell23_4154049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4154049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154049 prefixEnd_4154049 := by exact prefixLift 4154049
  have htrace : WordTrace (prefixWord ++ tailWord_4154049) baseStart_4154049 baseEnd_4154049 := by
    simpa [prefixWord, tailWord_4154049, baseEnd_4154049] using wordTrace_append hprefix tailTrace_4154049
  have hstable : (prefixWord ++ tailWord_4154049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154049).length < 2 ^ (prefixWord ++ tailWord_4154049).sum := by decide
  have hdescent : baseEnd_4154049 < baseStart_4154049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154064 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_4154064 : Nat := 118140960795 + 4154064 * 2 ^ 59
def prefixEnd_4154064 : Nat := 4983230072969 + 3 ^ 40 * 4154064 * 2
def baseEnd_4154064 : Nat := 2133031501538740439195813

theorem tailTrace_4154064 : CollatzResearch.WordTrace tailWord_4154064 prefixEnd_4154064 2133031501538740439195813 := by
  unfold tailWord_4154064
  simp only [CollatzResearch.WordTrace]
  refine ⟨75755580611271530246750623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101007440815028706995667497 75755580611271530246750623)
  ·
    refine ⟨113633370916907295370125935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75755580611271530246750623 113633370916907295370125935)
    ·
      refine ⟨170450056375360943055188903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113633370916907295370125935 170450056375360943055188903)
      ·
        refine ⟨255675084563041414582783355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170450056375360943055188903 255675084563041414582783355)
        ·
          refine ⟨383512626844562121874175033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255675084563041414582783355 383512626844562121874175033)
          ·
            refine ⟨287634470133421591405631275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383512626844562121874175033 287634470133421591405631275)
            ·
              refine ⟨431451705200132387108446913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287634470133421591405631275 431451705200132387108446913)
              ·
                refine ⟨323588778900099290331335185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431451705200132387108446913 323588778900099290331335185)
                ·
                  refine ⟨242691584175074467748501389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323588778900099290331335185 242691584175074467748501389)
                  ·
                    refine ⟨91009344065652925405688021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242691584175074467748501389 91009344065652925405688021)
                    ·
                      refine ⟨2133031501538740439195813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91009344065652925405688021 2133031501538740439195813)
                      ·
                        rfl

theorem cell23_4154064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_4154064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154064 prefixEnd_4154064 := by exact prefixLift 4154064
  have htrace : WordTrace (prefixWord ++ tailWord_4154064) baseStart_4154064 baseEnd_4154064 := by
    simpa [prefixWord, tailWord_4154064, baseEnd_4154064] using wordTrace_append hprefix tailTrace_4154064
  have hstable : (prefixWord ++ tailWord_4154064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154064).length < 2 ^ (prefixWord ++ tailWord_4154064).sum := by decide
  have hdescent : baseEnd_4154064 < baseStart_4154064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154085 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 2, 1, 3]
def baseStart_4154085 : Nat := 118140960795 + 4154085 * 2 ^ 59
def prefixEnd_4154085 : Nat := 4983230072969 + 3 ^ 40 * 4154085 * 2
def baseEnd_4154085 : Nat := 2133042284632484857033217

theorem tailTrace_4154085 : CollatzResearch.WordTrace tailWord_4154085 prefixEnd_4154085 2133042284632484857033217 := by
  unfold tailWord_4154085
  simp only [CollatzResearch.WordTrace]
  refine ⟨151511927155466981080015709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101007951436977987386677139 151511927155466981080015709)
  ·
    refine ⟨56816972683300117905005891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151511927155466981080015709 56816972683300117905005891)
    ·
      refine ⟨85225459024950176857508837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56816972683300117905005891 85225459024950176857508837)
      ·
        refine ⟨15979773567178158160782907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85225459024950176857508837 15979773567178158160782907)
        ·
          refine ⟨23969660350767237241174361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15979773567178158160782907 23969660350767237241174361)
          ·
            refine ⟨17977245263075427930880771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23969660350767237241174361 17977245263075427930880771)
            ·
              refine ⟨26965867894613141896321157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17977245263075427930880771 26965867894613141896321157)
              ·
                refine ⟨5056100230239964105560217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26965867894613141896321157 5056100230239964105560217)
                ·
                  refine ⟨3792075172679973079170163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5056100230239964105560217 3792075172679973079170163)
                  ·
                    refine ⟨5688112759019959618755245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792075172679973079170163 5688112759019959618755245)
                    ·
                      refine ⟨2133042284632484857033217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5688112759019959618755245 2133042284632484857033217)
                      ·
                        rfl

theorem cell23_4154085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_4154085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154085 prefixEnd_4154085 := by exact prefixLift 4154085
  have htrace : WordTrace (prefixWord ++ tailWord_4154085) baseStart_4154085 baseEnd_4154085 := by
    simpa [prefixWord, tailWord_4154085, baseEnd_4154085] using wordTrace_append hprefix tailTrace_4154085
  have hstable : (prefixWord ++ tailWord_4154085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154085).length < 2 ^ (prefixWord ++ tailWord_4154085).sum := by decide
  have hdescent : baseEnd_4154085 < baseStart_4154085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154111 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 3]
def baseStart_4154111 : Nat := 118140960795 + 4154111 * 2 ^ 59
def prefixEnd_4154111 : Nat := 4983230072969 + 3 ^ 40 * 4154111 * 2
def baseEnd_4154111 : Nat := 2133055635129501755308097

theorem tailTrace_4154111 : CollatzResearch.WordTrace tailWord_4154111 prefixEnd_4154111 2133055635129501755308097 := by
  unfold tailWord_4154111
  simp only [CollatzResearch.WordTrace]
  refine ⟨151512875453372787520462187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101008583635581858346974791 151512875453372787520462187)
  ·
    refine ⟨227269313180059181280693281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151512875453372787520462187 227269313180059181280693281)
    ·
      refine ⟨170451984885044385960519961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227269313180059181280693281 170451984885044385960519961)
      ·
        refine ⟨127838988663783289470389971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170451984885044385960519961 127838988663783289470389971)
        ·
          refine ⟨191758482995674934205584957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127838988663783289470389971 191758482995674934205584957)
          ·
            refine ⟨71909431123378100327094359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191758482995674934205584957 71909431123378100327094359)
            ·
              refine ⟨107864146685067150490641539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71909431123378100327094359 107864146685067150490641539)
              ·
                refine ⟨161796220027600725735962309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107864146685067150490641539 161796220027600725735962309)
                ·
                  refine ⟨30336791255175136075492933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161796220027600725735962309 30336791255175136075492933)
                  ·
                    refine ⟨5688148360345338014154925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30336791255175136075492933 5688148360345338014154925)
                    ·
                      refine ⟨2133055635129501755308097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5688148360345338014154925 2133055635129501755308097)
                      ·
                        rfl

theorem cell23_4154111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_4154111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154111 prefixEnd_4154111 := by exact prefixLift 4154111
  have htrace : WordTrace (prefixWord ++ tailWord_4154111) baseStart_4154111 baseEnd_4154111 := by
    simpa [prefixWord, tailWord_4154111, baseEnd_4154111] using wordTrace_append hprefix tailTrace_4154111
  have hstable : (prefixWord ++ tailWord_4154111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154111).length < 2 ^ (prefixWord ++ tailWord_4154111).sum := by decide
  have hdescent : baseEnd_4154111 < baseStart_4154111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154161 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 3, 7]
def baseStart_4154161 : Nat := 118140960795 + 4154161 * 2 ^ 59
def prefixEnd_4154161 : Nat := 4983230072969 + 3 ^ 40 * 4154161 * 2
def baseEnd_4154161 : Nat := 711027103054075519894289

theorem tailTrace_4154161 : CollatzResearch.WordTrace tailWord_4154161 prefixEnd_4154161 711027103054075519894289 := by
  unfold tailWord_4154161
  simp only [CollatzResearch.WordTrace]
  refine ⟨151514699103191646059782337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101009799402127764039854891 151514699103191646059782337)
  ·
    refine ⟨113636024327393734544836753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151514699103191646059782337 113636024327393734544836753)
    ·
      refine ⟨85227018245545300908627565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113636024327393734544836753 85227018245545300908627565)
      ·
        refine ⟨31960131842079487840735337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85227018245545300908627565 31960131842079487840735337)
        ·
          refine ⟨23970098881559615880551503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31960131842079487840735337 23970098881559615880551503)
          ·
            refine ⟨35955148322339423820827255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23970098881559615880551503 35955148322339423820827255)
            ·
              refine ⟨53932722483509135731240883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35955148322339423820827255 53932722483509135731240883)
              ·
                refine ⟨80899083725263703596861325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53932722483509135731240883 80899083725263703596861325)
                ·
                  refine ⟨30337156396973888848822997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80899083725263703596861325 30337156396973888848822997)
                  ·
                    refine ⟨711027103054075519894289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30337156396973888848822997 711027103054075519894289)
                    ·
                      rfl

theorem cell23_4154161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_4154161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154161 prefixEnd_4154161 := by exact prefixLift 4154161
  have htrace : WordTrace (prefixWord ++ tailWord_4154161) baseStart_4154161 baseEnd_4154161 := by
    simpa [prefixWord, tailWord_4154161, baseEnd_4154161] using wordTrace_append hprefix tailTrace_4154161
  have hstable : (prefixWord ++ tailWord_4154161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154161).length < 2 ^ (prefixWord ++ tailWord_4154161).sum := by decide
  have hdescent : baseEnd_4154161 < baseStart_4154161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154265 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 3, 1, 3]
def baseStart_4154265 : Nat := 118140960795 + 4154265 * 2 ^ 59
def prefixEnd_4154265 : Nat := 4983230072969 + 3 ^ 40 * 4154265 * 2
def baseEnd_4154265 : Nat := 2133134711150294152782389

theorem tailTrace_4154265 : CollatzResearch.WordTrace tailWord_4154265 prefixEnd_4154265 2133134711150294152782389 := by
  unfold tailWord_4154265
  simp only [CollatzResearch.WordTrace]
  refine ⟨151518492294814871821568249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101012328196543247881045499 151518492294814871821568249)
  ·
    refine ⟨113638869221111153866176187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151518492294814871821568249 113638869221111153866176187)
    ·
      refine ⟨170458303831666730799264281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113638869221111153866176187 170458303831666730799264281)
      ·
        refine ⟨127843727873750048099448211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170458303831666730799264281 127843727873750048099448211)
        ·
          refine ⟨191765591810625072149172317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127843727873750048099448211 191765591810625072149172317)
          ·
            refine ⟨71912096928984402055939619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191765591810625072149172317 71912096928984402055939619)
            ·
              refine ⟨107868145393476603083909429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71912096928984402055939619 107868145393476603083909429)
              ·
                refine ⟨10112638630638431539116509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107868145393476603083909429 10112638630638431539116509)
                ·
                  refine ⟨3792239486489411827168691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10112638630638431539116509 3792239486489411827168691)
                  ·
                    refine ⟨5688359229734117740753037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792239486489411827168691 5688359229734117740753037)
                    ·
                      refine ⟨2133134711150294152782389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5688359229734117740753037 2133134711150294152782389)
                      ·
                        rfl

theorem cell23_4154265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_4154265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154265 prefixEnd_4154265 := by exact prefixLift 4154265
  have htrace : WordTrace (prefixWord ++ tailWord_4154265) baseStart_4154265 baseEnd_4154265 := by
    simpa [prefixWord, tailWord_4154265, baseEnd_4154265] using wordTrace_append hprefix tailTrace_4154265
  have hstable : (prefixWord ++ tailWord_4154265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154265).length < 2 ^ (prefixWord ++ tailWord_4154265).sum := by decide
  have hdescent : baseEnd_4154265 < baseStart_4154265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154275 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 4, 3, 2]
def baseStart_4154275 : Nat := 118140960795 + 4154275 * 2 ^ 59
def prefixEnd_4154275 : Nat := 4983230072969 + 3 ^ 40 * 4154275 * 2
def baseEnd_4154275 : Nat := 2133139845956839113657343

theorem tailTrace_4154275 : CollatzResearch.WordTrace tailWord_4154275 prefixEnd_4154275 2133139845956839113657343 := by
  unfold tailWord_4154275
  simp only [CollatzResearch.WordTrace]
  refine ⟨151518857024778643529432279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101012571349852429019621519 151518857024778643529432279)
  ·
    refine ⟨227278285537167965294148419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151518857024778643529432279 227278285537167965294148419)
    ·
      refine ⟨340917428305751947941222629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227278285537167965294148419 340917428305751947941222629)
      ·
        refine ⟨63922017807328490238979243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340917428305751947941222629 63922017807328490238979243)
        ·
          refine ⟨95883026710992735358468865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63922017807328490238979243 95883026710992735358468865)
          ·
            refine ⟨71912270033244551518851649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95883026710992735358468865 71912270033244551518851649)
            ·
              refine ⟨53934202524933413639138737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71912270033244551518851649 53934202524933413639138737)
              ·
                refine ⟨40450651893700060229354053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53934202524933413639138737 40450651893700060229354053)
                ·
                  refine ⟨7584497230068761293003885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40450651893700060229354053 7584497230068761293003885)
                  ·
                    refine ⟨2844186461275785484876457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7584497230068761293003885 2844186461275785484876457)
                    ·
                      refine ⟨2133139845956839113657343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2844186461275785484876457 2133139845956839113657343)
                      ·
                        rfl

theorem cell23_4154275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_4154275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154275 prefixEnd_4154275 := by exact prefixLift 4154275
  have htrace : WordTrace (prefixWord ++ tailWord_4154275) baseStart_4154275 baseEnd_4154275 := by
    simpa [prefixWord, tailWord_4154275, baseEnd_4154275] using wordTrace_append hprefix tailTrace_4154275
  have hstable : (prefixWord ++ tailWord_4154275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154275).length < 2 ^ (prefixWord ++ tailWord_4154275).sum := by decide
  have hdescent : baseEnd_4154275 < baseStart_4154275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154298 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_4154298 : Nat := 118140960795 + 4154298 * 2 ^ 59
def prefixEnd_4154298 : Nat := 4983230072969 + 3 ^ 40 * 4154298 * 2
def baseEnd_4154298 : Nat := 711050552003964174556579

theorem tailTrace_4154298 : CollatzResearch.WordTrace tailWord_4154298 prefixEnd_4154298 711050552003964174556579 := by
  unfold tailWord_4154298
  simp only [CollatzResearch.WordTrace]
  refine ⟨37879923975923829614379887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101013130602463545638346365 37879923975923829614379887)
  ·
    refine ⟨56819885963885744421569831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37879923975923829614379887 56819885963885744421569831)
    ·
      refine ⟨85229828945828616632354747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56819885963885744421569831 85229828945828616632354747)
      ·
        refine ⟨127844743418742924948532121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85229828945828616632354747 127844743418742924948532121)
        ·
          refine ⟨95883557564057193711399091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127844743418742924948532121 95883557564057193711399091)
          ·
            refine ⟨143825336346085790567098637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95883557564057193711399091 143825336346085790567098637)
            ·
              refine ⟨53934501129782171462661989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143825336346085790567098637 53934501129782171462661989)
              ·
                refine ⟨10112718961834157149249123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53934501129782171462661989 10112718961834157149249123)
                ·
                  refine ⟨15169078442751235723873685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10112718961834157149249123 15169078442751235723873685)
                  ·
                    refine ⟨711050552003964174556579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15169078442751235723873685 711050552003964174556579)
                    ·
                      rfl

theorem cell23_4154298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_4154298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154298 prefixEnd_4154298 := by exact prefixLift 4154298
  have htrace : WordTrace (prefixWord ++ tailWord_4154298) baseStart_4154298 baseEnd_4154298 := by
    simpa [prefixWord, tailWord_4154298, baseEnd_4154298] using wordTrace_append hprefix tailTrace_4154298
  have hstable : (prefixWord ++ tailWord_4154298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154298).length < 2 ^ (prefixWord ++ tailWord_4154298).sum := by decide
  have hdescent : baseEnd_4154298 < baseStart_4154298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154315 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 4, 4]
def baseStart_4154315 : Nat := 118140960795 + 4154315 * 2 ^ 59
def prefixEnd_4154315 : Nat := 4983230072969 + 3 ^ 40 * 4154315 * 2
def baseEnd_4154315 : Nat := 711053461727672985719053

theorem tailTrace_4154315 : CollatzResearch.WordTrace tailWord_4154315 prefixEnd_4154315 711053461727672985719053 := by
  unfold tailWord_4154315
  simp only [CollatzResearch.WordTrace]
  refine ⟨151520315944633730360888399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101013543963089153573925599 151520315944633730360888399)
  ·
    refine ⟨227280473916950595541332599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151520315944633730360888399 227280473916950595541332599)
    ·
      refine ⟨340920710875425893311998899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227280473916950595541332599 340920710875425893311998899)
      ·
        refine ⟨511381066313138839967998349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340920710875425893311998899 511381066313138839967998349)
        ·
          refine ⟨191767899867427064987999381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511381066313138839967998349 191767899867427064987999381)
          ·
            refine ⟨8989120306285643671312471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191767899867427064987999381 8989120306285643671312471)
            ·
              refine ⟨13483680459428465506968707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8989120306285643671312471 13483680459428465506968707)
              ·
                refine ⟨20225520689142698260453061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13483680459428465506968707 20225520689142698260453061)
                ·
                  refine ⟨3792285129214255923834949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20225520689142698260453061 3792285129214255923834949)
                  ·
                    refine ⟨711053461727672985719053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3792285129214255923834949 711053461727672985719053)
                    ·
                      rfl

theorem cell23_4154315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 4].length) (baseStart_4154315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154315 prefixEnd_4154315 := by exact prefixLift 4154315
  have htrace : WordTrace (prefixWord ++ tailWord_4154315) baseStart_4154315 baseEnd_4154315 := by
    simpa [prefixWord, tailWord_4154315, baseEnd_4154315] using wordTrace_append hprefix tailTrace_4154315
  have hstable : (prefixWord ++ tailWord_4154315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154315).length < 2 ^ (prefixWord ++ tailWord_4154315).sum := by decide
  have hdescent : baseEnd_4154315 < baseStart_4154315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154335 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 6]
def baseStart_4154335 : Nat := 118140960795 + 4154335 * 2 ^ 59
def prefixEnd_4154335 : Nat := 4983230072969 + 3 ^ 40 * 4154335 * 2
def baseEnd_4154335 : Nat := 2133170654796108878907067

theorem tailTrace_4154335 : CollatzResearch.WordTrace tailWord_4154335 prefixEnd_4154335 2133170654796108878907067 := by
  unfold tailWord_4154335
  simp only [CollatzResearch.WordTrace]
  refine ⟨151521045404561273776616459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101014030269707515851077639 151521045404561273776616459)
  ·
    refine ⟨227281568106841910664924689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151521045404561273776616459 227281568106841910664924689)
    ·
      refine ⟨170461176080131432998693517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227281568106841910664924689 170461176080131432998693517)
      ·
        refine ⟨63922941030049287374510069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170461176080131432998693517 63922941030049287374510069)
        ·
          refine ⟨5992775721567120691360319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63922941030049287374510069 5992775721567120691360319)
          ·
            refine ⟨8989163582350681037040479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5992775721567120691360319 8989163582350681037040479)
            ·
              refine ⟨13483745373526021555560719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8989163582350681037040479 13483745373526021555560719)
              ·
                refine ⟨20225618060289032333341079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13483745373526021555560719 20225618060289032333341079)
                ·
                  refine ⟨30338427090433548500011619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20225618060289032333341079 30338427090433548500011619)
                  ·
                    refine ⟨45507640635650322750017429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30338427090433548500011619 45507640635650322750017429)
                    ·
                      refine ⟨2133170654796108878907067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45507640635650322750017429 2133170654796108878907067)
                      ·
                        rfl

theorem cell23_4154335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_4154335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154335 prefixEnd_4154335 := by exact prefixLift 4154335
  have htrace : WordTrace (prefixWord ++ tailWord_4154335) baseStart_4154335 baseEnd_4154335 := by
    simpa [prefixWord, tailWord_4154335, baseEnd_4154335] using wordTrace_append hprefix tailTrace_4154335
  have hstable : (prefixWord ++ tailWord_4154335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154335).length < 2 ^ (prefixWord ++ tailWord_4154335).sum := by decide
  have hdescent : baseEnd_4154335 < baseStart_4154335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154389 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_4154389 : Nat := 118140960795 + 4154389 * 2 ^ 59
def prefixEnd_4154389 : Nat := 4983230072969 + 3 ^ 40 * 4154389 * 2
def baseEnd_4154389 : Nat := 2133198382751451667631819

theorem tailTrace_4154389 : CollatzResearch.WordTrace tailWord_4154389 prefixEnd_4154389 2133198382751451667631819 := by
  unfold tailWord_4154389
  simp only [CollatzResearch.WordTrace]
  refine ⟨151523014946365640999082221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101015343297577093999388147 151523014946365640999082221)
  ·
    refine ⟨56821130604887115374655833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151523014946365640999082221 56821130604887115374655833)
    ·
      refine ⟨42615847953665336530991875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56821130604887115374655833 42615847953665336530991875)
      ·
        refine ⟨63923771930498004796487813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42615847953665336530991875 63923771930498004796487813)
        ·
          refine ⟨11985707236968375899341465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63923771930498004796487813 11985707236968375899341465)
          ·
            refine ⟨8989280427726281924506099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11985707236968375899341465 8989280427726281924506099)
            ·
              refine ⟨13483920641589422886759149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8989280427726281924506099 13483920641589422886759149)
              ·
                refine ⟨5056470240596033582534681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13483920641589422886759149 5056470240596033582534681)
                ·
                  refine ⟨3792352680447025186901011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5056470240596033582534681 3792352680447025186901011)
                  ·
                    refine ⟨5688529020670537780351517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792352680447025186901011 5688529020670537780351517)
                    ·
                      refine ⟨2133198382751451667631819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5688529020670537780351517 2133198382751451667631819)
                      ·
                        rfl

theorem cell23_4154389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_4154389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154389 prefixEnd_4154389 := by exact prefixLift 4154389
  have htrace : WordTrace (prefixWord ++ tailWord_4154389) baseStart_4154389 baseEnd_4154389 := by
    simpa [prefixWord, tailWord_4154389, baseEnd_4154389] using wordTrace_append hprefix tailTrace_4154389
  have hstable : (prefixWord ++ tailWord_4154389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154389).length < 2 ^ (prefixWord ++ tailWord_4154389).sum := by decide
  have hdescent : baseEnd_4154389 < baseStart_4154389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154399 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 1, 3, 2]
def baseStart_4154399 : Nat := 118140960795 + 4154399 * 2 ^ 59
def prefixEnd_4154399 : Nat := 4983230072969 + 3 ^ 40 * 4154399 * 2
def baseEnd_4154399 : Nat := 2133203517557996628506773

theorem tailTrace_4154399 : CollatzResearch.WordTrace tailWord_4154399 prefixEnd_4154399 2133203517557996628506773 := by
  unfold tailWord_4154399
  simp only [CollatzResearch.WordTrace]
  refine ⟨151523379676329412706946251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101015586450886275137964167 151523379676329412706946251)
  ·
    refine ⟨227285069514494119060419377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151523379676329412706946251 227285069514494119060419377)
    ·
      refine ⟨170463802135870589295314533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227285069514494119060419377 170463802135870589295314533)
      ·
        refine ⟨31961962900475735492871475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170463802135870589295314533 31961962900475735492871475)
        ·
          refine ⟨47942944350713603239307213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31961962900475735492871475 47942944350713603239307213)
          ·
            refine ⟨17978604131517601214740205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47942944350713603239307213 17978604131517601214740205)
            ·
              refine ⟨6741976549319100455527577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17978604131517601214740205 6741976549319100455527577)
              ·
                refine ⟨5056482411989325341645683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6741976549319100455527577 5056482411989325341645683)
                ·
                  refine ⟨7584723617983988012468525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5056482411989325341645683 7584723617983988012468525)
                  ·
                    refine ⟨2844271356743995504675697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7584723617983988012468525 2844271356743995504675697)
                    ·
                      refine ⟨2133203517557996628506773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2844271356743995504675697 2133203517557996628506773)
                      ·
                        rfl

theorem cell23_4154399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_4154399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154399 prefixEnd_4154399 := by exact prefixLift 4154399
  have htrace : WordTrace (prefixWord ++ tailWord_4154399) baseStart_4154399 baseEnd_4154399 := by
    simpa [prefixWord, tailWord_4154399, baseEnd_4154399] using wordTrace_append hprefix tailTrace_4154399
  have hstable : (prefixWord ++ tailWord_4154399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154399).length < 2 ^ (prefixWord ++ tailWord_4154399).sum := by decide
  have hdescent : baseEnd_4154399 < baseStart_4154399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154412 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 1, 4, 2]
def baseStart_4154412 : Nat := 118140960795 + 4154412 * 2 ^ 59
def prefixEnd_4154412 : Nat := 4983230072969 + 3 ^ 40 * 4154412 * 2
def baseEnd_4154412 : Nat := 2133210192806505077644213

theorem tailTrace_4154412 : CollatzResearch.WordTrace tailWord_4154412 prefixEnd_4154412 2133210192806505077644213 := by
  unfold tailWord_4154412
  simp only [CollatzResearch.WordTrace]
  refine ⟨75761926912641157963584745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101015902550188210618112993 75761926912641157963584745)
  ·
    refine ⟨56821445184480868472688559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75761926912641157963584745 56821445184480868472688559)
    ·
      refine ⟨85232167776721302709032839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56821445184480868472688559 85232167776721302709032839)
      ·
        refine ⟨127848251665081954063549259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85232167776721302709032839 127848251665081954063549259)
        ·
          refine ⟨191772377497622931095323889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127848251665081954063549259 191772377497622931095323889)
          ·
            refine ⟨143829283123217198321492917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191772377497622931095323889 143829283123217198321492917)
            ·
              refine ⟨13483995292801612342639961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143829283123217198321492917 13483995292801612342639961)
              ·
                refine ⟨10112996469601209256979971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13483995292801612342639961 10112996469601209256979971)
                ·
                  refine ⟨15169494704401813885469957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10112996469601209256979971 15169494704401813885469957)
                  ·
                    refine ⟨2844280257075340103525617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15169494704401813885469957 2844280257075340103525617)
                    ·
                      refine ⟨2133210192806505077644213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2844280257075340103525617 2133210192806505077644213)
                      ·
                        rfl

theorem cell23_4154412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_4154412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154412 prefixEnd_4154412 := by exact prefixLift 4154412
  have htrace : WordTrace (prefixWord ++ tailWord_4154412) baseStart_4154412 baseEnd_4154412 := by
    simpa [prefixWord, tailWord_4154412, baseEnd_4154412] using wordTrace_append hprefix tailTrace_4154412
  have hstable : (prefixWord ++ tailWord_4154412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154412).length < 2 ^ (prefixWord ++ tailWord_4154412).sum := by decide
  have hdescent : baseEnd_4154412 < baseStart_4154412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154525 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 10]
def baseStart_4154525 : Nat := 118140960795 + 4154525 * 2 ^ 59
def prefixEnd_4154525 : Nat := 4983230072969 + 3 ^ 40 * 4154525 * 2
def baseEnd_4154525 : Nat := 237029801791162570614577

theorem tailTrace_4154525 : CollatzResearch.WordTrace tailWord_4154525 prefixEnd_4154525 237029801791162570614577 := by
  unfold tailWord_4154525
  simp only [CollatzResearch.WordTrace]
  refine ⟨151527975273872936226033029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101018650182581957484022019 151527975273872936226033029)
  ·
    refine ⟨28411495363851175542381193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151527975273872936226033029 28411495363851175542381193)
    ·
      refine ⟨21308621522888381656785895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28411495363851175542381193 21308621522888381656785895)
      ·
        refine ⟨31962932284332572485178843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21308621522888381656785895 31962932284332572485178843)
        ·
          refine ⟨47944398426498858727768265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31962932284332572485178843 47944398426498858727768265)
          ·
            refine ⟨35958298819874144045826199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47944398426498858727768265 35958298819874144045826199)
            ·
              refine ⟨53937448229811216068739299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35958298819874144045826199 53937448229811216068739299)
              ·
                refine ⟨80906172344716824103108949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53937448229811216068739299 80906172344716824103108949)
                ·
                  refine ⟨237029801791162570614577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 80906172344716824103108949 237029801791162570614577)
                  ·
                    rfl

theorem cell23_4154525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_4154525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154525 prefixEnd_4154525 := by exact prefixLift 4154525
  have htrace : WordTrace (prefixWord ++ tailWord_4154525) baseStart_4154525 baseEnd_4154525 := by
    simpa [prefixWord, tailWord_4154525, baseEnd_4154525] using wordTrace_append hprefix tailTrace_4154525
  have hstable : (prefixWord ++ tailWord_4154525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154525).length < 2 ^ (prefixWord ++ tailWord_4154525).sum := by decide
  have hdescent : baseEnd_4154525 < baseStart_4154525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154586 : List Nat := [3, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3]
def baseStart_4154586 : Nat := 118140960795 + 4154586 * 2 ^ 59
def prefixEnd_4154586 : Nat := 4983230072969 + 3 ^ 40 * 4154586 * 2
def baseEnd_4154586 : Nat := 2133299538440387396868413

theorem tailTrace_4154586 : CollatzResearch.WordTrace tailWord_4154586 prefixEnd_4154586 2133299538440387396868413 := by
  unfold tailWord_4154586
  simp only [CollatzResearch.WordTrace]
  refine ⟨37882550031662985911000903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101020133417767962429335741 37882550031662985911000903)
  ·
    refine ⟨56823825047494478866501355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37882550031662985911000903 56823825047494478866501355)
    ·
      refine ⟨85235737571241718299752033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56823825047494478866501355 85235737571241718299752033)
      ·
        refine ⟨63926803178431288724814025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85235737571241718299752033 63926803178431288724814025)
        ·
          refine ⟨47945102383823466543610519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63926803178431288724814025 47945102383823466543610519)
          ·
            refine ⟨71917653575735199815415779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47945102383823466543610519 71917653575735199815415779)
            ·
              refine ⟨107876480363602799723123669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71917653575735199815415779 107876480363602799723123669)
              ·
                refine ⟨2528355008521940618510711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 107876480363602799723123669 2528355008521940618510711)
                ·
                  refine ⟨3792532512782910927766067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528355008521940618510711 3792532512782910927766067)
                  ·
                    refine ⟨5688798769174366391649101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792532512782910927766067 5688798769174366391649101)
                    ·
                      refine ⟨2133299538440387396868413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5688798769174366391649101 2133299538440387396868413)
                      ·
                        rfl

theorem cell23_4154586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_4154586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154586 prefixEnd_4154586 := by exact prefixLift 4154586
  have htrace : WordTrace (prefixWord ++ tailWord_4154586) baseStart_4154586 baseEnd_4154586 := by
    simpa [prefixWord, tailWord_4154586, baseEnd_4154586] using wordTrace_append hprefix tailTrace_4154586
  have hstable : (prefixWord ++ tailWord_4154586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154586).length < 2 ^ (prefixWord ++ tailWord_4154586).sum := by decide
  have hdescent : baseEnd_4154586 < baseStart_4154586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154603 : List Nat := [1, 1, 1, 1, 2, 6, 4, 2, 1, 1, 3]
def baseStart_4154603 : Nat := 118140960795 + 4154603 * 2 ^ 59
def prefixEnd_4154603 : Nat := 4983230072969 + 3 ^ 40 * 4154603 * 2
def baseEnd_4154603 : Nat := 2133308267611513830355835

theorem tailTrace_4154603 : CollatzResearch.WordTrace tailWord_4154603 prefixEnd_4154603 2133308267611513830355835 := by
  unfold tailWord_4154603
  simp only [CollatzResearch.WordTrace]
  refine ⟨151530820167590355547372463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101020546778393570364914975 151530820167590355547372463)
  ·
    refine ⟨227296230251385533321058695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151530820167590355547372463 227296230251385533321058695)
    ·
      refine ⟨340944345377078299981588043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227296230251385533321058695 340944345377078299981588043)
      ·
        refine ⟨511416518065617449972382065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340944345377078299981588043 511416518065617449972382065)
        ·
          refine ⟨383562388549213087479286549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511416518065617449972382065 383562388549213087479286549)
          ·
            refine ⟨17979486963244363475591557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 383562388549213087479286549 17979486963244363475591557)
            ·
              refine ⟨3371153805608318151673417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17979486963244363475591557 3371153805608318151673417)
              ·
                refine ⟨2528365354206238613755063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3371153805608318151673417 2528365354206238613755063)
                ·
                  refine ⟨3792548031309357920632595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528365354206238613755063 3792548031309357920632595)
                  ·
                    refine ⟨5688822046964036880948893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792548031309357920632595 5688822046964036880948893)
                    ·
                      refine ⟨2133308267611513830355835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5688822046964036880948893 2133308267611513830355835)
                      ·
                        rfl

theorem cell23_4154603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 1, 1, 3].length) (baseStart_4154603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154603 prefixEnd_4154603 := by exact prefixLift 4154603
  have htrace : WordTrace (prefixWord ++ tailWord_4154603) baseStart_4154603 baseEnd_4154603 := by
    simpa [prefixWord, tailWord_4154603, baseEnd_4154603] using wordTrace_append hprefix tailTrace_4154603
  have hstable : (prefixWord ++ tailWord_4154603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154603).length < 2 ^ (prefixWord ++ tailWord_4154603).sum := by decide
  have hdescent : baseEnd_4154603 < baseStart_4154603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154629 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 1, 2, 3]
def baseStart_4154629 : Nat := 118140960795 + 4154629 * 2 ^ 59
def prefixEnd_4154629 : Nat := 4983230072969 + 3 ^ 40 * 4154629 * 2
def baseEnd_4154629 : Nat := 2133321618108530728630715

theorem tailTrace_4154629 : CollatzResearch.WordTrace tailWord_4154629 prefixEnd_4154629 2133321618108530728630715 := by
  unfold tailWord_4154629
  simp only [CollatzResearch.WordTrace]
  refine ⟨151531768465496161987818941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101021178976997441325212627 151531768465496161987818941)
  ·
    refine ⟨56824413174561060745432103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151531768465496161987818941 56824413174561060745432103)
    ·
      refine ⟨85236619761841591118148155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56824413174561060745432103 85236619761841591118148155)
      ·
        refine ⟨127854929642762386677222233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85236619761841591118148155 127854929642762386677222233)
        ·
          refine ⟨95891197232071790007916675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127854929642762386677222233 95891197232071790007916675)
          ·
            refine ⟨143836795848107685011875013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95891197232071790007916675 143836795848107685011875013)
            ·
              refine ⟨26969399221520190939726565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143836795848107685011875013 26969399221520190939726565)
              ·
                refine ⟨5056762354035035801198731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26969399221520190939726565 5056762354035035801198731)
                ·
                  refine ⟨7585143531052553701798097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5056762354035035801198731 7585143531052553701798097)
                  ·
                    refine ⟨5688857648289415276348573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7585143531052553701798097 5688857648289415276348573)
                    ·
                      refine ⟨2133321618108530728630715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5688857648289415276348573 2133321618108530728630715)
                      ·
                        rfl

theorem cell23_4154629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_4154629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154629 prefixEnd_4154629 := by exact prefixLift 4154629
  have htrace : WordTrace (prefixWord ++ tailWord_4154629) baseStart_4154629 baseEnd_4154629 := by
    simpa [prefixWord, tailWord_4154629, baseEnd_4154629] using wordTrace_append hprefix tailTrace_4154629
  have hstable : (prefixWord ++ tailWord_4154629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154629).length < 2 ^ (prefixWord ++ tailWord_4154629).sum := by decide
  have hdescent : baseEnd_4154629 < baseStart_4154629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154653 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_4154653 : Nat := 118140960795 + 4154653 * 2 ^ 59
def prefixEnd_4154653 : Nat := 4983230072969 + 3 ^ 40 * 4154653 * 2
def baseEnd_4154653 : Nat := 711111313881412878243535

theorem tailTrace_4154653 : CollatzResearch.WordTrace tailWord_4154653 prefixEnd_4154653 711111313881412878243535 := by
  unfold tailWord_4154653
  simp only [CollatzResearch.WordTrace]
  refine ⟨151532643817409214086692613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101021762544939476057795075 151532643817409214086692613)
  ·
    refine ⟨28412370715764227641254865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151532643817409214086692613 28412370715764227641254865)
    ·
      refine ⟨21309278036823170730941149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28412370715764227641254865 21309278036823170730941149)
      ·
        refine ⟨7990979263808689024102931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21309278036823170730941149 7990979263808689024102931)
        ·
          refine ⟨11986468895713033536154397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7990979263808689024102931 11986468895713033536154397)
          ·
            refine ⟨4494925835892387576057899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11986468895713033536154397 4494925835892387576057899)
            ·
              refine ⟨6742388753838581364086849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494925835892387576057899 6742388753838581364086849)
              ·
                refine ⟨5056791565378936023065137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6742388753838581364086849 5056791565378936023065137)
                ·
                  refine ⟨3792593674034202017298853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5056791565378936023065137 3792593674034202017298853)
                  ·
                    refine ⟨711111313881412878243535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3792593674034202017298853 711111313881412878243535)
                    ·
                      rfl

theorem cell23_4154653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_4154653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154653 prefixEnd_4154653 := by exact prefixLift 4154653
  have htrace : WordTrace (prefixWord ++ tailWord_4154653) baseStart_4154653 baseEnd_4154653 := by
    simpa [prefixWord, tailWord_4154653, baseEnd_4154653] using wordTrace_append hprefix tailTrace_4154653
  have hstable : (prefixWord ++ tailWord_4154653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154653).length < 2 ^ (prefixWord ++ tailWord_4154653).sum := by decide
  have hdescent : baseEnd_4154653 < baseStart_4154653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154689 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4154689 : Nat := 118140960795 + 4154689 * 2 ^ 59
def prefixEnd_4154689 : Nat := 4983230072969 + 3 ^ 40 * 4154689 * 2
def baseEnd_4154689 : Nat := 2133352426947800493880439

theorem tailTrace_4154689 : CollatzResearch.WordTrace tailWord_4154689 prefixEnd_4154689 2133352426947800493880439 := by
  unfold tailWord_4154689
  simp only [CollatzResearch.WordTrace]
  refine ⟨151533956845278792235003121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101022637896852528156668747 151533956845278792235003121)
  ·
    refine ⟨113650467633959094176252341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151533956845278792235003121 113650467633959094176252341)
    ·
      refine ⟨10654731340683665079023657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113650467633959094176252341 10654731340683665079023657)
      ·
        refine ⟨7991048505512748809267743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10654731340683665079023657 7991048505512748809267743)
        ·
          refine ⟨11986572758269123213901615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7991048505512748809267743 11986572758269123213901615)
          ·
            refine ⟨17979859137403684820852423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986572758269123213901615 17979859137403684820852423)
            ·
              refine ⟨26969788706105527231278635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17979859137403684820852423 26969788706105527231278635)
              ·
                refine ⟨40454683059158290846917953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26969788706105527231278635 40454683059158290846917953)
                ·
                  refine ⟨30341012294368718135188465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40454683059158290846917953 30341012294368718135188465)
                  ·
                    refine ⟨22755759220776538601391349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30341012294368718135188465 22755759220776538601391349)
                    ·
                      refine ⟨2133352426947800493880439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22755759220776538601391349 2133352426947800493880439)
                      ·
                        rfl

theorem cell23_4154689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4154689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154689 prefixEnd_4154689 := by exact prefixLift 4154689
  have htrace : WordTrace (prefixWord ++ tailWord_4154689) baseStart_4154689 baseEnd_4154689 := by
    simpa [prefixWord, tailWord_4154689, baseEnd_4154689] using wordTrace_append hprefix tailTrace_4154689
  have hstable : (prefixWord ++ tailWord_4154689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154689).length < 2 ^ (prefixWord ++ tailWord_4154689).sum := by decide
  have hdescent : baseEnd_4154689 < baseStart_4154689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154727 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_4154727 : Nat := 118140960795 + 4154727 * 2 ^ 59
def prefixEnd_4154727 : Nat := 4983230072969 + 3 ^ 40 * 4154727 * 2
def baseEnd_4154727 : Nat := 2133371939212671345205265

theorem tailTrace_4154727 : CollatzResearch.WordTrace tailWord_4154727 prefixEnd_4154727 2133371939212671345205265 := by
  unfold tailWord_4154727
  simp only [CollatzResearch.WordTrace]
  refine ⟨151535342819141124724886435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101023561879427416483257623 151535342819141124724886435)
  ·
    refine ⟨227303014228711687087329653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151535342819141124724886435 227303014228711687087329653)
    ·
      refine ⟨21309657583941720664437155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227303014228711687087329653 21309657583941720664437155)
      ·
        refine ⟨31964486375912580996655733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21309657583941720664437155 31964486375912580996655733)
        ·
          refine ⟨2996670597741804468436475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31964486375912580996655733 2996670597741804468436475)
          ·
            refine ⟨4495005896612706702654713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996670597741804468436475 4495005896612706702654713)
            ·
              refine ⟨3371254422459530026991035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4495005896612706702654713 3371254422459530026991035)
              ·
                refine ⟨5056881633689295040486553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3371254422459530026991035 5056881633689295040486553)
                ·
                  refine ⟨3792661225266971280364915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5056881633689295040486553 3792661225266971280364915)
                  ·
                    refine ⟨5688991837900456920547373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792661225266971280364915 5688991837900456920547373)
                    ·
                      refine ⟨2133371939212671345205265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5688991837900456920547373 2133371939212671345205265)
                      ·
                        rfl

theorem cell23_4154727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_4154727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154727 prefixEnd_4154727 := by exact prefixLift 4154727
  have htrace : WordTrace (prefixWord ++ tailWord_4154727) baseStart_4154727 baseEnd_4154727 := by
    simpa [prefixWord, tailWord_4154727, baseEnd_4154727] using wordTrace_append hprefix tailTrace_4154727
  have hstable : (prefixWord ++ tailWord_4154727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154727).length < 2 ^ (prefixWord ++ tailWord_4154727).sum := by decide
  have hdescent : baseEnd_4154727 < baseStart_4154727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154752 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 1, 7]
def baseStart_4154752 : Nat := 118140960795 + 4154752 * 2 ^ 59
def prefixEnd_4154752 : Nat := 4983230072969 + 3 ^ 40 * 4154752 * 2
def baseEnd_4154752 : Nat := 711128258743011249130883

theorem tailTrace_4154752 : CollatzResearch.WordTrace tailWord_4154752 prefixEnd_4154752 711128258743011249130883 := by
  unfold tailWord_4154752
  simp only [CollatzResearch.WordTrace]
  refine ⟨75768127322025276997273255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101024169762700369329697673 75768127322025276997273255)
  ·
    refine ⟨113652190983037915495909883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75768127322025276997273255 113652190983037915495909883)
    ·
      refine ⟨170478286474556873243864825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113652190983037915495909883 170478286474556873243864825)
      ·
        refine ⟨127858714855917654932898619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170478286474556873243864825 127858714855917654932898619)
        ·
          refine ⟨191788072283876482399347929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127858714855917654932898619 191788072283876482399347929)
          ·
            refine ⟨143841054212907361799510947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191788072283876482399347929 143841054212907361799510947)
            ·
              refine ⟨215761581319361042699266421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143841054212907361799510947 215761581319361042699266421)
              ·
                refine ⟨20227648248690097753056227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215761581319361042699266421 20227648248690097753056227)
                ·
                  refine ⟨30341472373035146629584341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20227648248690097753056227 30341472373035146629584341)
                  ·
                    refine ⟨711128258743011249130883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30341472373035146629584341 711128258743011249130883)
                    ·
                      rfl

theorem cell23_4154752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_4154752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154752 prefixEnd_4154752 := by exact prefixLift 4154752
  have htrace : WordTrace (prefixWord ++ tailWord_4154752) baseStart_4154752 baseEnd_4154752 := by
    simpa [prefixWord, tailWord_4154752, baseEnd_4154752] using wordTrace_append hprefix tailTrace_4154752
  have hstable : (prefixWord ++ tailWord_4154752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154752).length < 2 ^ (prefixWord ++ tailWord_4154752).sum := by decide
  have hdescent : baseEnd_4154752 < baseStart_4154752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154818 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4154818 : Nat := 118140960795 + 4154818 * 2 ^ 59
def prefixEnd_4154818 : Nat := 4983230072969 + 3 ^ 40 * 4154818 * 2
def baseEnd_4154818 : Nat := 2133418665952230489167347

theorem tailTrace_4154818 : CollatzResearch.WordTrace tailWord_4154818 prefixEnd_4154818 2133418665952230489167347 := by
  unfold tailWord_4154818
  simp only [CollatzResearch.WordTrace]
  refine ⟨37884665465452861816612277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101025774574540964844299405 37884665465452861816612277)
  ·
    refine ⟨3551687387386205795307401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37884665465452861816612277 3551687387386205795307401)
    ·
      refine ⟨2663765540539654346480551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3551687387386205795307401 2663765540539654346480551)
      ·
        refine ⟨3995648310809481519720827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663765540539654346480551 3995648310809481519720827)
        ·
          refine ⟨5993472466214222279581241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995648310809481519720827 5993472466214222279581241)
          ·
            refine ⟨4495104349660666709685931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5993472466214222279581241 4495104349660666709685931)
            ·
              refine ⟨6742656524491000064528897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4495104349660666709685931 6742656524491000064528897)
              ·
                refine ⟨5056992393368250048396673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6742656524491000064528897 5056992393368250048396673)
                ·
                  refine ⟨3792744295026187536297505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5056992393368250048396673 3792744295026187536297505)
                  ·
                    refine ⟨2844558221269640652223129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3792744295026187536297505 2844558221269640652223129)
                    ·
                      refine ⟨2133418665952230489167347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2844558221269640652223129 2133418665952230489167347)
                      ·
                        rfl

theorem cell23_4154818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4154818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154818 prefixEnd_4154818 := by exact prefixLift 4154818
  have htrace : WordTrace (prefixWord ++ tailWord_4154818) baseStart_4154818 baseEnd_4154818 := by
    simpa [prefixWord, tailWord_4154818, baseEnd_4154818] using wordTrace_append hprefix tailTrace_4154818
  have hstable : (prefixWord ++ tailWord_4154818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154818).length < 2 ^ (prefixWord ++ tailWord_4154818).sum := by decide
  have hdescent : baseEnd_4154818 < baseStart_4154818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154876 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_4154876 : Nat := 118140960795 + 4154876 * 2 ^ 59
def prefixEnd_4154876 : Nat := 4983230072969 + 3 ^ 40 * 4154876 * 2
def baseEnd_4154876 : Nat := 711149482610063754080693

theorem tailTrace_4154876 : CollatzResearch.WordTrace tailWord_4154876 prefixEnd_4154876 711149482610063754080693 := by
  unfold tailWord_4154876
  simp only [CollatzResearch.WordTrace]
  refine ⟨75770388647800661586030241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101027184863734215448040321 75770388647800661586030241)
  ·
    refine ⟨56827791485850496189522681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75770388647800661586030241 56827791485850496189522681)
    ·
      refine ⟨42620843614387872142142011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56827791485850496189522681 42620843614387872142142011)
      ·
        refine ⟨63931265421581808213213017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42620843614387872142142011 63931265421581808213213017)
        ·
          refine ⟨47948449066186356159909763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63931265421581808213213017 47948449066186356159909763)
          ·
            refine ⟨71922673599279534239864645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47948449066186356159909763 71922673599279534239864645)
            ·
              refine ⟨13485501299864912669974621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71922673599279534239864645 13485501299864912669974621)
              ·
                refine ⟨5057062987449342251240483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13485501299864912669974621 5057062987449342251240483)
                ·
                  refine ⟨7585594481174013376860725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057062987449342251240483 7585594481174013376860725)
                  ·
                    refine ⟨711149482610063754080693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7585594481174013376860725 711149482610063754080693)
                    ·
                      rfl

theorem cell23_4154876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_4154876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154876 prefixEnd_4154876 := by exact prefixLift 4154876
  have htrace : WordTrace (prefixWord ++ tailWord_4154876) baseStart_4154876 baseEnd_4154876 := by
    simpa [prefixWord, tailWord_4154876, baseEnd_4154876] using wordTrace_append hprefix tailTrace_4154876
  have hstable : (prefixWord ++ tailWord_4154876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154876).length < 2 ^ (prefixWord ++ tailWord_4154876).sum := by decide
  have hdescent : baseEnd_4154876 < baseStart_4154876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154890 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_4154890 : Nat := 118140960795 + 4154890 * 2 ^ 59
def prefixEnd_4154890 : Nat := 4983230072969 + 3 ^ 40 * 4154890 * 2
def baseEnd_4154890 : Nat := 2133455636559354207467015

theorem tailTrace_4154890 : CollatzResearch.WordTrace tailWord_4154890 prefixEnd_4154890 2133455636559354207467015 := by
  unfold tailWord_4154890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37885321979387650890767531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101027525278367069042046749 37885321979387650890767531)
  ·
    refine ⟨56827982969081476336151297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37885321979387650890767531 56827982969081476336151297)
    ·
      refine ⟨42620987226811107252113473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56827982969081476336151297 42620987226811107252113473)
      ·
        refine ⟨31965740420108330439085105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42620987226811107252113473 31965740420108330439085105)
        ·
          refine ⟨23974305315081247829313829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31965740420108330439085105 23974305315081247829313829)
          ·
            refine ⟨4495182246577733967996343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23974305315081247829313829 4495182246577733967996343)
            ·
              refine ⟨6742773369866600951994515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4495182246577733967996343 6742773369866600951994515)
              ·
                refine ⟨10114160054799901427991773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6742773369866600951994515 10114160054799901427991773)
                ·
                  refine ⟨3792810020549963035496915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10114160054799901427991773 3792810020549963035496915)
                  ·
                    refine ⟨5689215030824944553245373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792810020549963035496915 5689215030824944553245373)
                    ·
                      refine ⟨2133455636559354207467015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5689215030824944553245373 2133455636559354207467015)
                      ·
                        rfl

theorem cell23_4154890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_4154890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154890 prefixEnd_4154890 := by exact prefixLift 4154890
  have htrace : WordTrace (prefixWord ++ tailWord_4154890) baseStart_4154890 baseEnd_4154890 := by
    simpa [prefixWord, tailWord_4154890, baseEnd_4154890] using wordTrace_append hprefix tailTrace_4154890
  have hstable : (prefixWord ++ tailWord_4154890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154890).length < 2 ^ (prefixWord ++ tailWord_4154890).sum := by decide
  have hdescent : baseEnd_4154890 < baseStart_4154890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154913 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_4154913 : Nat := 118140960795 + 4154913 * 2 ^ 59
def prefixEnd_4154913 : Nat := 4983230072969 + 3 ^ 40 * 4154913 * 2
def baseEnd_4154913 : Nat := 2133467446614407617479409

theorem tailTrace_4154913 : CollatzResearch.WordTrace tailWord_4154913 prefixEnd_4154913 2133467446614407617479409 := by
  unfold tailWord_4154913
  simp only [CollatzResearch.WordTrace]
  refine ⟨151542126796467278491157393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101028084530978185660771595 151542126796467278491157393)
  ·
    refine ⟨113656595097350458868368045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151542126796467278491157393 113656595097350458868368045)
    ·
      refine ⟨42621223161506422075638017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113656595097350458868368045 42621223161506422075638017)
      ·
        refine ⟨31965917371129816556728513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42621223161506422075638017 31965917371129816556728513)
        ·
          refine ⟨23974438028347362417546385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31965917371129816556728513 23974438028347362417546385)
          ·
            refine ⟨17980828521260521813159789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23974438028347362417546385 17980828521260521813159789)
            ·
              refine ⟨6742810695472695679934921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17980828521260521813159789 6742810695472695679934921)
              ·
                refine ⟨5057108021604521759951191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6742810695472695679934921 5057108021604521759951191)
                ·
                  refine ⟨7585662032406782639926787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057108021604521759951191 7585662032406782639926787)
                  ·
                    refine ⟨11378493048610173959890181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7585662032406782639926787 11378493048610173959890181)
                    ·
                      refine ⟨2133467446614407617479409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11378493048610173959890181 2133467446614407617479409)
                      ·
                        rfl

theorem cell23_4154913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_4154913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154913 prefixEnd_4154913 := by exact prefixLift 4154913
  have htrace : WordTrace (prefixWord ++ tailWord_4154913) baseStart_4154913 baseEnd_4154913 := by
    simpa [prefixWord, tailWord_4154913, baseEnd_4154913] using wordTrace_append hprefix tailTrace_4154913
  have hstable : (prefixWord ++ tailWord_4154913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154913).length < 2 ^ (prefixWord ++ tailWord_4154913).sum := by decide
  have hdescent : baseEnd_4154913 < baseStart_4154913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154933 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_4154933 : Nat := 118140960795 + 4154933 * 2 ^ 59
def prefixEnd_4154933 : Nat := 4983230072969 + 3 ^ 40 * 4154933 * 2
def baseEnd_4154933 : Nat := 2133477716227497539229317

theorem tailTrace_4154933 : CollatzResearch.WordTrace tailWord_4154933 prefixEnd_4154933 2133477716227497539229317 := by
  unfold tailWord_4154933
  simp only [CollatzResearch.WordTrace]
  refine ⟨151542856256394821906885453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101028570837596547937923635 151542856256394821906885453)
  ·
    refine ⟨56828571096148058215082045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151542856256394821906885453 56828571096148058215082045)
    ·
      refine ⟨21310714161055521830655767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56828571096148058215082045 21310714161055521830655767)
      ·
        refine ⟨31966071241583282745983651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21310714161055521830655767 31966071241583282745983651)
        ·
          refine ⟨47949106862374924118975477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31966071241583282745983651 47949106862374924118975477)
          ·
            refine ⟨4495228768347649136153951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47949106862374924118975477 4495228768347649136153951)
            ·
              refine ⟨6742843152521473704230927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4495228768347649136153951 6742843152521473704230927)
              ·
                refine ⟨10114264728782210556346391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6742843152521473704230927 10114264728782210556346391)
                ·
                  refine ⟨15171397093173315834519587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10114264728782210556346391 15171397093173315834519587)
                  ·
                    refine ⟨22757095639759973751779381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15171397093173315834519587 22757095639759973751779381)
                    ·
                      refine ⟨2133477716227497539229317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22757095639759973751779381 2133477716227497539229317)
                      ·
                        rfl

theorem cell23_4154933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_4154933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154933 prefixEnd_4154933 := by exact prefixLift 4154933
  have htrace : WordTrace (prefixWord ++ tailWord_4154933) baseStart_4154933 baseEnd_4154933 := by
    simpa [prefixWord, tailWord_4154933, baseEnd_4154933] using wordTrace_append hprefix tailTrace_4154933
  have hstable : (prefixWord ++ tailWord_4154933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154933).length < 2 ^ (prefixWord ++ tailWord_4154933).sum := by decide
  have hdescent : baseEnd_4154933 < baseStart_4154933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154940 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_4154940 : Nat := 118140960795 + 4154940 * 2 ^ 59
def prefixEnd_4154940 : Nat := 4983230072969 + 3 ^ 40 * 4154940 * 2
def baseEnd_4154940 : Nat := 711160436864026337280595

theorem tailTrace_4154940 : CollatzResearch.WordTrace tailWord_4154940 prefixEnd_4154940 711160436864026337280595 := by
  unfold tailWord_4154940
  simp only [CollatzResearch.WordTrace]
  refine ⟨75771555783684731051195137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101028741044912974734926849 75771555783684731051195137)
  ·
    refine ⟨56828666837763548288396353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75771555783684731051195137 56828666837763548288396353)
    ·
      refine ⟨42621500128322661216297265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56828666837763548288396353 42621500128322661216297265)
      ·
        refine ⟨31966125096241995912222949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42621500128322661216297265 31966125096241995912222949)
        ·
          refine ⟨5993648455545374233541803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31966125096241995912222949 5993648455545374233541803)
          ·
            refine ⟨8990472683318061350312705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5993648455545374233541803 8990472683318061350312705)
            ·
              refine ⟨6742854512488546012734529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8990472683318061350312705 6742854512488546012734529)
              ·
                refine ⟨5057140884366409509550897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6742854512488546012734529 5057140884366409509550897)
                ·
                  refine ⟨3792855663274807132163173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5057140884366409509550897 3792855663274807132163173)
                  ·
                    refine ⟨711160436864026337280595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3792855663274807132163173 711160436864026337280595)
                    ·
                      rfl

theorem cell23_4154940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_4154940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154940 prefixEnd_4154940 := by exact prefixLift 4154940
  have htrace : WordTrace (prefixWord ++ tailWord_4154940) baseStart_4154940 baseEnd_4154940 := by
    simpa [prefixWord, tailWord_4154940, baseEnd_4154940] using wordTrace_append hprefix tailTrace_4154940
  have hstable : (prefixWord ++ tailWord_4154940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154940).length < 2 ^ (prefixWord ++ tailWord_4154940).sum := by decide
  have hdescent : baseEnd_4154940 < baseStart_4154940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154941 : List Nat := [1, 4, 1, 3, 4, 1, 2, 2, 1, 1, 3]
def baseStart_4154941 : Nat := 118140960795 + 4154941 * 2 ^ 59
def prefixEnd_4154941 : Nat := 4983230072969 + 3 ^ 40 * 4154941 * 2
def baseEnd_4154941 : Nat := 2133481824072733507929281

theorem tailTrace_4154941 : CollatzResearch.WordTrace tailWord_4154941 prefixEnd_4154941 2133481824072733507929281 := by
  unfold tailWord_4154941
  simp only [CollatzResearch.WordTrace]
  refine ⟨151543148040365839273176677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101028765360243892848784451 151543148040365839273176677)
  ·
    refine ⟨28414340257568594863720627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151543148040365839273176677 28414340257568594863720627)
    ·
      refine ⟨42621510386352892295580941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28414340257568594863720627 42621510386352892295580941)
      ·
        refine ⟨15983066394882334610842853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42621510386352892295580941 15983066394882334610842853)
        ·
          refine ⟨2996824949040437739533035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15983066394882334610842853 2996824949040437739533035)
          ·
            refine ⟨4495237423560656609299553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996824949040437739533035 4495237423560656609299553)
            ·
              refine ⟨3371428067670492456974665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4495237423560656609299553 3371428067670492456974665)
              ·
                refine ⟨2528571050752869342730999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3371428067670492456974665 2528571050752869342730999)
                ·
                  refine ⟨3792856576129304014096499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528571050752869342730999 3792856576129304014096499)
                  ·
                    refine ⟨5689284864193956021144749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792856576129304014096499 5689284864193956021144749)
                    ·
                      refine ⟨2133481824072733507929281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5689284864193956021144749 2133481824072733507929281)
                      ·
                        rfl

theorem cell23_4154941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_4154941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154941 prefixEnd_4154941 := by exact prefixLift 4154941
  have htrace : WordTrace (prefixWord ++ tailWord_4154941) baseStart_4154941 baseEnd_4154941 := by
    simpa [prefixWord, tailWord_4154941, baseEnd_4154941] using wordTrace_append hprefix tailTrace_4154941
  have hstable : (prefixWord ++ tailWord_4154941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154941).length < 2 ^ (prefixWord ++ tailWord_4154941).sum := by decide
  have hdescent : baseEnd_4154941 < baseStart_4154941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154949 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_4154949 : Nat := 118140960795 + 4154949 * 2 ^ 59
def prefixEnd_4154949 : Nat := 4983230072969 + 3 ^ 40 * 4154949 * 2
def baseEnd_4154949 : Nat := 711161977305989825543081

theorem tailTrace_4154949 : CollatzResearch.WordTrace tailWord_4154949 prefixEnd_4154949 711161977305989825543081 := by
  unfold tailWord_4154949
  simp only [CollatzResearch.WordTrace]
  refine ⟨151543439824336856639467901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101028959882891237759645267 151543439824336856639467901)
  ·
    refine ⟨56828789934126321239800463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151543439824336856639467901 56828789934126321239800463)
    ·
      refine ⟨85243184901189481859700695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56828789934126321239800463 85243184901189481859700695)
      ·
        refine ⟨127864777351784222789551043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85243184901189481859700695 127864777351784222789551043)
        ·
          refine ⟨191797166027676334184326565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127864777351784222789551043 191797166027676334184326565)
          ·
            refine ⟨35961968630189312659561231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191797166027676334184326565 35961968630189312659561231)
            ·
              refine ⟨53942952945283968989341847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35961968630189312659561231 53942952945283968989341847)
              ·
                refine ⟨80914429417925953484012771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53942952945283968989341847 80914429417925953484012771)
                ·
                  refine ⟨121371644126888930226019157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80914429417925953484012771 121371644126888930226019157)
                  ·
                    refine ⟨711161977305989825543081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 121371644126888930226019157 711161977305989825543081)
                    ·
                      rfl

theorem cell23_4154949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_4154949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154949 prefixEnd_4154949 := by exact prefixLift 4154949
  have htrace : WordTrace (prefixWord ++ tailWord_4154949) baseStart_4154949 baseEnd_4154949 := by
    simpa [prefixWord, tailWord_4154949, baseEnd_4154949] using wordTrace_append hprefix tailTrace_4154949
  have hstable : (prefixWord ++ tailWord_4154949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154949).length < 2 ^ (prefixWord ++ tailWord_4154949).sum := by decide
  have hdescent : baseEnd_4154949 < baseStart_4154949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154959 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_4154959 : Nat := 118140960795 + 4154959 * 2 ^ 59
def prefixEnd_4154959 : Nat := 4983230072969 + 3 ^ 40 * 4154959 * 2
def baseEnd_4154959 : Nat := 2133491066724514437504197

theorem tailTrace_4154959 : CollatzResearch.WordTrace tailWord_4154959 prefixEnd_4154959 2133491066724514437504197 := by
  unfold tailWord_4154959
  simp only [CollatzResearch.WordTrace]
  refine ⟨151543804554300628347331931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101029203036200418898221287 151543804554300628347331931)
  ·
    refine ⟨227315706831450942520997897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151543804554300628347331931 227315706831450942520997897)
    ·
      refine ⟨170486780123588206890748423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227315706831450942520997897 170486780123588206890748423)
      ·
        refine ⟨255730170185382310336122635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170486780123588206890748423 255730170185382310336122635)
        ·
          refine ⟨383595255278073465504183953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255730170185382310336122635 383595255278073465504183953)
          ·
            refine ⟨287696441458555099128137965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383595255278073465504183953 287696441458555099128137965)
            ·
              refine ⟨107886165546958162173051737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287696441458555099128137965 107886165546958162173051737)
              ·
                refine ⟨80914624160218621629788803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107886165546958162173051737 80914624160218621629788803)
                ·
                  refine ⟨121371936240327932444683205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80914624160218621629788803 121371936240327932444683205)
                  ·
                    refine ⟨22757238045061487333378101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121371936240327932444683205 22757238045061487333378101)
                    ·
                      refine ⟨2133491066724514437504197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22757238045061487333378101 2133491066724514437504197)
                      ·
                        rfl

theorem cell23_4154959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_4154959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154959 prefixEnd_4154959 := by exact prefixLift 4154959
  have htrace : WordTrace (prefixWord ++ tailWord_4154959) baseStart_4154959 baseEnd_4154959 := by
    simpa [prefixWord, tailWord_4154959, baseEnd_4154959] using wordTrace_append hprefix tailTrace_4154959
  have hstable : (prefixWord ++ tailWord_4154959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154959).length < 2 ^ (prefixWord ++ tailWord_4154959).sum := by decide
  have hdescent : baseEnd_4154959 < baseStart_4154959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154997 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4154997 : Nat := 118140960795 + 4154997 * 2 ^ 59
def prefixEnd_4154997 : Nat := 4983230072969 + 3 ^ 40 * 4154997 * 2
def baseEnd_4154997 : Nat := 2133510578989385288829023

theorem tailTrace_4154997 : CollatzResearch.WordTrace tailWord_4154997 prefixEnd_4154997 2133510578989385288829023 := by
  unfold tailWord_4154997
  simp only [CollatzResearch.WordTrace]
  refine ⟨151545190528162960837215245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101030127018775307224810163 151545190528162960837215245)
  ·
    refine ⟨56829446448061110313955717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151545190528162960837215245 56829446448061110313955717)
    ·
      refine ⟨10655521209011458183866697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56829446448061110313955717 10655521209011458183866697)
      ·
        refine ⟨7991640906758593637900023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10655521209011458183866697 7991640906758593637900023)
        ·
          refine ⟨11987461360137890456850035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7991640906758593637900023 11987461360137890456850035)
          ·
            refine ⟨17981192040206835685275053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11987461360137890456850035 17981192040206835685275053)
            ·
              refine ⟨6742947015077563381978145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17981192040206835685275053 6742947015077563381978145)
              ·
                refine ⟨5057210261308172536483609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6742947015077563381978145 5057210261308172536483609)
                ·
                  refine ⟨3792907695981129402362707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5057210261308172536483609 3792907695981129402362707)
                  ·
                    refine ⟨5689361543971694103544061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3792907695981129402362707 5689361543971694103544061)
                    ·
                      refine ⟨2133510578989385288829023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5689361543971694103544061 2133510578989385288829023)
                      ·
                        rfl

theorem cell23_4154997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4154997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4154997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4154997 prefixEnd_4154997 := by exact prefixLift 4154997
  have htrace : WordTrace (prefixWord ++ tailWord_4154997) baseStart_4154997 baseEnd_4154997 := by
    simpa [prefixWord, tailWord_4154997, baseEnd_4154997] using wordTrace_append hprefix tailTrace_4154997
  have hstable : (prefixWord ++ tailWord_4154997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154997).length < 2 ^ (prefixWord ++ tailWord_4154997).sum := by decide
  have hdescent : baseEnd_4154997 < baseStart_4154997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155056 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 4, 5]
def baseStart_4155056 : Nat := 118140960795 + 4155056 * 2 ^ 59
def prefixEnd_4155056 : Nat := 4983230072969 + 3 ^ 40 * 4155056 * 2
def baseEnd_4155056 : Nat := 711180291449333519330417

theorem tailTrace_4155056 : CollatzResearch.WordTrace tailWord_4155056 prefixEnd_4155056 711180291449333519330417 := by
  unfold tailWord_4155056
  simp only [CollatzResearch.WordTrace]
  refine ⟨75773671217474606956806511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101031561623299475942408681 75773671217474606956806511)
  ·
    refine ⟨113660506826211910435209767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75773671217474606956806511 113660506826211910435209767)
    ·
      refine ⟨170490760239317865652814651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113660506826211910435209767 170490760239317865652814651)
      ·
        refine ⟨255736140358976798479221977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170490760239317865652814651 255736140358976798479221977)
        ·
          refine ⟨191802105269232598859416483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255736140358976798479221977 191802105269232598859416483)
          ·
            refine ⟨287703157903848898289124725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191802105269232598859416483 287703157903848898289124725)
            ·
              refine ⟨26972171053485834214605443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287703157903848898289124725 26972171053485834214605443)
              ·
                refine ⟨40458256580228751321908165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26972171053485834214605443 40458256580228751321908165)
                ·
                  refine ⟨7585923108792890872857781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40458256580228751321908165 7585923108792890872857781)
                  ·
                    refine ⟨711180291449333519330417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7585923108792890872857781 711180291449333519330417)
                    ·
                      rfl

theorem cell23_4155056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_4155056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155056 prefixEnd_4155056 := by exact prefixLift 4155056
  have htrace : WordTrace (prefixWord ++ tailWord_4155056) baseStart_4155056 baseEnd_4155056 := by
    simpa [prefixWord, tailWord_4155056, baseEnd_4155056] using wordTrace_append hprefix tailTrace_4155056
  have hstable : (prefixWord ++ tailWord_4155056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155056).length < 2 ^ (prefixWord ++ tailWord_4155056).sum := by decide
  have hdescent : baseEnd_4155056 < baseStart_4155056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155066 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_4155066 : Nat := 118140960795 + 4155066 * 2 ^ 59
def prefixEnd_4155066 : Nat := 4983230072969 + 3 ^ 40 * 4155066 * 2
def baseEnd_4155066 : Nat := 2133546009154545518866205

theorem tailTrace_4155066 : CollatzResearch.WordTrace tailWord_4155066 prefixEnd_4155066 2133546009154545518866205 := by
  unfold tailWord_4155066
  simp only [CollatzResearch.WordTrace]
  refine ⟨37886926791228246405369263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101031804776608657080984701 37886926791228246405369263)
  ·
    refine ⟨56830390186842369608053895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37886926791228246405369263 56830390186842369608053895)
    ·
      refine ⟨85245585280263554412080843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56830390186842369608053895 85245585280263554412080843)
      ·
        refine ⟨127868377920395331618121265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85245585280263554412080843 127868377920395331618121265)
        ·
          refine ⟨95901283440296498713590949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127868377920395331618121265 95901283440296498713590949)
          ·
            refine ⟨17981490645055593508798303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95901283440296498713590949 17981490645055593508798303)
            ·
              refine ⟨26972235967583390263197455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17981490645055593508798303 26972235967583390263197455)
              ·
                refine ⟨40458353951375085394796183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26972235967583390263197455 40458353951375085394796183)
                ·
                  refine ⟨60687530927062628092194275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40458353951375085394796183 60687530927062628092194275)
                  ·
                    refine ⟨91031296390593942138291413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60687530927062628092194275 91031296390593942138291413)
                    ·
                      refine ⟨2133546009154545518866205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91031296390593942138291413 2133546009154545518866205)
                      ·
                        rfl

theorem cell23_4155066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_4155066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155066 prefixEnd_4155066 := by exact prefixLift 4155066
  have htrace : WordTrace (prefixWord ++ tailWord_4155066) baseStart_4155066 baseEnd_4155066 := by
    simpa [prefixWord, tailWord_4155066, baseEnd_4155066] using wordTrace_append hprefix tailTrace_4155066
  have hstable : (prefixWord ++ tailWord_4155066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155066).length < 2 ^ (prefixWord ++ tailWord_4155066).sum := by decide
  have hdescent : baseEnd_4155066 < baseStart_4155066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155090 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_4155090 : Nat := 118140960795 + 4155090 * 2 ^ 59
def prefixEnd_4155090 : Nat := 4983230072969 + 3 ^ 40 * 4155090 * 2
def baseEnd_4155090 : Nat := 711186110896751141655365

theorem tailTrace_4155090 : CollatzResearch.WordTrace tailWord_4155090 prefixEnd_4155090 711186110896751141655365 := by
  unfold tailWord_4155090
  simp only [CollatzResearch.WordTrace]
  refine ⟨37887145629206509430087681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101032388344550691813567149 37887145629206509430087681)
  ·
    refine ⟨28415359221904882072565761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37887145629206509430087681 28415359221904882072565761)
    ·
      refine ⟨21311519416428661554424321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28415359221904882072565761 21311519416428661554424321)
      ·
        refine ⟨15983639562321496165818241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21311519416428661554424321 15983639562321496165818241)
        ·
          refine ⟨11987729671741122124363681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15983639562321496165818241 11987729671741122124363681)
          ·
            refine ⟨8990797253805841593272761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11987729671741122124363681 8990797253805841593272761)
            ·
              refine ⟨6743097940354381194954571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8990797253805841593272761 6743097940354381194954571)
              ·
                refine ⟨10114646910531571792431857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6743097940354381194954571 10114646910531571792431857)
                ·
                  refine ⟨7585985182898678844323893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10114646910531571792431857 7585985182898678844323893)
                  ·
                    refine ⟨711186110896751141655365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7585985182898678844323893 711186110896751141655365)
                    ·
                      rfl

theorem cell23_4155090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_4155090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155090 prefixEnd_4155090 := by exact prefixLift 4155090
  have htrace : WordTrace (prefixWord ++ tailWord_4155090) baseStart_4155090 baseEnd_4155090 := by
    simpa [prefixWord, tailWord_4155090, baseEnd_4155090] using wordTrace_append hprefix tailTrace_4155090
  have hstable : (prefixWord ++ tailWord_4155090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155090).length < 2 ^ (prefixWord ++ tailWord_4155090).sum := by decide
  have hdescent : baseEnd_4155090 < baseStart_4155090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155111 : List Nat := [1, 1, 5, 4, 2, 1, 2, 2, 5]
def baseStart_4155111 : Nat := 118140960795 + 4155111 * 2 ^ 59
def prefixEnd_4155111 : Nat := 4983230072969 + 3 ^ 40 * 4155111 * 2
def baseEnd_4155111 : Nat := 237063235087110871422611

theorem tailTrace_4155111 : CollatzResearch.WordTrace tailWord_4155111 prefixEnd_4155111 237063235087110871422611 := by
  unfold tailWord_4155111
  simp only [CollatzResearch.WordTrace]
  refine ⟨151549348449749958306865187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101032898966499972204576791 151549348449749958306865187)
  ·
    refine ⟨227324022674624937460297781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151549348449749958306865187 227324022674624937460297781)
    ·
      refine ⟨21311627125746087886902917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227324022674624937460297781 21311627125746087886902917)
      ·
        refine ⟨3995930086077391478794297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21311627125746087886902917 3995930086077391478794297)
        ·
          refine ⟨2996947564558043609095723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3995930086077391478794297 2996947564558043609095723)
          ·
            refine ⟨4495421346837065413643585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996947564558043609095723 4495421346837065413643585)
            ·
              refine ⟨3371566010127799060232689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4495421346837065413643585 3371566010127799060232689)
              ·
                refine ⟨2528674507595849295174517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3371566010127799060232689 2528674507595849295174517)
                ·
                  refine ⟨237063235087110871422611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2528674507595849295174517 237063235087110871422611)
                  ·
                    rfl

theorem cell23_4155111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 5].length) (baseStart_4155111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155111 prefixEnd_4155111 := by exact prefixLift 4155111
  have htrace : WordTrace (prefixWord ++ tailWord_4155111) baseStart_4155111 baseEnd_4155111 := by
    simpa [prefixWord, tailWord_4155111, baseEnd_4155111] using wordTrace_append hprefix tailTrace_4155111
  have hstable : (prefixWord ++ tailWord_4155111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155111).length < 2 ^ (prefixWord ++ tailWord_4155111).sum := by decide
  have hdescent : baseEnd_4155111 < baseStart_4155111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155116 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 8]
def baseStart_4155116 : Nat := 118140960795 + 4155116 * 2 ^ 59
def prefixEnd_4155116 : Nat := 4983230072969 + 3 ^ 40 * 4155116 * 2
def baseEnd_4155116 : Nat := 237063520354141147026775

theorem tailTrace_4155116 : CollatzResearch.WordTrace tailWord_4155116 prefixEnd_4155116 237063520354141147026775 := by
  unfold tailWord_4155116
  simp only [CollatzResearch.WordTrace]
  refine ⟨75774765407365922080398601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101033020543154562773864801 75774765407365922080398601)
  ·
    refine ⟨56831074055524441560298951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75774765407365922080398601 56831074055524441560298951)
    ·
      refine ⟨85246611083286662340448427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56831074055524441560298951 85246611083286662340448427)
      ·
        refine ⟨127869916624929993510672641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85246611083286662340448427 127869916624929993510672641)
        ·
          refine ⟨95902437468697495133004481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127869916624929993510672641 95902437468697495133004481)
          ·
            refine ⟨71926828101523121349753361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95902437468697495133004481 71926828101523121349753361)
            ·
              refine ⟨53945121076142341012315021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71926828101523121349753361 53945121076142341012315021)
              ·
                refine ⟨20229420403553377879618133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53945121076142341012315021 20229420403553377879618133)
                ·
                  refine ⟨237063520354141147026775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20229420403553377879618133 237063520354141147026775)
                  ·
                    rfl

theorem cell23_4155116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_4155116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155116 prefixEnd_4155116 := by exact prefixLift 4155116
  have htrace : WordTrace (prefixWord ++ tailWord_4155116) baseStart_4155116 baseEnd_4155116 := by
    simpa [prefixWord, tailWord_4155116, baseEnd_4155116] using wordTrace_append hprefix tailTrace_4155116
  have hstable : (prefixWord ++ tailWord_4155116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155116).length < 2 ^ (prefixWord ++ tailWord_4155116).sum := by decide
  have hdescent : baseEnd_4155116 < baseStart_4155116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155136 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_4155136 : Nat := 118140960795 + 4155136 * 2 ^ 59
def prefixEnd_4155136 : Nat := 4983230072969 + 3 ^ 40 * 4155136 * 2
def baseEnd_4155136 : Nat := 2133581952800360244990883

theorem tailTrace_4155136 : CollatzResearch.WordTrace tailWord_4155136 prefixEnd_4155136 2133581952800360244990883 := by
  unfold tailWord_4155136
  simp only [CollatzResearch.WordTrace]
  refine ⟨75775130137329693788262631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101033506849772925051016841 75775130137329693788262631)
  ·
    refine ⟨113662695205994540682393947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75775130137329693788262631 113662695205994540682393947)
    ·
      refine ⟨170494042808991811023590921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113662695205994540682393947 170494042808991811023590921)
      ·
        refine ⟨127870532106743858267693191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170494042808991811023590921 127870532106743858267693191)
        ·
          refine ⟨191805798160115787401539787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127870532106743858267693191 191805798160115787401539787)
          ·
            refine ⟨287708697240173681102309681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191805798160115787401539787 287708697240173681102309681)
            ·
              refine ⟨215781522930130260826732261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287708697240173681102309681 215781522930130260826732261)
              ·
                refine ⟨40459035549399423905012299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215781522930130260826732261 40459035549399423905012299)
                ·
                  refine ⟨60688553324099135857518449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40459035549399423905012299 60688553324099135857518449)
                  ·
                    refine ⟨45516414993074351893138837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60688553324099135857518449 45516414993074351893138837)
                    ·
                      refine ⟨2133581952800360244990883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45516414993074351893138837 2133581952800360244990883)
                      ·
                        rfl

theorem cell23_4155136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_4155136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155136 prefixEnd_4155136 := by exact prefixLift 4155136
  have htrace : WordTrace (prefixWord ++ tailWord_4155136) baseStart_4155136 baseEnd_4155136 := by
    simpa [prefixWord, tailWord_4155136, baseEnd_4155136] using wordTrace_append hprefix tailTrace_4155136
  have hstable : (prefixWord ++ tailWord_4155136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155136).length < 2 ^ (prefixWord ++ tailWord_4155136).sum := by decide
  have hdescent : baseEnd_4155136 < baseStart_4155136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155154 : List Nat := [3, 2, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_4155154 : Nat := 118140960795 + 4155154 * 2 ^ 59
def prefixEnd_4155154 : Nat := 4983230072969 + 3 ^ 40 * 4155154 * 2
def baseEnd_4155154 : Nat := 711197065150713724855267

theorem tailTrace_4155154 : CollatzResearch.WordTrace tailWord_4155154 prefixEnd_4155154 711197065150713724855267 := by
  unfold tailWord_4155154
  simp only [CollatzResearch.WordTrace]
  refine ⟨37887729197148544162670129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101033944525729451100453677 37887729197148544162670129)
  ·
    refine ⟨28415796897861408122002597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37887729197148544162670129 28415796897861408122002597)
    ·
      refine ⟨5327961918349014022875487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28415796897861408122002597 5327961918349014022875487)
      ·
        refine ⟨7991942877523521034313231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327961918349014022875487 7991942877523521034313231)
        ·
          refine ⟨11987914316285281551469847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7991942877523521034313231 11987914316285281551469847)
          ·
            refine ⟨17981871474427922327204771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11987914316285281551469847 17981871474427922327204771)
            ·
              refine ⟨26972807211641883490807157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17981871474427922327204771 26972807211641883490807157)
              ·
                refine ⟨2528700676091426577263171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26972807211641883490807157 2528700676091426577263171)
                ·
                  refine ⟨3793051014137139865894757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528700676091426577263171 3793051014137139865894757)
                  ·
                    refine ⟨711197065150713724855267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3793051014137139865894757 711197065150713724855267)
                    ·
                      rfl

theorem cell23_4155154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_4155154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155154 prefixEnd_4155154 := by exact prefixLift 4155154
  have htrace : WordTrace (prefixWord ++ tailWord_4155154) baseStart_4155154 baseEnd_4155154 := by
    simpa [prefixWord, tailWord_4155154, baseEnd_4155154] using wordTrace_append hprefix tailTrace_4155154
  have hstable : (prefixWord ++ tailWord_4155154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155154).length < 2 ^ (prefixWord ++ tailWord_4155154).sum := by decide
  have hdescent : baseEnd_4155154 < baseStart_4155154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155163 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 1, 5]
def baseStart_4155163 : Nat := 118140960795 + 4155163 * 2 ^ 59
def prefixEnd_4155163 : Nat := 4983230072969 + 3 ^ 40 * 4155163 * 2
def baseEnd_4155163 : Nat := 711198605592677213117753

theorem tailTrace_4155163 : CollatzResearch.WordTrace tailWord_4155163 prefixEnd_4155163 711198605592677213117753 := by
  unfold tailWord_4155163
  simp only [CollatzResearch.WordTrace]
  refine ⟨151551245045561571187758143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101034163363707714125172095 151551245045561571187758143)
  ·
    refine ⟨227326867568342356781637215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151551245045561571187758143 227326867568342356781637215)
    ·
      refine ⟨340990301352513535172455823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227326867568342356781637215 340990301352513535172455823)
      ·
        refine ⟨511485452028770302758683735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340990301352513535172455823 511485452028770302758683735)
        ·
          refine ⟨767228178043155454138025603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511485452028770302758683735 767228178043155454138025603)
          ·
            refine ⟨1150842267064733181207038405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767228178043155454138025603 1150842267064733181207038405)
            ·
              refine ⟨215782925074637471476319701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1150842267064733181207038405 215782925074637471476319701)
              ·
                refine ⟨5057412306436815737726243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 215782925074637471476319701 5057412306436815737726243)
                ·
                  refine ⟨7586118459655223606589365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057412306436815737726243 7586118459655223606589365)
                  ·
                    refine ⟨711198605592677213117753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7586118459655223606589365 711198605592677213117753)
                    ·
                      rfl

theorem cell23_4155163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 5].length) (baseStart_4155163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155163 prefixEnd_4155163 := by exact prefixLift 4155163
  have htrace : WordTrace (prefixWord ++ tailWord_4155163) baseStart_4155163 baseEnd_4155163 := by
    simpa [prefixWord, tailWord_4155163, baseEnd_4155163] using wordTrace_append hprefix tailTrace_4155163
  have hstable : (prefixWord ++ tailWord_4155163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155163).length < 2 ^ (prefixWord ++ tailWord_4155163).sum := by decide
  have hdescent : baseEnd_4155163 < baseStart_4155163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155197 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_4155197 : Nat := 118140960795 + 4155197 * 2 ^ 59
def prefixEnd_4155197 : Nat := 4983230072969 + 3 ^ 40 * 4155197 * 2
def baseEnd_4155197 : Nat := 711204425040094835442701

theorem tailTrace_4155197 : CollatzResearch.WordTrace tailWord_4155197 prefixEnd_4155197 711204425040094835442701 := by
  unfold tailWord_4155197
  simp only [CollatzResearch.WordTrace]
  refine ⟨151552485127438394994495845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101034990084958929996330563 151552485127438394994495845)
  ·
    refine ⟨28416090961394699061467971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151552485127438394994495845 28416090961394699061467971)
    ·
      refine ⟨42624136442092048592201957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28416090961394699061467971 42624136442092048592201957)
      ·
        refine ⟨7992025582892259111037867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42624136442092048592201957 7992025582892259111037867)
        ·
          refine ⟨11988038374338388666556801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7992025582892259111037867 11988038374338388666556801)
          ·
            refine ⟨8991028780753791499917601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11988038374338388666556801 8991028780753791499917601)
            ·
              refine ⟨6743271585565343624938201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8991028780753791499917601 6743271585565343624938201)
              ·
                refine ⟨5057453689174007718703651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6743271585565343624938201 5057453689174007718703651)
                ·
                  refine ⟨7586180533761011578055477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057453689174007718703651 7586180533761011578055477)
                  ·
                    refine ⟨711204425040094835442701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7586180533761011578055477 711204425040094835442701)
                    ·
                      rfl

theorem cell23_4155197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_4155197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155197 prefixEnd_4155197 := by exact prefixLift 4155197
  have htrace : WordTrace (prefixWord ++ tailWord_4155197) baseStart_4155197 baseEnd_4155197 := by
    simpa [prefixWord, tailWord_4155197, baseEnd_4155197] using wordTrace_append hprefix tailTrace_4155197
  have hstable : (prefixWord ++ tailWord_4155197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155197).length < 2 ^ (prefixWord ++ tailWord_4155197).sum := by decide
  have hdescent : baseEnd_4155197 < baseStart_4155197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155220 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_4155220 : Nat := 118140960795 + 4155220 * 2 ^ 59
def prefixEnd_4155220 : Nat := 4983230072969 + 3 ^ 40 * 4155220 * 2
def baseEnd_4155220 : Nat := 2133625085175337916340497

theorem tailTrace_4155220 : CollatzResearch.WordTrace tailWord_4155220 prefixEnd_4155220 2133625085175337916340497 := by
  unfold tailWord_4155220
  simp only [CollatzResearch.WordTrace]
  refine ⟨75776662003177534961291557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101035549337570046615055409 75776662003177534961291557)
  ·
    refine ⟨14208124125595787805242167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75776662003177534961291557 14208124125595787805242167)
    ·
      refine ⟨21312186188393681707863251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14208124125595787805242167 21312186188393681707863251)
      ·
        refine ⟨31968279282590522561794877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21312186188393681707863251 31968279282590522561794877)
        ·
          refine ⟨11988104730971445960673079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31968279282590522561794877 11988104730971445960673079)
          ·
            refine ⟨17982157096457168941009619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11988104730971445960673079 17982157096457168941009619)
            ·
              refine ⟨26973235644685753411514429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17982157096457168941009619 26973235644685753411514429)
              ·
                refine ⟨10114963366757157529317911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26973235644685753411514429 10114963366757157529317911)
                ·
                  refine ⟨15172445050135736293976867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10114963366757157529317911 15172445050135736293976867)
                  ·
                    refine ⟨22758667575203604440965301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15172445050135736293976867 22758667575203604440965301)
                    ·
                      refine ⟨2133625085175337916340497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22758667575203604440965301 2133625085175337916340497)
                      ·
                        rfl

theorem cell23_4155220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_4155220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155220 prefixEnd_4155220 := by exact prefixLift 4155220
  have htrace : WordTrace (prefixWord ++ tailWord_4155220) baseStart_4155220 baseEnd_4155220 := by
    simpa [prefixWord, tailWord_4155220, baseEnd_4155220] using wordTrace_append hprefix tailTrace_4155220
  have hstable : (prefixWord ++ tailWord_4155220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155220).length < 2 ^ (prefixWord ++ tailWord_4155220).sum := by decide
  have hdescent : baseEnd_4155220 < baseStart_4155220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155228 : List Nat := [2, 2, 4, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_4155228 : Nat := 118140960795 + 4155228 * 2 ^ 59
def prefixEnd_4155228 : Nat := 4983230072969 + 3 ^ 40 * 4155228 * 2
def baseEnd_4155228 : Nat := 2133629193020573885040461

theorem tailTrace_4155228 : CollatzResearch.WordTrace tailWord_4155228 prefixEnd_4155228 2133629193020573885040461 := by
  unfold tailWord_4155228
  simp only [CollatzResearch.WordTrace]
  refine ⟨75776807895163043644437169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101035743860217391525916225 75776807895163043644437169)
  ·
    refine ⟨56832605921372282733327877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75776807895163043644437169 56832605921372282733327877)
    ·
      refine ⟨10656113610257303012498977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56832605921372282733327877 10656113610257303012498977)
      ·
        refine ⟨7992085207692977259374233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10656113610257303012498977 7992085207692977259374233)
        ·
          refine ⟨5994063905769732944530675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7992085207692977259374233 5994063905769732944530675)
          ·
            refine ⟨8991095858654599416796013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994063905769732944530675 8991095858654599416796013)
            ·
              refine ⟨3371660946995474781298505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8991095858654599416796013 3371660946995474781298505)
              ·
                refine ⟨2528745710246606085973879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3371660946995474781298505 2528745710246606085973879)
                ·
                  refine ⟨3793118565369909128960819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528745710246606085973879 3793118565369909128960819)
                  ·
                    refine ⟨5689677848054863693441229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3793118565369909128960819 5689677848054863693441229)
                    ·
                      refine ⟨2133629193020573885040461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5689677848054863693441229 2133629193020573885040461)
                      ·
                        rfl

theorem cell23_4155228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_4155228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155228 prefixEnd_4155228 := by exact prefixLift 4155228
  have htrace : WordTrace (prefixWord ++ tailWord_4155228) baseStart_4155228 baseEnd_4155228 := by
    simpa [prefixWord, tailWord_4155228, baseEnd_4155228] using wordTrace_append hprefix tailTrace_4155228
  have hstable : (prefixWord ++ tailWord_4155228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155228).length < 2 ^ (prefixWord ++ tailWord_4155228).sum := by decide
  have hdescent : baseEnd_4155228 < baseStart_4155228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155244 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 2, 4]
def baseStart_4155244 : Nat := 118140960795 + 4155244 * 2 ^ 59
def prefixEnd_4155244 : Nat := 4983230072969 + 3 ^ 40 * 4155244 * 2
def baseEnd_4155244 : Nat := 711212469570348607480129

theorem tailTrace_4155244 : CollatzResearch.WordTrace tailWord_4155244 prefixEnd_4155244 711212469570348607480129 := by
  unfold tailWord_4155244
  simp only [CollatzResearch.WordTrace]
  refine ⟨75777099679134061010728393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101036132905512081347637857 75777099679134061010728393)
  ·
    refine ⟨56832824759350545758046295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75777099679134061010728393 56832824759350545758046295)
    ·
      refine ⟨85249237139025818637069443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56832824759350545758046295 85249237139025818637069443)
      ·
        refine ⟨127873855708538727955604165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85249237139025818637069443 127873855708538727955604165)
        ·
          refine ⟨23976347945351011491675781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127873855708538727955604165 23976347945351011491675781)
          ·
            refine ⟨4495565239753314654689209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23976347945351011491675781 4495565239753314654689209)
            ·
              refine ⟨3371673929814985991016907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4495565239753314654689209 3371673929814985991016907)
              ·
                refine ⟨5057510894722478986525361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3371673929814985991016907 5057510894722478986525361)
                ·
                  refine ⟨3793133171041859239894021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5057510894722478986525361 3793133171041859239894021)
                  ·
                    refine ⟨711212469570348607480129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3793133171041859239894021 711212469570348607480129)
                    ·
                      rfl

theorem cell23_4155244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_4155244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155244 prefixEnd_4155244 := by exact prefixLift 4155244
  have htrace : WordTrace (prefixWord ++ tailWord_4155244) baseStart_4155244 baseEnd_4155244 := by
    simpa [prefixWord, tailWord_4155244, baseEnd_4155244] using wordTrace_append hprefix tailTrace_4155244
  have hstable : (prefixWord ++ tailWord_4155244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155244).length < 2 ^ (prefixWord ++ tailWord_4155244).sum := by decide
  have hdescent : baseEnd_4155244 < baseStart_4155244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155250 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_4155250 : Nat := 118140960795 + 4155250 * 2 ^ 59
def prefixEnd_4155250 : Nat := 4983230072969 + 3 ^ 40 * 4155250 * 2
def baseEnd_4155250 : Nat := 2133640489594972798965359

theorem tailTrace_4155250 : CollatzResearch.WordTrace tailWord_4155250 prefixEnd_4155250 2133640489594972798965359 := by
  unfold tailWord_4155250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37888604549061596261543801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101036278797497590030783469 37888604549061596261543801)
  ·
    refine ⟨28416453411796197196157851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37888604549061596261543801 28416453411796197196157851)
    ·
      refine ⟨42624680117694295794236777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28416453411796197196157851 42624680117694295794236777)
      ·
        refine ⟨31968510088270721845677583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42624680117694295794236777 31968510088270721845677583)
        ·
          refine ⟨47952765132406082768516375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31968510088270721845677583 47952765132406082768516375)
          ·
            refine ⟨71929147698609124152774563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47952765132406082768516375 71929147698609124152774563)
            ·
              refine ⟨107893721547913686229161845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71929147698609124152774563 107893721547913686229161845)
              ·
                refine ⟨10115036395116908083983923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107893721547913686229161845 10115036395116908083983923)
                ·
                  refine ⟨15172554592675362125975885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10115036395116908083983923 15172554592675362125975885)
                  ·
                    refine ⟨5689707972253260797240957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15172554592675362125975885 5689707972253260797240957)
                    ·
                      refine ⟨2133640489594972798965359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5689707972253260797240957 2133640489594972798965359)
                      ·
                        rfl

theorem cell23_4155250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_4155250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155250 prefixEnd_4155250 := by exact prefixLift 4155250
  have htrace : WordTrace (prefixWord ++ tailWord_4155250) baseStart_4155250 baseEnd_4155250 := by
    simpa [prefixWord, tailWord_4155250, baseEnd_4155250] using wordTrace_append hprefix tailTrace_4155250
  have hstable : (prefixWord ++ tailWord_4155250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155250).length < 2 ^ (prefixWord ++ tailWord_4155250).sum := by decide
  have hdescent : baseEnd_4155250 < baseStart_4155250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155254 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4155254 : Nat := 118140960795 + 4155254 * 2 ^ 59
def prefixEnd_4155254 : Nat := 4983230072969 + 3 ^ 40 * 4155254 * 2
def baseEnd_4155254 : Nat := 2133642543517590783315341

theorem tailTrace_4155254 : CollatzResearch.WordTrace tailWord_4155254 prefixEnd_4155254 2133642543517590783315341 := by
  unfold tailWord_4155254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472160255514493358082551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101036376058821262486213877 9472160255514493358082551)
  ·
    refine ⟨14208240383271740037123827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9472160255514493358082551 14208240383271740037123827)
    ·
      refine ⟨21312360574907610055685741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14208240383271740037123827 21312360574907610055685741)
      ·
        refine ⟨7992135215590353770882153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21312360574907610055685741 7992135215590353770882153)
        ·
          refine ⟨5994101411692765328161615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7992135215590353770882153 5994101411692765328161615)
          ·
            refine ⟨8991152117539147992242423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994101411692765328161615 8991152117539147992242423)
            ·
              refine ⟨13486728176308721988363635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991152117539147992242423 13486728176308721988363635)
              ·
                refine ⟨20230092264463082982545453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13486728176308721988363635 20230092264463082982545453)
                ·
                  refine ⟨7586284599173656118454545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20230092264463082982545453 7586284599173656118454545)
                  ·
                    refine ⟨5689713449380242088840909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7586284599173656118454545 5689713449380242088840909)
                    ·
                      refine ⟨2133642543517590783315341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5689713449380242088840909 2133642543517590783315341)
                      ·
                        rfl

theorem cell23_4155254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4155254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155254 prefixEnd_4155254 := by exact prefixLift 4155254
  have htrace : WordTrace (prefixWord ++ tailWord_4155254) baseStart_4155254 baseEnd_4155254 := by
    simpa [prefixWord, tailWord_4155254, baseEnd_4155254] using wordTrace_append hprefix tailTrace_4155254
  have hstable : (prefixWord ++ tailWord_4155254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155254).length < 2 ^ (prefixWord ++ tailWord_4155254).sum := by decide
  have hdescent : baseEnd_4155254 < baseStart_4155254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155284 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_4155284 : Nat := 118140960795 + 4155284 * 2 ^ 59
def prefixEnd_4155284 : Nat := 4983230072969 + 3 ^ 40 * 4155284 * 2
def baseEnd_4155284 : Nat := 2133657947937225665940203

theorem tailTrace_4155284 : CollatzResearch.WordTrace tailWord_4155284 prefixEnd_4155284 2133657947937225665940203 := by
  unfold tailWord_4155284
  simp only [CollatzResearch.WordTrace]
  refine ⟨75777829139061604426456453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101037105518748805901941937 75777829139061604426456453)
  ·
    refine ⟨14208342963574050829960585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75777829139061604426456453 14208342963574050829960585)
    ·
      refine ⟨10656257222680538122470439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14208342963574050829960585 10656257222680538122470439)
      ·
        refine ⟨15984385834020807183705659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10656257222680538122470439 15984385834020807183705659)
        ·
          refine ⟨23976578751031210775558489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15984385834020807183705659 23976578751031210775558489)
          ·
            refine ⟨17982434063273408081668867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23976578751031210775558489 17982434063273408081668867)
            ·
              refine ⟨26973651094910112122503301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17982434063273408081668867 26973651094910112122503301)
              ·
                refine ⟨5057559580295646022969369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26973651094910112122503301 5057559580295646022969369)
                ·
                  refine ⟨3793169685221734517227027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5057559580295646022969369 3793169685221734517227027)
                  ·
                    refine ⟨5689754527832601775840541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3793169685221734517227027 5689754527832601775840541)
                    ·
                      refine ⟨2133657947937225665940203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5689754527832601775840541 2133657947937225665940203)
                      ·
                        rfl

theorem cell23_4155284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_4155284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155284 prefixEnd_4155284 := by exact prefixLift 4155284
  have htrace : WordTrace (prefixWord ++ tailWord_4155284) baseStart_4155284 baseEnd_4155284 := by
    simpa [prefixWord, tailWord_4155284, baseEnd_4155284] using wordTrace_append hprefix tailTrace_4155284
  have hstable : (prefixWord ++ tailWord_4155284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155284).length < 2 ^ (prefixWord ++ tailWord_4155284).sum := by decide
  have hdescent : baseEnd_4155284 < baseStart_4155284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155290 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_4155290 : Nat := 118140960795 + 4155290 * 2 ^ 59
def prefixEnd_4155290 : Nat := 4983230072969 + 3 ^ 40 * 4155290 * 2
def baseEnd_4155290 : Nat := 2133661028821152642465175

theorem tailTrace_4155290 : CollatzResearch.WordTrace tailWord_4155290 prefixEnd_4155290 2133661028821152642465175 := by
  unfold tailWord_4155290
  simp only [CollatzResearch.WordTrace]
  refine ⟨37888969279025367969407831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101037251410734314585087549 37888969279025367969407831)
  ·
    refine ⟨56833453918538051954111747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37888969279025367969407831 56833453918538051954111747)
    ·
      refine ⟨85250180877807077931167621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56833453918538051954111747 85250180877807077931167621)
      ·
        refine ⟨15984408914588827112093929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85250180877807077931167621 15984408914588827112093929)
        ·
          refine ⟨11988306685941620334070447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15984408914588827112093929 11988306685941620334070447)
          ·
            refine ⟨17982460028912430501105671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11988306685941620334070447 17982460028912430501105671)
            ·
              refine ⟨26973690043368645751658507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17982460028912430501105671 26973690043368645751658507)
              ·
                refine ⟨40460535065052968627487761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26973690043368645751658507 40460535065052968627487761)
                ·
                  refine ⟨30345401298789726470615821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40460535065052968627487761 30345401298789726470615821)
                  ·
                    refine ⟨11379525487046147426480933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30345401298789726470615821 11379525487046147426480933)
                    ·
                      refine ⟨2133661028821152642465175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11379525487046147426480933 2133661028821152642465175)
                      ·
                        rfl

theorem cell23_4155290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_4155290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155290 prefixEnd_4155290 := by exact prefixLift 4155290
  have htrace : WordTrace (prefixWord ++ tailWord_4155290) baseStart_4155290 baseEnd_4155290 := by
    simpa [prefixWord, tailWord_4155290, baseEnd_4155290] using wordTrace_append hprefix tailTrace_4155290
  have hstable : (prefixWord ++ tailWord_4155290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155290).length < 2 ^ (prefixWord ++ tailWord_4155290).sum := by decide
  have hdescent : baseEnd_4155290 < baseStart_4155290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155300 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_4155300 : Nat := 118140960795 + 4155300 * 2 ^ 59
def prefixEnd_4155300 : Nat := 4983230072969 + 3 ^ 40 * 4155300 * 2
def baseEnd_4155300 : Nat := 711222054542565867780043

theorem tailTrace_4155300 : CollatzResearch.WordTrace tailWord_4155300 prefixEnd_4155300 711222054542565867780043 := by
  unfold tailWord_4155300
  simp only [CollatzResearch.WordTrace]
  refine ⟨75778120923032621792747677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101037494564043495723663569 75778120923032621792747677)
  ·
    refine ⟨28416795346137233172280379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75778120923032621792747677 28416795346137233172280379)
    ·
      refine ⟨42625193019205849758420569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28416795346137233172280379 42625193019205849758420569)
      ·
        refine ⟨31968894764404387318815427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42625193019205849758420569 31968894764404387318815427)
        ·
          refine ⟨47953342146606580978223141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31968894764404387318815427 47953342146606580978223141)
          ·
            refine ⟨8991251652488733933416839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47953342146606580978223141 8991251652488733933416839)
            ·
              refine ⟨13486877478733100900125259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991251652488733933416839 13486877478733100900125259)
              ·
                refine ⟨20230316218099651350187889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13486877478733100900125259 20230316218099651350187889)
                ·
                  refine ⟨15172737163574738512640917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20230316218099651350187889 15172737163574738512640917)
                  ·
                    refine ⟨711222054542565867780043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15172737163574738512640917 711222054542565867780043)
                    ·
                      rfl

theorem cell23_4155300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_4155300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155300 prefixEnd_4155300 := by exact prefixLift 4155300
  have htrace : WordTrace (prefixWord ++ tailWord_4155300) baseStart_4155300 baseEnd_4155300 := by
    simpa [prefixWord, tailWord_4155300, baseEnd_4155300] using wordTrace_append hprefix tailTrace_4155300
  have hstable : (prefixWord ++ tailWord_4155300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155300).length < 2 ^ (prefixWord ++ tailWord_4155300).sum := by decide
  have hdescent : baseEnd_4155300 < baseStart_4155300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155397 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_4155397 : Nat := 118140960795 + 4155397 * 2 ^ 59
def prefixEnd_4155397 : Nat := 4983230072969 + 3 ^ 40 * 4155397 * 2
def baseEnd_4155397 : Nat := 2133715971251183723827183

theorem tailTrace_4155397 : CollatzResearch.WordTrace tailWord_4155397 prefixEnd_4155397 2133715971251183723827183 := by
  unfold tailWord_4155397
  simp only [CollatzResearch.WordTrace]
  refine ⟨151559779726713829151776445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101039853151142552767850963 151559779726713829151776445)
  ·
    refine ⟨56834917397517685931916167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151559779726713829151776445 56834917397517685931916167)
    ·
      refine ⟨85252376096276528897874251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56834917397517685931916167 85252376096276528897874251)
      ·
        refine ⟨127878564144414793346811377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85252376096276528897874251 127878564144414793346811377)
        ·
          refine ⟨95908923108311095010108533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127878564144414793346811377 95908923108311095010108533)
          ·
            refine ⟨8991461541404165157197675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95908923108311095010108533 8991461541404165157197675)
            ·
              refine ⟨13487192312106247735796513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991461541404165157197675 13487192312106247735796513)
              ·
                refine ⟨10115394234079685801847385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13487192312106247735796513 10115394234079685801847385)
                ·
                  refine ⟨7586545675559764351385539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10115394234079685801847385 7586545675559764351385539)
                  ·
                    refine ⟨11379818513339646527078309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7586545675559764351385539 11379818513339646527078309)
                    ·
                      refine ⟨2133715971251183723827183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11379818513339646527078309 2133715971251183723827183)
                      ·
                        rfl

theorem cell23_4155397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_4155397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155397 prefixEnd_4155397 := by exact prefixLift 4155397
  have htrace : WordTrace (prefixWord ++ tailWord_4155397) baseStart_4155397 baseEnd_4155397 := by
    simpa [prefixWord, tailWord_4155397, baseEnd_4155397] using wordTrace_append hprefix tailTrace_4155397
  have hstable : (prefixWord ++ tailWord_4155397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155397).length < 2 ^ (prefixWord ++ tailWord_4155397).sum := by decide
  have hdescent : baseEnd_4155397 < baseStart_4155397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155431 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_4155431 : Nat := 118140960795 + 4155431 * 2 ^ 59
def prefixEnd_4155431 : Nat := 4983230072969 + 3 ^ 40 * 4155431 * 2
def baseEnd_4155431 : Nat := 2133733429593436590802027

theorem tailTrace_4155431 : CollatzResearch.WordTrace tailWord_4155431 prefixEnd_4155431 2133733429593436590802027 := by
  unfold tailWord_4155431
  simp only [CollatzResearch.WordTrace]
  refine ⟨151561019808590652958514147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101040679872393768639009431 151561019808590652958514147)
  ·
    refine ⟨227341529712885979437771221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151561019808590652958514147 227341529712885979437771221)
    ·
      refine ⟨5328317102645765143072763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 227341529712885979437771221 5328317102645765143072763)
      ·
        refine ⟨7992475653968647714609145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328317102645765143072763 7992475653968647714609145)
        ·
          refine ⟨5994356740476485785956859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7992475653968647714609145 5994356740476485785956859)
          ·
            refine ⟨8991535110714728678935289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994356740476485785956859 8991535110714728678935289)
            ·
              refine ⟨6743651333036046509201467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8991535110714728678935289 6743651333036046509201467)
              ·
                refine ⟨10115476999554069763802201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6743651333036046509201467 10115476999554069763802201)
                ·
                  refine ⟨7586607749665552322851651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10115476999554069763802201 7586607749665552322851651)
                  ·
                    refine ⟨11379911624498328484277477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7586607749665552322851651 11379911624498328484277477)
                    ·
                      refine ⟨2133733429593436590802027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11379911624498328484277477 2133733429593436590802027)
                      ·
                        rfl

theorem cell23_4155431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_4155431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155431 prefixEnd_4155431 := by exact prefixLift 4155431
  have htrace : WordTrace (prefixWord ++ tailWord_4155431) baseStart_4155431 baseEnd_4155431 := by
    simpa [prefixWord, tailWord_4155431, baseEnd_4155431] using wordTrace_append hprefix tailTrace_4155431
  have hstable : (prefixWord ++ tailWord_4155431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155431).length < 2 ^ (prefixWord ++ tailWord_4155431).sum := by decide
  have hdescent : baseEnd_4155431 < baseStart_4155431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155434 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_4155434 : Nat := 118140960795 + 4155434 * 2 ^ 59
def prefixEnd_4155434 : Nat := 4983230072969 + 3 ^ 40 * 4155434 * 2
def baseEnd_4155434 : Nat := 2133734970035400079064513

theorem tailTrace_4155434 : CollatzResearch.WordTrace tailWord_4155434 prefixEnd_4155434 2133734970035400079064513 := by
  unfold tailWord_4155434
  simp only [CollatzResearch.WordTrace]
  refine ⟨37890282306894946117718339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101040752818386522980582237 37890282306894946117718339)
  ·
    refine ⟨56835423460342419176577509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37890282306894946117718339 56835423460342419176577509)
    ·
      refine ⟨10656641898814203595608283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56835423460342419176577509 10656641898814203595608283)
      ·
        refine ⟨15984962848221305393412425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10656641898814203595608283 15984962848221305393412425)
        ·
          refine ⟨11988722136165979045059319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15984962848221305393412425 11988722136165979045059319)
          ·
            refine ⟨17983083204248968567588979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11988722136165979045059319 17983083204248968567588979)
            ·
              refine ⟨26974624806373452851383469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17983083204248968567588979 26974624806373452851383469)
              ·
                refine ⟨10115484302390044819268801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26974624806373452851383469 10115484302390044819268801)
                ·
                  refine ⟨7586613226792533614451601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10115484302390044819268801 7586613226792533614451601)
                  ·
                    refine ⟨5689959920094400210838701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7586613226792533614451601 5689959920094400210838701)
                    ·
                      refine ⟨2133734970035400079064513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5689959920094400210838701 2133734970035400079064513)
                      ·
                        rfl

theorem cell23_4155434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_4155434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155434 prefixEnd_4155434 := by exact prefixLift 4155434
  have htrace : WordTrace (prefixWord ++ tailWord_4155434) baseStart_4155434 baseEnd_4155434 := by
    simpa [prefixWord, tailWord_4155434, baseEnd_4155434] using wordTrace_append hprefix tailTrace_4155434
  have hstable : (prefixWord ++ tailWord_4155434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155434).length < 2 ^ (prefixWord ++ tailWord_4155434).sum := by decide
  have hdescent : baseEnd_4155434 < baseStart_4155434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155487 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 1, 8, 2]
def baseStart_4155487 : Nat := 118140960795 + 4155487 * 2 ^ 59
def prefixEnd_4155487 : Nat := 4983230072969 + 3 ^ 40 * 4155487 * 2
def baseEnd_4155487 : Nat := 2133762184510088371701769

theorem tailTrace_4155487 : CollatzResearch.WordTrace tailWord_4155487 prefixEnd_4155487 2133762184510088371701769 := by
  unfold tailWord_4155487
  simp only [CollatzResearch.WordTrace]
  refine ⟨151563062296387774522552715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101042041530925183015035143 151563062296387774522552715)
  ·
    refine ⟨227344593444581661783829073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151563062296387774522552715 227344593444581661783829073)
    ·
      refine ⟨170508445083436246337871805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227344593444581661783829073 170508445083436246337871805)
      ·
        refine ⟨63940666906288592376701927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170508445083436246337871805 63940666906288592376701927)
        ·
          refine ⟨95911000359432888565052891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63940666906288592376701927 95911000359432888565052891)
          ·
            refine ⟨143866500539149332847579337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95911000359432888565052891 143866500539149332847579337)
            ·
              refine ⟨107899875404361999635684503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143866500539149332847579337 107899875404361999635684503)
              ·
                refine ⟨161849813106542999453526755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107899875404361999635684503 161849813106542999453526755)
                ·
                  refine ⟨242774719659814499180290133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161849813106542999453526755 242774719659814499180290133)
                  ·
                    refine ⟨2845016246013451162269025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 242774719659814499180290133 2845016246013451162269025)
                    ·
                      refine ⟨2133762184510088371701769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845016246013451162269025 2133762184510088371701769)
                      ·
                        rfl

theorem cell23_4155487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_4155487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155487 prefixEnd_4155487 := by exact prefixLift 4155487
  have htrace : WordTrace (prefixWord ++ tailWord_4155487) baseStart_4155487 baseEnd_4155487 := by
    simpa [prefixWord, tailWord_4155487, baseEnd_4155487] using wordTrace_append hprefix tailTrace_4155487
  have hstable : (prefixWord ++ tailWord_4155487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155487).length < 2 ^ (prefixWord ++ tailWord_4155487).sum := by decide
  have hdescent : baseEnd_4155487 < baseStart_4155487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155497 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 4, 4]
def baseStart_4155497 : Nat := 118140960795 + 4155497 * 2 ^ 59
def prefixEnd_4155497 : Nat := 4983230072969 + 3 ^ 40 * 4155497 * 2
def baseEnd_4155497 : Nat := 711255773105544444192241

theorem tailTrace_4155497 : CollatzResearch.WordTrace tailWord_4155497 prefixEnd_4155497 711255773105544444192241 := by
  unfold tailWord_4155497
  simp only [CollatzResearch.WordTrace]
  refine ⟨151563427026351546230416745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101042284684234364153611163 151563427026351546230416745)
  ·
    refine ⟨113672570269763659672812559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151563427026351546230416745 113672570269763659672812559)
    ·
      refine ⟨170508855404645489509218839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113672570269763659672812559 170508855404645489509218839)
      ·
        refine ⟨255763283106968234263828259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170508855404645489509218839 255763283106968234263828259)
        ·
          refine ⟨383644924660452351395742389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255763283106968234263828259 383644924660452351395742389)
          ·
            refine ⟨35966711686917407943350849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383644924660452351395742389 35966711686917407943350849)
            ·
              refine ⟨26975033765188055957513137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35966711686917407943350849 26975033765188055957513137)
              ·
                refine ⟨20231275323891041968134853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26975033765188055957513137 20231275323891041968134853)
                ·
                  refine ⟨3793364123229570369025285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20231275323891041968134853 3793364123229570369025285)
                  ·
                    refine ⟨711255773105544444192241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3793364123229570369025285 711255773105544444192241)
                    ·
                      rfl

theorem cell23_4155497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 4].length) (baseStart_4155497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155497 prefixEnd_4155497 := by exact prefixLift 4155497
  have htrace : WordTrace (prefixWord ++ tailWord_4155497) baseStart_4155497 baseEnd_4155497 := by
    simpa [prefixWord, tailWord_4155497, baseEnd_4155497] using wordTrace_append hprefix tailTrace_4155497
  have hstable : (prefixWord ++ tailWord_4155497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155497).length < 2 ^ (prefixWord ++ tailWord_4155497).sum := by decide
  have hdescent : baseEnd_4155497 < baseStart_4155497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155504 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 4]
def baseStart_4155504 : Nat := 118140960795 + 4155504 * 2 ^ 59
def prefixEnd_4155504 : Nat := 4983230072969 + 3 ^ 40 * 4155504 * 2
def baseEnd_4155504 : Nat := 2133770913681214805189191

theorem tailTrace_4155504 : CollatzResearch.WordTrace tailWord_4155504 prefixEnd_4155504 2133770913681214805189191 := by
  unfold tailWord_4155504
  simp only [CollatzResearch.WordTrace]
  refine ⟨75781841168663093212960783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101042454891550790950614377 75781841168663093212960783)
  ·
    refine ⟨113672761752994639819441175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75781841168663093212960783 113672761752994639819441175)
    ·
      refine ⟨170509142629491959729161763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113672761752994639819441175 170509142629491959729161763)
      ·
        refine ⟨255763713944237939593742645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170509142629491959729161763 255763713944237939593742645)
        ·
          refine ⟨23977848182272306836913373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255763713944237939593742645 23977848182272306836913373)
          ·
            refine ⟨8991693068352115063842515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23977848182272306836913373 8991693068352115063842515)
            ·
              refine ⟨13487539602528172595763773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991693068352115063842515 13487539602528172595763773)
              ·
                refine ⟨5057827350948064723411415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13487539602528172595763773 5057827350948064723411415)
                ·
                  refine ⟨7586741026422097085117123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057827350948064723411415 7586741026422097085117123)
                  ·
                    refine ⟨11380111539633145627675685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7586741026422097085117123 11380111539633145627675685)
                    ·
                      refine ⟨2133770913681214805189191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11380111539633145627675685 2133770913681214805189191)
                      ·
                        rfl

theorem cell23_4155504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 4].length) (baseStart_4155504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155504 prefixEnd_4155504 := by exact prefixLift 4155504
  have htrace : WordTrace (prefixWord ++ tailWord_4155504) baseStart_4155504 baseEnd_4155504 := by
    simpa [prefixWord, tailWord_4155504, baseEnd_4155504] using wordTrace_append hprefix tailTrace_4155504
  have hstable : (prefixWord ++ tailWord_4155504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155504).length < 2 ^ (prefixWord ++ tailWord_4155504).sum := by decide
  have hdescent : baseEnd_4155504 < baseStart_4155504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155520 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_4155520 : Nat := 118140960795 + 4155520 * 2 ^ 59
def prefixEnd_4155520 : Nat := 4983230072969 + 3 ^ 40 * 4155520 * 2
def baseEnd_4155520 : Nat := 2133779129371686742589117

theorem tailTrace_4155520 : CollatzResearch.WordTrace tailWord_4155520 prefixEnd_4155520 2133779129371686742589117 := by
  unfold tailWord_4155520
  simp only [CollatzResearch.WordTrace]
  refine ⟨75782132952634110579252007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101042843936845480772336009 75782132952634110579252007)
  ·
    refine ⟨113673199428951165868878011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75782132952634110579252007 113673199428951165868878011)
    ·
      refine ⟨170509799143426748803317017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113673199428951165868878011 170509799143426748803317017)
      ·
        refine ⟨127882349357570061602487763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170509799143426748803317017 127882349357570061602487763)
        ·
          refine ⟨191823524036355092403731645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127882349357570061602487763 191823524036355092403731645)
          ·
            refine ⟨71933821513633159651399367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191823524036355092403731645 71933821513633159651399367)
            ·
              refine ⟨107900732270449739477099051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71933821513633159651399367 107900732270449739477099051)
              ·
                refine ⟨161851098405674609215648577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107900732270449739477099051 161851098405674609215648577)
                ·
                  refine ⟨121388323804255956911736433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161851098405674609215648577 121388323804255956911736433)
                  ·
                    refine ⟨91041242853191967683802325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121388323804255956911736433 91041242853191967683802325)
                    ·
                      refine ⟨2133779129371686742589117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91041242853191967683802325 2133779129371686742589117)
                      ·
                        rfl

theorem cell23_4155520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_4155520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155520 prefixEnd_4155520 := by exact prefixLift 4155520
  have htrace : WordTrace (prefixWord ++ tailWord_4155520) baseStart_4155520 baseEnd_4155520 := by
    simpa [prefixWord, tailWord_4155520, baseEnd_4155520] using wordTrace_append hprefix tailTrace_4155520
  have hstable : (prefixWord ++ tailWord_4155520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155520).length < 2 ^ (prefixWord ++ tailWord_4155520).sum := by decide
  have hdescent : baseEnd_4155520 < baseStart_4155520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155534 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_4155534 : Nat := 118140960795 + 4155534 * 2 ^ 59
def prefixEnd_4155534 : Nat := 4983230072969 + 3 ^ 40 * 4155534 * 2
def baseEnd_4155534 : Nat := 2133786318100849687814053

theorem tailTrace_4155534 : CollatzResearch.WordTrace tailWord_4155534 prefixEnd_4155534 2133786318100849687814053 := by
  unfold tailWord_4155534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18945597065902187693689207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101043184351478334366342437 18945597065902187693689207)
  ·
    refine ⟨28418395598853281540533811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18945597065902187693689207 28418395598853281540533811)
    ·
      refine ⟨42627593398279922310800717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28418395598853281540533811 42627593398279922310800717)
      ·
        refine ⟨15985347524354970866550269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42627593398279922310800717 15985347524354970866550269)
        ·
          refine ⟨5994505321633114074956351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15985347524354970866550269 5994505321633114074956351)
          ·
            refine ⟨8991757982449671112434527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994505321633114074956351 8991757982449671112434527)
            ·
              refine ⟨13487636973674506668651791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991757982449671112434527 13487636973674506668651791)
              ·
                refine ⟨20231455460511760002977687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13487636973674506668651791 20231455460511760002977687)
                ·
                  refine ⟨30347183190767640004466531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20231455460511760002977687 30347183190767640004466531)
                  ·
                    refine ⟨45520774786151460006699797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30347183190767640004466531 45520774786151460006699797)
                    ·
                      refine ⟨2133786318100849687814053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45520774786151460006699797 2133786318100849687814053)
                      ·
                        rfl

theorem cell23_4155534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_4155534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155534 prefixEnd_4155534 := by exact prefixLift 4155534
  have htrace : WordTrace (prefixWord ++ tailWord_4155534) baseStart_4155534 baseEnd_4155534 := by
    simpa [prefixWord, tailWord_4155534, baseEnd_4155534] using wordTrace_append hprefix tailTrace_4155534
  have hstable : (prefixWord ++ tailWord_4155534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155534).length < 2 ^ (prefixWord ++ tailWord_4155534).sum := by decide
  have hdescent : baseEnd_4155534 < baseStart_4155534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155577 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_4155577 : Nat := 118140960795 + 4155577 * 2 ^ 59
def prefixEnd_4155577 : Nat := 4983230072969 + 3 ^ 40 * 4155577 * 2
def baseEnd_4155577 : Nat := 2133808397768993019576355

theorem tailTrace_4155577 : CollatzResearch.WordTrace tailWord_4155577 prefixEnd_4155577 2133808397768993019576355 := by
  unfold tailWord_4155577
  simp only [CollatzResearch.WordTrace]
  refine ⟨151566344866061719893328985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101044229910707813262219323 151566344866061719893328985)
  ·
    refine ⟨113674758649546289919996739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151566344866061719893328985 113674758649546289919996739)
    ·
      refine ⟨170512137974319434879995109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113674758649546289919996739 170512137974319434879995109)
      ·
        refine ⟨31971025870184894039999083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170512137974319434879995109 31971025870184894039999083)
        ·
          refine ⟨47956538805277341059998625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31971025870184894039999083 47956538805277341059998625)
          ·
            refine ⟨35967404103958005794998969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47956538805277341059998625 35967404103958005794998969)
            ·
              refine ⟨26975553077968504346249227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35967404103958005794998969 26975553077968504346249227)
              ·
                refine ⟨40463329616952756519373841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26975553077968504346249227 40463329616952756519373841)
                ·
                  refine ⟨30347497212714567389530381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40463329616952756519373841 30347497212714567389530381)
                  ·
                    refine ⟨11380311454767962771073893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30347497212714567389530381 11380311454767962771073893)
                    ·
                      refine ⟨2133808397768993019576355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11380311454767962771073893 2133808397768993019576355)
                      ·
                        rfl

theorem cell23_4155577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_4155577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155577 prefixEnd_4155577 := by exact prefixLift 4155577
  have htrace : WordTrace (prefixWord ++ tailWord_4155577) baseStart_4155577 baseEnd_4155577 := by
    simpa [prefixWord, tailWord_4155577, baseEnd_4155577] using wordTrace_append hprefix tailTrace_4155577
  have hstable : (prefixWord ++ tailWord_4155577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155577).length < 2 ^ (prefixWord ++ tailWord_4155577).sum := by decide
  have hdescent : baseEnd_4155577 < baseStart_4155577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155588 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_4155588 : Nat := 118140960795 + 4155588 * 2 ^ 59
def prefixEnd_4155588 : Nat := 4983230072969 + 3 ^ 40 * 4155588 * 2
def baseEnd_4155588 : Nat := 2133814046056192476538805

theorem tailTrace_4155588 : CollatzResearch.WordTrace tailWord_4155588 prefixEnd_4155588 2133814046056192476538805 := by
  unfold tailWord_4155588
  simp only [CollatzResearch.WordTrace]
  refine ⟨75783373034510934385989709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101044497379347912514652945 75783373034510934385989709)
  ·
    refine ⟨28418764887941600394746141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75783373034510934385989709 28418764887941600394746141)
    ·
      refine ⟨10657036832978100148029803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28418764887941600394746141 10657036832978100148029803)
      ·
        refine ⟨15985555249467150222044705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10657036832978100148029803 15985555249467150222044705)
        ·
          refine ⟨11989166437100362666533529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15985555249467150222044705 11989166437100362666533529)
          ·
            refine ⟨8991874827825271999900147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11989166437100362666533529 8991874827825271999900147)
            ·
              refine ⟨13487812241737907999850221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991874827825271999900147 13487812241737907999850221)
              ·
                refine ⟨5057929590651715499943833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13487812241737907999850221 5057929590651715499943833)
                ·
                  refine ⟨3793447192988786624957875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5057929590651715499943833 3793447192988786624957875)
                  ·
                    refine ⟨5690170789483179937436813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3793447192988786624957875 5690170789483179937436813)
                    ·
                      refine ⟨2133814046056192476538805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5690170789483179937436813 2133814046056192476538805)
                      ·
                        rfl

theorem cell23_4155588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_4155588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155588 prefixEnd_4155588 := by exact prefixLift 4155588
  have htrace : WordTrace (prefixWord ++ tailWord_4155588) baseStart_4155588 baseEnd_4155588 := by
    simpa [prefixWord, tailWord_4155588, baseEnd_4155588] using wordTrace_append hprefix tailTrace_4155588
  have hstable : (prefixWord ++ tailWord_4155588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155588).length < 2 ^ (prefixWord ++ tailWord_4155588).sum := by decide
  have hdescent : baseEnd_4155588 < baseStart_4155588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155598 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2]
def baseStart_4155598 : Nat := 118140960795 + 4155598 * 2 ^ 59
def prefixEnd_4155598 : Nat := 4983230072969 + 3 ^ 40 * 4155598 * 2
def baseEnd_4155598 : Nat := 2133819180862737437413759

theorem tailTrace_4155598 : CollatzResearch.WordTrace tailWord_4155598 prefixEnd_4155598 2133819180862737437413759 := by
  unfold tailWord_4155598
  simp only [CollatzResearch.WordTrace]
  refine ⟨18945888849873205059980431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101044740532657093653228965 18945888849873205059980431)
  ·
    refine ⟨28418833274809807589970647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18945888849873205059980431 28418833274809807589970647)
    ·
      refine ⟨42628249912214711384955971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28418833274809807589970647 42628249912214711384955971)
      ·
        refine ⟨63942374868322067077433957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42628249912214711384955971 63942374868322067077433957)
        ·
          refine ⟨11989195287810387577018867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63942374868322067077433957 11989195287810387577018867)
          ·
            refine ⟨17983792931715581365528301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11989195287810387577018867 17983792931715581365528301)
            ·
              refine ⟨6743922349393343012073113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17983792931715581365528301 6743922349393343012073113)
              ·
                refine ⟨5057941762045007259054835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6743922349393343012073113 5057941762045007259054835)
                ·
                  refine ⟨7586912643067510888582253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057941762045007259054835 7586912643067510888582253)
                  ·
                    refine ⟨2845092241150316583218345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7586912643067510888582253 2845092241150316583218345)
                    ·
                      refine ⟨2133819180862737437413759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845092241150316583218345 2133819180862737437413759)
                      ·
                        rfl

theorem cell23_4155598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_4155598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155598 prefixEnd_4155598 := by exact prefixLift 4155598
  have htrace : WordTrace (prefixWord ++ tailWord_4155598) baseStart_4155598 baseEnd_4155598 := by
    simpa [prefixWord, tailWord_4155598, baseEnd_4155598] using wordTrace_append hprefix tailTrace_4155598
  have hstable : (prefixWord ++ tailWord_4155598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155598).length < 2 ^ (prefixWord ++ tailWord_4155598).sum := by decide
  have hdescent : baseEnd_4155598 < baseStart_4155598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155607 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_4155607 : Nat := 118140960795 + 4155607 * 2 ^ 59
def prefixEnd_4155607 : Nat := 4983230072969 + 3 ^ 40 * 4155607 * 2
def baseEnd_4155607 : Nat := 2133823802188627902201217

theorem tailTrace_4155607 : CollatzResearch.WordTrace tailWord_4155607 prefixEnd_4155607 2133823802188627902201217 := by
  unfold tailWord_4155607
  simp only [CollatzResearch.WordTrace]
  refine ⟨151567439055953035016921075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101044959370635356677947383 151567439055953035016921075)
  ·
    refine ⟨227351158583929552525381613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151567439055953035016921075 227351158583929552525381613)
    ·
      refine ⟨85256684468973582197018105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227351158583929552525381613 85256684468973582197018105)
      ·
        refine ⟨63942513351730186647763579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85256684468973582197018105 63942513351730186647763579)
        ·
          refine ⟨95913770027595279971645369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63942513351730186647763579 95913770027595279971645369)
          ·
            refine ⟨71935327520696459978734027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95913770027595279971645369 71935327520696459978734027)
            ·
              refine ⟨107902991281044689968101041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71935327520696459978734027 107902991281044689968101041)
              ·
                refine ⟨80927243460783517476075781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107902991281044689968101041 80927243460783517476075781)
                ·
                  refine ⟨15173858148896909526764209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80927243460783517476075781 15173858148896909526764209)
                  ·
                    refine ⟨11380393611672682145073157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15173858148896909526764209 11380393611672682145073157)
                    ·
                      refine ⟨2133823802188627902201217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11380393611672682145073157 2133823802188627902201217)
                      ·
                        rfl

theorem cell23_4155607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_4155607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155607 prefixEnd_4155607 := by exact prefixLift 4155607
  have htrace : WordTrace (prefixWord ++ tailWord_4155607) baseStart_4155607 baseEnd_4155607 := by
    simpa [prefixWord, tailWord_4155607, baseEnd_4155607] using wordTrace_append hprefix tailTrace_4155607
  have hstable : (prefixWord ++ tailWord_4155607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155607).length < 2 ^ (prefixWord ++ tailWord_4155607).sum := by decide
  have hdescent : baseEnd_4155607 < baseStart_4155607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155628 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 2, 2, 2]
def baseStart_4155628 : Nat := 118140960795 + 4155628 * 2 ^ 59
def prefixEnd_4155628 : Nat := 4983230072969 + 3 ^ 40 * 4155628 * 2
def baseEnd_4155628 : Nat := 2133834585282372320038621

theorem tailTrace_4155628 : CollatzResearch.WordTrace tailWord_4155628 prefixEnd_4155628 2133834585282372320038621 := by
  unfold tailWord_4155628
  simp only [CollatzResearch.WordTrace]
  refine ⟨75784102494438477801717769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101045469992584637068957025 75784102494438477801717769)
  ·
    refine ⟨56838076870828858351288327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75784102494438477801717769 56838076870828858351288327)
    ·
      refine ⟨85257115306243287526932491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56838076870828858351288327 85257115306243287526932491)
      ·
        refine ⟨127885672959364931290398737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85257115306243287526932491 127885672959364931290398737)
        ·
          refine ⟨95914254719523698467799053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127885672959364931290398737 95914254719523698467799053)
          ·
            refine ⟨35967845519821386925424645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95914254719523698467799053 35967845519821386925424645)
            ·
              refine ⟨6743971034966510048517121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35967845519821386925424645 6743971034966510048517121)
              ·
                refine ⟨5057978276224882536387841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6743971034966510048517121 5057978276224882536387841)
                ·
                  refine ⟨3793483707168661902290881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5057978276224882536387841 3793483707168661902290881)
                  ·
                    refine ⟨2845112780376496426718161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3793483707168661902290881 2845112780376496426718161)
                    ·
                      refine ⟨2133834585282372320038621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845112780376496426718161 2133834585282372320038621)
                      ·
                        rfl

theorem cell23_4155628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_4155628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155628 prefixEnd_4155628 := by exact prefixLift 4155628
  have htrace : WordTrace (prefixWord ++ tailWord_4155628) baseStart_4155628 baseEnd_4155628 := by
    simpa [prefixWord, tailWord_4155628, baseEnd_4155628] using wordTrace_append hprefix tailTrace_4155628
  have hstable : (prefixWord ++ tailWord_4155628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155628).length < 2 ^ (prefixWord ++ tailWord_4155628).sum := by decide
  have hdescent : baseEnd_4155628 < baseStart_4155628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155644 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_4155644 : Nat := 118140960795 + 4155644 * 2 ^ 59
def prefixEnd_4155644 : Nat := 4983230072969 + 3 ^ 40 * 4155644 * 2
def baseEnd_4155644 : Nat := 2133842800972844257438547

theorem tailTrace_4155644 : CollatzResearch.WordTrace tailWord_4155644 prefixEnd_4155644 2133842800972844257438547 := by
  unfold tailWord_4155644
  simp only [CollatzResearch.WordTrace]
  refine ⟨75784394278409495168008993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101045859037879326890678657 75784394278409495168008993)
  ·
    refine ⟨56838295708807121376006745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75784394278409495168008993 56838295708807121376006745)
    ·
      refine ⟨42628721781605341032005059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56838295708807121376006745 42628721781605341032005059)
      ·
        refine ⟨63943082672408011548007589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42628721781605341032005059 63943082672408011548007589)
        ·
          refine ⟨11989328001076502165251423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63943082672408011548007589 11989328001076502165251423)
          ·
            refine ⟨17983992001614753247877135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11989328001076502165251423 17983992001614753247877135)
            ·
              refine ⟨26975988002422129871815703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17983992001614753247877135 26975988002422129871815703)
              ·
                refine ⟨40463982003633194807723555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26975988002422129871815703 40463982003633194807723555)
                ·
                  refine ⟨60695973005449792211585333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40463982003633194807723555 60695973005449792211585333)
                  ·
                    refine ⟨5690247469260918019836125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60695973005449792211585333 5690247469260918019836125)
                    ·
                      refine ⟨2133842800972844257438547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5690247469260918019836125 2133842800972844257438547)
                      ·
                        rfl

theorem cell23_4155644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_4155644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155644 prefixEnd_4155644 := by exact prefixLift 4155644
  have htrace : WordTrace (prefixWord ++ tailWord_4155644) baseStart_4155644 baseEnd_4155644 := by
    simpa [prefixWord, tailWord_4155644, baseEnd_4155644] using wordTrace_append hprefix tailTrace_4155644
  have hstable : (prefixWord ++ tailWord_4155644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155644).length < 2 ^ (prefixWord ++ tailWord_4155644).sum := by decide
  have hdescent : baseEnd_4155644 < baseStart_4155644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155647 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 1, 7]
def baseStart_4155647 : Nat := 118140960795 + 4155647 * 2 ^ 59
def prefixEnd_4155647 : Nat := 4983230072969 + 3 ^ 40 * 4155647 * 2
def baseEnd_4155647 : Nat := 711281447138269248567011

theorem tailTrace_4155647 : CollatzResearch.WordTrace tailWord_4155647 prefixEnd_4155647 711281447138269248567011 := by
  unfold tailWord_4155647
  simp only [CollatzResearch.WordTrace]
  refine ⟨151568897975808121848377195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101045931983872081232251463 151568897975808121848377195)
  ·
    refine ⟨227353346963712182772565793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151568897975808121848377195 227353346963712182772565793)
    ·
      refine ⟨170515010222784137079424345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227353346963712182772565793 170515010222784137079424345)
      ·
        refine ⟨127886257667088102809568259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170515010222784137079424345 127886257667088102809568259)
        ·
          refine ⟨191829386500632154214352389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127886257667088102809568259 191829386500632154214352389)
          ·
            refine ⟨35968009968868528915191073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191829386500632154214352389 35968009968868528915191073)
            ·
              refine ⟨26976007476651396686393305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35968009968868528915191073 26976007476651396686393305)
              ·
                refine ⟨20232005607488547514794979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26976007476651396686393305 20232005607488547514794979)
                ·
                  refine ⟨30348008411232821272192469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20232005607488547514794979 30348008411232821272192469)
                  ·
                    refine ⟨711281447138269248567011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30348008411232821272192469 711281447138269248567011)
                    ·
                      rfl

theorem cell23_4155647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_4155647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155647 prefixEnd_4155647 := by exact prefixLift 4155647
  have htrace : WordTrace (prefixWord ++ tailWord_4155647) baseStart_4155647 baseEnd_4155647 := by
    simpa [prefixWord, tailWord_4155647, baseEnd_4155647] using wordTrace_append hprefix tailTrace_4155647
  have hstable : (prefixWord ++ tailWord_4155647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155647).length < 2 ^ (prefixWord ++ tailWord_4155647).sum := by decide
  have hdescent : baseEnd_4155647 < baseStart_4155647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155678 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4155678 : Nat := 118140960795 + 4155678 * 2 ^ 59
def prefixEnd_4155678 : Nat := 4983230072969 + 3 ^ 40 * 4155678 * 2
def baseEnd_4155678 : Nat := 2133860259315097124413391

theorem tailTrace_4155678 : CollatzResearch.WordTrace tailWord_4155678 prefixEnd_4155678 2133860259315097124413391 := by
  unfold tailWord_4155678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18946253579836976767844461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101046685759130542761837125 18946253579836976767844461)
  ·
    refine ⟨7104845092438866287941673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18946253579836976767844461 7104845092438866287941673)
    ·
      refine ⟨5328633819329149715956255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7104845092438866287941673 5328633819329149715956255)
      ·
        refine ⟨7992950728993724573934383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328633819329149715956255 7992950728993724573934383)
        ·
          refine ⟨11989426093490586860901575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7992950728993724573934383 11989426093490586860901575)
          ·
            refine ⟨17984139140235880291352363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11989426093490586860901575 17984139140235880291352363)
            ·
              refine ⟨26976208710353820437028545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17984139140235880291352363 26976208710353820437028545)
              ·
                refine ⟨20232156532765365327771409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26976208710353820437028545 20232156532765365327771409)
                ·
                  refine ⟨15174117399574023995828557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20232156532765365327771409 15174117399574023995828557)
                  ·
                    refine ⟨5690294024840258998435709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15174117399574023995828557 5690294024840258998435709)
                    ·
                      refine ⟨2133860259315097124413391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5690294024840258998435709 2133860259315097124413391)
                      ·
                        rfl

theorem cell23_4155678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4155678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155678 prefixEnd_4155678 := by exact prefixLift 4155678
  have htrace : WordTrace (prefixWord ++ tailWord_4155678) baseStart_4155678 baseEnd_4155678 := by
    simpa [prefixWord, tailWord_4155678, baseEnd_4155678] using wordTrace_append hprefix tailTrace_4155678
  have hstable : (prefixWord ++ tailWord_4155678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155678).length < 2 ^ (prefixWord ++ tailWord_4155678).sum := by decide
  have hdescent : baseEnd_4155678 < baseStart_4155678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155701 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_4155701 : Nat := 118140960795 + 4155701 * 2 ^ 59
def prefixEnd_4155701 : Nat := 4983230072969 + 3 ^ 40 * 4155701 * 2
def baseEnd_4155701 : Nat := 2133872069370150534425785

theorem tailTrace_4155701 : CollatzResearch.WordTrace tailWord_4155701 prefixEnd_4155701 2133872069370150534425785 := by
  unfold tailWord_4155701
  simp only [CollatzResearch.WordTrace]
  refine ⟨151570867517612489070842957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101047245011741659380561971 151570867517612489070842957)
  ·
    refine ⟨56839075319104683401566109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151570867517612489070842957 56839075319104683401566109)
    ·
      refine ⟨21314653244664256275587291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56839075319104683401566109 21314653244664256275587291)
      ·
        refine ⟨31971979866996384413380937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21314653244664256275587291 31971979866996384413380937)
        ·
          refine ⟨23978984900247288310035703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31971979866996384413380937 23978984900247288310035703)
          ·
            refine ⟨35968477350370932465053555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23978984900247288310035703 35968477350370932465053555)
            ·
              refine ⟨53952716025556398697580333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35968477350370932465053555 53952716025556398697580333)
              ·
                refine ⟨20232268509583649511592625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53952716025556398697580333 20232268509583649511592625)
                ·
                  refine ⟨15174201382187737133694469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20232268509583649511592625 15174201382187737133694469)
                  ·
                    refine ⟨2845162759160200712567713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15174201382187737133694469 2845162759160200712567713)
                    ·
                      refine ⟨2133872069370150534425785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845162759160200712567713 2133872069370150534425785)
                      ·
                        rfl

theorem cell23_4155701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_4155701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155701 prefixEnd_4155701 := by exact prefixLift 4155701
  have htrace : WordTrace (prefixWord ++ tailWord_4155701) baseStart_4155701 baseEnd_4155701 := by
    simpa [prefixWord, tailWord_4155701, baseEnd_4155701] using wordTrace_append hprefix tailTrace_4155701
  have hstable : (prefixWord ++ tailWord_4155701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155701).length < 2 ^ (prefixWord ++ tailWord_4155701).sum := by decide
  have hdescent : baseEnd_4155701 < baseStart_4155701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155704 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 1, 4, 3]
def baseStart_4155704 : Nat := 118140960795 + 4155704 * 2 ^ 59
def prefixEnd_4155704 : Nat := 4983230072969 + 3 ^ 40 * 4155704 * 2
def baseEnd_4155704 : Nat := 2133873609812114022688271

theorem tailTrace_4155704 : CollatzResearch.WordTrace tailWord_4155704 prefixEnd_4155704 2133873609812114022688271 := by
  unfold tailWord_4155704
  simp only [CollatzResearch.WordTrace]
  refine ⟨75785488468300810291601083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101047317957734413722134777 75785488468300810291601083)
  ·
    refine ⟨113678232702451215437401625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75785488468300810291601083 113678232702451215437401625)
    ·
      refine ⟨85258674526838411578051219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113678232702451215437401625 85258674526838411578051219)
      ·
        refine ⟨127888011790257617367076829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85258674526838411578051219 127888011790257617367076829)
        ·
          refine ⟨47958004421346606512653811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127888011790257617367076829 47958004421346606512653811)
          ·
            refine ⟨71937006632019909768980717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47958004421346606512653811 71937006632019909768980717)
            ·
              refine ⟨26976377487007466163367769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71937006632019909768980717 26976377487007466163367769)
              ·
                refine ⟨20232283115255599622525827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26976377487007466163367769 20232283115255599622525827)
                ·
                  refine ⟨30348424672883399433788741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20232283115255599622525827 30348424672883399433788741)
                  ·
                    refine ⟨5690329626165637393835389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30348424672883399433788741 5690329626165637393835389)
                    ·
                      refine ⟨2133873609812114022688271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5690329626165637393835389 2133873609812114022688271)
                      ·
                        rfl

theorem cell23_4155704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_4155704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155704 prefixEnd_4155704 := by exact prefixLift 4155704
  have htrace : WordTrace (prefixWord ++ tailWord_4155704) baseStart_4155704 baseEnd_4155704 := by
    simpa [prefixWord, tailWord_4155704, baseEnd_4155704] using wordTrace_append hprefix tailTrace_4155704
  have hstable : (prefixWord ++ tailWord_4155704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155704).length < 2 ^ (prefixWord ++ tailWord_4155704).sum := by decide
  have hdescent : baseEnd_4155704 < baseStart_4155704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155717 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_4155717 : Nat := 118140960795 + 4155717 * 2 ^ 59
def prefixEnd_4155717 : Nat := 4983230072969 + 3 ^ 40 * 4155717 * 2
def baseEnd_4155717 : Nat := 2133880285060622471825711

theorem tailTrace_4155717 : CollatzResearch.WordTrace tailWord_4155717 prefixEnd_4155717 2133880285060622471825711 := by
  unfold tailWord_4155717
  simp only [CollatzResearch.WordTrace]
  refine ⟨151571451085554523803425405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101047634057036349202283603 151571451085554523803425405)
  ·
    refine ⟨56839294157082946426284527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151571451085554523803425405 56839294157082946426284527)
    ·
      refine ⟨85258941235624419639426791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56839294157082946426284527 85258941235624419639426791)
      ·
        refine ⟨127888411853436629459140187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85258941235624419639426791 127888411853436629459140187)
        ·
          refine ⟨191832617780154944188710281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127888411853436629459140187 191832617780154944188710281)
          ·
            refine ⟨143874463335116208141532711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191832617780154944188710281 143874463335116208141532711)
            ·
              refine ⟨215811695002674312212299067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143874463335116208141532711 215811695002674312212299067)
              ·
                refine ⟨323717542504011468318448601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215811695002674312212299067 323717542504011468318448601)
                ·
                  refine ⟨242788156878008601238836451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323717542504011468318448601 242788156878008601238836451)
                  ·
                    refine ⟨364182235317012901858254677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242788156878008601238836451 364182235317012901858254677)
                    ·
                      refine ⟨2133880285060622471825711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 364182235317012901858254677 2133880285060622471825711)
                      ·
                        rfl

theorem cell23_4155717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_4155717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155717 prefixEnd_4155717 := by exact prefixLift 4155717
  have htrace : WordTrace (prefixWord ++ tailWord_4155717) baseStart_4155717 baseEnd_4155717 := by
    simpa [prefixWord, tailWord_4155717, baseEnd_4155717] using wordTrace_append hprefix tailTrace_4155717
  have hstable : (prefixWord ++ tailWord_4155717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155717).length < 2 ^ (prefixWord ++ tailWord_4155717).sum := by decide
  have hdescent : baseEnd_4155717 < baseStart_4155717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155727 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_4155727 : Nat := 118140960795 + 4155727 * 2 ^ 59
def prefixEnd_4155727 : Nat := 4983230072969 + 3 ^ 40 * 4155727 * 2
def baseEnd_4155727 : Nat := 2133885419867167432700665

theorem tailTrace_4155727 : CollatzResearch.WordTrace tailWord_4155727 prefixEnd_4155727 2133885419867167432700665 := by
  unfold tailWord_4155727
  simp only [CollatzResearch.WordTrace]
  refine ⟨151571815815518295511289435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101047877210345530340859623 151571815815518295511289435)
  ·
    refine ⟨227357723723277443266934153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151571815815518295511289435 227357723723277443266934153)
    ·
      refine ⟨170518292792458082450200615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227357723723277443266934153 170518292792458082450200615)
      ·
        refine ⟨255777439188687123675300923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170518292792458082450200615 255777439188687123675300923)
        ·
          refine ⟨383666158783030685512951385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255777439188687123675300923 383666158783030685512951385)
          ·
            refine ⟨287749619087273014134713539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383666158783030685512951385 287749619087273014134713539)
            ·
              refine ⟨431624428630909521202070309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287749619087273014134713539 431624428630909521202070309)
              ·
                refine ⟨80929580368295535225388183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431624428630909521202070309 80929580368295535225388183)
                ·
                  refine ⟨121394370552443302838082275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80929580368295535225388183 121394370552443302838082275)
                  ·
                    refine ⟨182091555828664954257123413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121394370552443302838082275 182091555828664954257123413)
                    ·
                      refine ⟨2133885419867167432700665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 182091555828664954257123413 2133885419867167432700665)
                      ·
                        rfl

theorem cell23_4155727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_4155727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155727 prefixEnd_4155727 := by exact prefixLift 4155727
  have htrace : WordTrace (prefixWord ++ tailWord_4155727) baseStart_4155727 baseEnd_4155727 := by
    simpa [prefixWord, tailWord_4155727, baseEnd_4155727] using wordTrace_append hprefix tailTrace_4155727
  have hstable : (prefixWord ++ tailWord_4155727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155727).length < 2 ^ (prefixWord ++ tailWord_4155727).sum := by decide
  have hdescent : baseEnd_4155727 < baseStart_4155727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155728 : List Nat := [2, 1, 1, 1, 1, 6, 3, 3, 1, 4]
def baseStart_4155728 : Nat := 118140960795 + 4155728 * 2 ^ 59
def prefixEnd_4155728 : Nat := 4983230072969 + 3 ^ 40 * 4155728 * 2
def baseEnd_4155728 : Nat := 711295311115940642929387

theorem tailTrace_4155728 : CollatzResearch.WordTrace tailWord_4155728 prefixEnd_4155728 711295311115940642929387 := by
  unfold tailWord_4155728
  simp only [CollatzResearch.WordTrace]
  refine ⟨75785926144257336341037919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101047901525676448454717225 75785926144257336341037919)
  ·
    refine ⟨113678889216386004511556879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75785926144257336341037919 113678889216386004511556879)
    ·
      refine ⟨170518333824579006767335319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113678889216386004511556879 170518333824579006767335319)
      ·
        refine ⟨255777500736868510151002979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170518333824579006767335319 255777500736868510151002979)
        ·
          refine ⟨383666251105302765226504469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255777500736868510151002979 383666251105302765226504469)
          ·
            refine ⟨17984355520561067119992397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 383666251105302765226504469 17984355520561067119992397)
            ·
              refine ⟨6744133320210400169997149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17984355520561067119992397 6744133320210400169997149)
              ·
                refine ⟨2529049995078900063748931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6744133320210400169997149 2529049995078900063748931)
                ·
                  refine ⟨3793574992618350095623397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529049995078900063748931 3793574992618350095623397)
                  ·
                    refine ⟨711295311115940642929387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3793574992618350095623397 711295311115940642929387)
                    ·
                      rfl

theorem cell23_4155728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 1, 4].length) (baseStart_4155728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155728 prefixEnd_4155728 := by exact prefixLift 4155728
  have htrace : WordTrace (prefixWord ++ tailWord_4155728) baseStart_4155728 baseEnd_4155728 := by
    simpa [prefixWord, tailWord_4155728, baseEnd_4155728] using wordTrace_append hprefix tailTrace_4155728
  have hstable : (prefixWord ++ tailWord_4155728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155728).length < 2 ^ (prefixWord ++ tailWord_4155728).sum := by decide
  have hdescent : baseEnd_4155728 < baseStart_4155728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155742 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_4155742 : Nat := 118140960795 + 4155742 * 2 ^ 59
def prefixEnd_4155742 : Nat := 4983230072969 + 3 ^ 40 * 4155742 * 2
def baseEnd_4155742 : Nat := 2133893122076984874013097

theorem tailTrace_4155742 : CollatzResearch.WordTrace tailWord_4155742 prefixEnd_4155742 2133893122076984874013097 := by
  unfold tailWord_4155742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18946545363807994134135685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101048241940309302048723653 18946545363807994134135685)
  ·
    refine ⟨3552477255713998900150441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18946545363807994134135685 3552477255713998900150441)
    ·
      refine ⟨2664357941785499175112831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3552477255713998900150441 2664357941785499175112831)
      ·
        refine ⟨3996536912678248762669247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664357941785499175112831 3996536912678248762669247)
        ·
          refine ⟨5994805369017373144003871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996536912678248762669247 5994805369017373144003871)
          ·
            refine ⟨8992208053526059716005807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994805369017373144003871 8992208053526059716005807)
            ·
              refine ⟨13488312080289089574008711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992208053526059716005807 13488312080289089574008711)
              ·
                refine ⟨20232468120433634361013067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13488312080289089574008711 20232468120433634361013067)
                ·
                  refine ⟨30348702180650451541519601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20232468120433634361013067 30348702180650451541519601)
                  ·
                    refine ⟨22761526635487838656139701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30348702180650451541519601 22761526635487838656139701)
                    ·
                      refine ⟨2133893122076984874013097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22761526635487838656139701 2133893122076984874013097)
                      ·
                        rfl

theorem cell23_4155742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_4155742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155742 prefixEnd_4155742 := by exact prefixLift 4155742
  have htrace : WordTrace (prefixWord ++ tailWord_4155742) baseStart_4155742 baseEnd_4155742 := by
    simpa [prefixWord, tailWord_4155742, baseEnd_4155742] using wordTrace_append hprefix tailTrace_4155742
  have hstable : (prefixWord ++ tailWord_4155742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155742).length < 2 ^ (prefixWord ++ tailWord_4155742).sum := by decide
  have hdescent : baseEnd_4155742 < baseStart_4155742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155761 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 6, 3, 2]
def baseStart_4155761 : Nat := 118140960795 + 4155761 * 2 ^ 59
def prefixEnd_4155761 : Nat := 4983230072969 + 3 ^ 40 * 4155761 * 2
def baseEnd_4155761 : Nat := 2133902878209420299675509

theorem tailTrace_4155761 : CollatzResearch.WordTrace tailWord_4155761 prefixEnd_4155761 2133902878209420299675509 := by
  unfold tailWord_4155761
  simp only [CollatzResearch.WordTrace]
  refine ⟨151573055897395119318027137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101048703931596746212018091 151573055897395119318027137)
  ·
    refine ⟨113679791923046339488520353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151573055897395119318027137 113679791923046339488520353)
    ·
      refine ⟨85259843942284754616390265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113679791923046339488520353 85259843942284754616390265)
      ·
        refine ⟨63944882956713565962292699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85259843942284754616390265 63944882956713565962292699)
        ·
          refine ⟨95917324435070348943439049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63944882956713565962292699 95917324435070348943439049)
          ·
            refine ⟨71937993326302761707579287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95917324435070348943439049 71937993326302761707579287)
            ·
              refine ⟨107906989989454142561368931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71937993326302761707579287 107906989989454142561368931)
              ·
                refine ⟨161860484984181213842053397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107906989989454142561368931 161860484984181213842053397)
                ·
                  refine ⟨7587210233633494398846253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161860484984181213842053397 7587210233633494398846253)
                  ·
                    refine ⟨2845203837612560399567345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7587210233633494398846253 2845203837612560399567345)
                    ·
                      refine ⟨2133902878209420299675509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845203837612560399567345 2133902878209420299675509)
                      ·
                        rfl

theorem cell23_4155761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_4155761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155761 prefixEnd_4155761 := by exact prefixLift 4155761
  have htrace : WordTrace (prefixWord ++ tailWord_4155761) baseStart_4155761 baseEnd_4155761 := by
    simpa [prefixWord, tailWord_4155761, baseEnd_4155761] using wordTrace_append hprefix tailTrace_4155761
  have hstable : (prefixWord ++ tailWord_4155761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155761).length < 2 ^ (prefixWord ++ tailWord_4155761).sum := by decide
  have hdescent : baseEnd_4155761 < baseStart_4155761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155771 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 1, 5]
def baseStart_4155771 : Nat := 118140960795 + 4155771 * 2 ^ 59
def prefixEnd_4155771 : Nat := 4983230072969 + 3 ^ 40 * 4155771 * 2
def baseEnd_4155771 : Nat := 711302671005321753516821

theorem tailTrace_4155771 : CollatzResearch.WordTrace tailWord_4155771 prefixEnd_4155771 711302671005321753516821 := by
  unfold tailWord_4155771
  simp only [CollatzResearch.WordTrace]
  refine ⟨151573420627358891025891167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101048947084905927350594111 151573420627358891025891167)
  ·
    refine ⟨227360130941038336538836751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151573420627358891025891167 227360130941038336538836751)
    ·
      refine ⟨341040196411557504808255127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227360130941038336538836751 341040196411557504808255127)
      ·
        refine ⟨511560294617336257212382691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341040196411557504808255127 511560294617336257212382691)
        ·
          refine ⟨767340441926004385818574037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511560294617336257212382691 767340441926004385818574037)
          ·
            refine ⟨17984541607640727792622829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 767340441926004385818574037 17984541607640727792622829)
            ·
              refine ⟨6744203102865272922233561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17984541607640727792622829 6744203102865272922233561)
              ·
                refine ⟨5058152327148954691675171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6744203102865272922233561 5058152327148954691675171)
                ·
                  refine ⟨7587228490723432037512757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058152327148954691675171 7587228490723432037512757)
                  ·
                    refine ⟨711302671005321753516821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7587228490723432037512757 711302671005321753516821)
                    ·
                      rfl

theorem cell23_4155771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 5].length) (baseStart_4155771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155771 prefixEnd_4155771 := by exact prefixLift 4155771
  have htrace : WordTrace (prefixWord ++ tailWord_4155771) baseStart_4155771 baseEnd_4155771 := by
    simpa [prefixWord, tailWord_4155771, baseEnd_4155771] using wordTrace_append hprefix tailTrace_4155771
  have hstable : (prefixWord ++ tailWord_4155771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155771).length < 2 ^ (prefixWord ++ tailWord_4155771).sum := by decide
  have hdescent : baseEnd_4155771 < baseStart_4155771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155788 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 1, 5]
def baseStart_4155788 : Nat := 118140960795 + 4155788 * 2 ^ 59
def prefixEnd_4155788 : Nat := 4983230072969 + 3 ^ 40 * 4155788 * 2
def baseEnd_4155788 : Nat := 711305580729030564679295

theorem tailTrace_4155788 : CollatzResearch.WordTrace tailWord_4155788 prefixEnd_4155788 711305580729030564679295 := by
  unfold tailWord_4155788
  simp only [CollatzResearch.WordTrace]
  refine ⟨75787020334148651464630009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101049360445531535286173345 75787020334148651464630009)
  ·
    refine ⟨56840265250611488598472507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75787020334148651464630009 56840265250611488598472507)
    ·
      refine ⟨85260397875917232897708761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56840265250611488598472507 85260397875917232897708761)
      ·
        refine ⟨63945298406937924673281571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85260397875917232897708761 63945298406937924673281571)
        ·
          refine ⟨95917947610406887009922357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63945298406937924673281571 95917947610406887009922357)
          ·
            refine ⟨8992307588475645657180221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95917947610406887009922357 8992307588475645657180221)
            ·
              refine ⟨3372115345678367121442583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8992307588475645657180221 3372115345678367121442583)
              ·
                refine ⟨5058173018517550682163875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372115345678367121442583 5058173018517550682163875)
                ·
                  refine ⟨7587259527776326023245813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058173018517550682163875 7587259527776326023245813)
                  ·
                    refine ⟨711305580729030564679295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7587259527776326023245813 711305580729030564679295)
                    ·
                      rfl

theorem cell23_4155788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_4155788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155788 prefixEnd_4155788 := by exact prefixLift 4155788
  have htrace : WordTrace (prefixWord ++ tailWord_4155788) baseStart_4155788 baseEnd_4155788 := by
    simpa [prefixWord, tailWord_4155788, baseEnd_4155788] using wordTrace_append hprefix tailTrace_4155788
  have hstable : (prefixWord ++ tailWord_4155788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155788).length < 2 ^ (prefixWord ++ tailWord_4155788).sum := by decide
  have hdescent : baseEnd_4155788 < baseStart_4155788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155802 : List Nat := [3, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3]
def baseStart_4155802 : Nat := 118140960795 + 4155802 * 2 ^ 59
def prefixEnd_4155802 : Nat := 4983230072969 + 3 ^ 40 * 4155802 * 2
def baseEnd_4155802 : Nat := 2133923930916254639262821

theorem tailTrace_4155802 : CollatzResearch.WordTrace tailWord_4155802 prefixEnd_4155802 2133923930916254639262821 := by
  unfold tailWord_4155802
  simp only [CollatzResearch.WordTrace]
  refine ⟨37893637822561645830067415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101049700860164388880179773 37893637822561645830067415)
  ·
    refine ⟨56840456733842468745101123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37893637822561645830067415 56840456733842468745101123)
    ·
      refine ⟨85260685100763703117651685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56840456733842468745101123 85260685100763703117651685)
      ·
        refine ⟨15986378456393194334559691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85260685100763703117651685 15986378456393194334559691)
        ·
          refine ⟨23979567684589791501839537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15986378456393194334559691 23979567684589791501839537)
          ·
            refine ⟨17984675763442343626379653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23979567684589791501839537 17984675763442343626379653)
            ·
              refine ⟨3372126705645439429946185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17984675763442343626379653 3372126705645439429946185)
              ·
                refine ⟨2529095029234079572459639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372126705645439429946185 2529095029234079572459639)
                ·
                  refine ⟨3793642543851119358689459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529095029234079572459639 3793642543851119358689459)
                  ·
                    refine ⟨5690463815776679038034189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3793642543851119358689459 5690463815776679038034189)
                    ·
                      refine ⟨2133923930916254639262821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5690463815776679038034189 2133923930916254639262821)
                      ·
                        rfl

theorem cell23_4155802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_4155802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155802 prefixEnd_4155802 := by exact prefixLift 4155802
  have htrace : WordTrace (prefixWord ++ tailWord_4155802) baseStart_4155802 baseEnd_4155802 := by
    simpa [prefixWord, tailWord_4155802, baseEnd_4155802] using wordTrace_append hprefix tailTrace_4155802
  have hstable : (prefixWord ++ tailWord_4155802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155802).length < 2 ^ (prefixWord ++ tailWord_4155802).sum := by decide
  have hdescent : baseEnd_4155802 < baseStart_4155802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155811 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 3]
def baseStart_4155811 : Nat := 118140960795 + 4155811 * 2 ^ 59
def prefixEnd_4155811 : Nat := 4983230072969 + 3 ^ 40 * 4155811 * 2
def baseEnd_4155811 : Nat := 2133928552242145104050279

theorem tailTrace_4155811 : CollatzResearch.WordTrace tailWord_4155811 prefixEnd_4155811 2133928552242145104050279 := by
  unfold tailWord_4155811
  simp only [CollatzResearch.WordTrace]
  refine ⟨151574879547213977857347287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101049919698142651904898191 151574879547213977857347287)
  ·
    refine ⟨227362319320820966786020931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151574879547213977857347287 227362319320820966786020931)
    ·
      refine ⟨341043478981231450179031397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227362319320820966786020931 341043478981231450179031397)
      ·
        refine ⟨63945652308980896908568387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341043478981231450179031397 63945652308980896908568387)
        ·
          refine ⟨95918478463471345362852581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63945652308980896908568387 95918478463471345362852581)
          ·
            refine ⟨17984714711900877255534859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95918478463471345362852581 17984714711900877255534859)
            ·
              refine ⟨26977072067851315883302289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17984714711900877255534859 26977072067851315883302289)
              ·
                refine ⟨20232804050888486912476717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26977072067851315883302289 20232804050888486912476717)
                ·
                  refine ⟨7587301519083182592178769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20232804050888486912476717 7587301519083182592178769)
                  ·
                    refine ⟨5690476139312386944134077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7587301519083182592178769 5690476139312386944134077)
                    ·
                      refine ⟨2133928552242145104050279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5690476139312386944134077 2133928552242145104050279)
                      ·
                        rfl

theorem cell23_4155811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_4155811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155811 prefixEnd_4155811 := by exact prefixLift 4155811
  have htrace : WordTrace (prefixWord ++ tailWord_4155811) baseStart_4155811 baseEnd_4155811 := by
    simpa [prefixWord, tailWord_4155811, baseEnd_4155811] using wordTrace_append hprefix tailTrace_4155811
  have hstable : (prefixWord ++ tailWord_4155811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155811).length < 2 ^ (prefixWord ++ tailWord_4155811).sum := by decide
  have hdescent : baseEnd_4155811 < baseStart_4155811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155825 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 3, 2, 2]
def baseStart_4155825 : Nat := 118140960795 + 4155825 * 2 ^ 59
def prefixEnd_4155825 : Nat := 4983230072969 + 3 ^ 40 * 4155825 * 2
def baseEnd_4155825 : Nat := 2133935740971308049275215

theorem tailTrace_4155825 : CollatzResearch.WordTrace tailWord_4155825 prefixEnd_4155825 2133935740971308049275215 := by
  unfold tailWord_4155825
  simp only [CollatzResearch.WordTrace]
  refine ⟨151575390169163258248356929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101050260112775505498904619 151575390169163258248356929)
  ·
    refine ⟨113681542626872443686267697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151575390169163258248356929 113681542626872443686267697)
    ·
      refine ⟨85261156970154332764700773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113681542626872443686267697 85261156970154332764700773)
      ·
        refine ⟨15986466931903937393381395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85261156970154332764700773 15986466931903937393381395)
        ·
          refine ⟨23979700397855906090072093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15986466931903937393381395 23979700397855906090072093)
          ·
            refine ⟨8992387649195964783777035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23979700397855906090072093 8992387649195964783777035)
            ·
              refine ⟨13488581473793947175665553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992387649195964783777035 13488581473793947175665553)
              ·
                refine ⟨10116436105345460381749165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13488581473793947175665553 10116436105345460381749165)
                ·
                  refine ⟨3793663539504547643155937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10116436105345460381749165 3793663539504547643155937)
                  ·
                    refine ⟨2845247654628410732366953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3793663539504547643155937 2845247654628410732366953)
                    ·
                      refine ⟨2133935740971308049275215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845247654628410732366953 2133935740971308049275215)
                      ·
                        rfl

theorem cell23_4155825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_4155825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155825 prefixEnd_4155825 := by exact prefixLift 4155825
  have htrace : WordTrace (prefixWord ++ tailWord_4155825) baseStart_4155825 baseEnd_4155825 := by
    simpa [prefixWord, tailWord_4155825, baseEnd_4155825] using wordTrace_append hprefix tailTrace_4155825
  have hstable : (prefixWord ++ tailWord_4155825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155825).length < 2 ^ (prefixWord ++ tailWord_4155825).sum := by decide
  have hdescent : baseEnd_4155825 < baseStart_4155825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155831 : List Nat := [1, 1, 3, 1, 3, 4, 3, 7]
def baseStart_4155831 : Nat := 118140960795 + 4155831 * 2 ^ 59
def prefixEnd_4155831 : Nat := 4983230072969 + 3 ^ 40 * 4155831 * 2
def baseEnd_4155831 : Nat := 79034771179823519474081

theorem tailTrace_4155831 : CollatzResearch.WordTrace tailWord_4155831 prefixEnd_4155831 79034771179823519474081 := by
  unfold tailWord_4155831
  simp only [CollatzResearch.WordTrace]
  refine ⟨151575609007141521273075347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101050406004761014182050231 151575609007141521273075347)
  ·
    refine ⟨227363413510712281909613021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151575609007141521273075347 227363413510712281909613021)
    ·
      refine ⟨85261280066517105716104883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227363413510712281909613021 85261280066517105716104883)
      ·
        refine ⟨127891920099775658574157325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85261280066517105716104883 127891920099775658574157325)
        ·
          refine ⟨47959470037415871965308997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127891920099775658574157325 47959470037415871965308997)
          ·
            refine ⟨8992400632015475993495437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47959470037415871965308997 8992400632015475993495437)
            ·
              refine ⟨3372150237005803497560789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8992400632015475993495437 3372150237005803497560789)
              ·
                refine ⟨79034771179823519474081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3372150237005803497560789 79034771179823519474081)
                ·
                  rfl

theorem cell23_4155831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 7].length) (baseStart_4155831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155831 prefixEnd_4155831 := by exact prefixLift 4155831
  have htrace : WordTrace (prefixWord ++ tailWord_4155831) baseStart_4155831 baseEnd_4155831 := by
    simpa [prefixWord, tailWord_4155831, baseEnd_4155831] using wordTrace_append hprefix tailTrace_4155831
  have hstable : (prefixWord ++ tailWord_4155831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155831).length < 2 ^ (prefixWord ++ tailWord_4155831).sum := by decide
  have hdescent : baseEnd_4155831 < baseStart_4155831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155852 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 2, 4]
def baseStart_4155852 : Nat := 118140960795 + 4155852 * 2 ^ 59
def prefixEnd_4155852 : Nat := 4983230072969 + 3 ^ 40 * 4155852 * 2
def baseEnd_4155852 : Nat := 711316534982993147879197

theorem tailTrace_4155852 : CollatzResearch.WordTrace tailWord_4155852 prefixEnd_4155852 711316534982993147879197 := by
  unfold tailWord_4155852
  simp only [CollatzResearch.WordTrace]
  refine ⟨75788187470032720929794905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101050916626710294573059873 75788187470032720929794905)
  ·
    refine ⟨56841140602524540697346179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75788187470032720929794905 56841140602524540697346179)
    ·
      refine ⟨85261710903786811046019269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56841140602524540697346179 85261710903786811046019269)
      ·
        refine ⟨15986570794460027071128613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85261710903786811046019269 15986570794460027071128613)
        ·
          refine ⟨2997482023961255075836615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15986570794460027071128613 2997482023961255075836615)
          ·
            refine ⟨4496223035941882613754923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997482023961255075836615 4496223035941882613754923)
            ·
              refine ⟨6744334553912823920632385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496223035941882613754923 6744334553912823920632385)
              ·
                refine ⟨5058250915434617940474289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6744334553912823920632385 5058250915434617940474289)
                ·
                  refine ⟨3793688186575963455355717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058250915434617940474289 3793688186575963455355717)
                  ·
                    refine ⟨711316534982993147879197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3793688186575963455355717 711316534982993147879197)
                    ·
                      rfl

theorem cell23_4155852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_4155852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155852 prefixEnd_4155852 := by exact prefixLift 4155852
  have htrace : WordTrace (prefixWord ++ tailWord_4155852) baseStart_4155852 baseEnd_4155852 := by
    simpa [prefixWord, tailWord_4155852, baseEnd_4155852] using wordTrace_append hprefix tailTrace_4155852
  have hstable : (prefixWord ++ tailWord_4155852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155852).length < 2 ^ (prefixWord ++ tailWord_4155852).sum := by decide
  have hdescent : baseEnd_4155852 < baseStart_4155852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155875 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 1, 3, 3]
def baseStart_4155875 : Nat := 118140960795 + 4155875 * 2 ^ 59
def prefixEnd_4155875 : Nat := 4983230072969 + 3 ^ 40 * 4155875 * 2
def baseEnd_4155875 : Nat := 2133961415004032853649985

theorem tailTrace_4155875 : CollatzResearch.WordTrace tailWord_4155875 prefixEnd_4155875 2133961415004032853649985 := by
  unfold tailWord_4155875
  simp only [CollatzResearch.WordTrace]
  refine ⟨151577213818982116787677079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101051475879321411191784719 151577213818982116787677079)
  ·
    refine ⟨227365820728473175181515619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151577213818982116787677079 227365820728473175181515619)
    ·
      refine ⟨341048731092709762772273429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227365820728473175181515619 341048731092709762772273429)
      ·
        refine ⟨15986659269970770129950317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 341048731092709762772273429 15986659269970770129950317)
        ·
          refine ⟨5994997226239038798731369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15986659269970770129950317 5994997226239038798731369)
          ·
            refine ⟨4496247919679279099048527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5994997226239038798731369 4496247919679279099048527)
            ·
              refine ⟨6744371879518918648572791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496247919679279099048527 6744371879518918648572791)
              ·
                refine ⟨10116557819278377972859187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6744371879518918648572791 10116557819278377972859187)
                ·
                  refine ⟨15174836728917566959288781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10116557819278377972859187 15174836728917566959288781)
                  ·
                    refine ⟨5690563773344087609733293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15174836728917566959288781 5690563773344087609733293)
                    ·
                      refine ⟨2133961415004032853649985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5690563773344087609733293 2133961415004032853649985)
                      ·
                        rfl

theorem cell23_4155875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_4155875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155875 prefixEnd_4155875 := by exact prefixLift 4155875
  have htrace : WordTrace (prefixWord ++ tailWord_4155875) baseStart_4155875 baseEnd_4155875 := by
    simpa [prefixWord, tailWord_4155875, baseEnd_4155875] using wordTrace_append hprefix tailTrace_4155875
  have hstable : (prefixWord ++ tailWord_4155875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155875).length < 2 ^ (prefixWord ++ tailWord_4155875).sum := by decide
  have hdescent : baseEnd_4155875 < baseStart_4155875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155893 : List Nat := [1, 3, 5, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4155893 : Nat := 118140960795 + 4155893 * 2 ^ 59
def prefixEnd_4155893 : Nat := 4983230072969 + 3 ^ 40 * 4155893 * 2
def baseEnd_4155893 : Nat := 2133970657655813783224903

theorem tailTrace_4155893 : CollatzResearch.WordTrace tailWord_4155893 prefixEnd_4155893 2133970657655813783224903 := by
  unfold tailWord_4155893
  simp only [CollatzResearch.WordTrace]
  refine ⟨151577870332916905861832333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101051913555277937241221555 151577870332916905861832333)
  ·
    refine ⟨56841701374843839698187125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151577870332916905861832333 56841701374843839698187125)
    ·
      refine ⟨5328909503891609971705043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56841701374843839698187125 5328909503891609971705043)
      ·
        refine ⟨7993364255837414957557565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328909503891609971705043 7993364255837414957557565)
        ·
          refine ⟨2997511595939030609084087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7993364255837414957557565 2997511595939030609084087)
          ·
            refine ⟨4496267393908545913626131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997511595939030609084087 4496267393908545913626131)
            ·
              refine ⟨6744401090862818870439197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496267393908545913626131 6744401090862818870439197)
              ·
                refine ⟨2529150409073557076414699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6744401090862818870439197 2529150409073557076414699)
                ·
                  refine ⟨3793725613610335614622049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529150409073557076414699 3793725613610335614622049)
                  ·
                    refine ⟨2845294210207751710966537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3793725613610335614622049 2845294210207751710966537)
                    ·
                      refine ⟨2133970657655813783224903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845294210207751710966537 2133970657655813783224903)
                      ·
                        rfl

theorem cell23_4155893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4155893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155893 prefixEnd_4155893 := by exact prefixLift 4155893
  have htrace : WordTrace (prefixWord ++ tailWord_4155893) baseStart_4155893 baseEnd_4155893 := by
    simpa [prefixWord, tailWord_4155893, baseEnd_4155893] using wordTrace_append hprefix tailTrace_4155893
  have hstable : (prefixWord ++ tailWord_4155893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155893).length < 2 ^ (prefixWord ++ tailWord_4155893).sum := by decide
  have hdescent : baseEnd_4155893 < baseStart_4155893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155901 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_4155901 : Nat := 118140960795 + 4155901 * 2 ^ 59
def prefixEnd_4155901 : Nat := 4983230072969 + 3 ^ 40 * 4155901 * 2
def baseEnd_4155901 : Nat := 2133974765501049751924865

theorem tailTrace_4155901 : CollatzResearch.WordTrace tailWord_4155901 prefixEnd_4155901 2133974765501049751924865 := by
  unfold tailWord_4155901
  simp only [CollatzResearch.WordTrace]
  refine ⟨151578162116887923228123557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101052108077925282152082371 151578162116887923228123557)
  ·
    refine ⟨28420905396916485605273167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151578162116887923228123557 28420905396916485605273167)
    ·
      refine ⟨42631358095374728407909751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28420905396916485605273167 42631358095374728407909751)
      ·
        refine ⟨63947037143062092611864627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42631358095374728407909751 63947037143062092611864627)
        ·
          refine ⟨95920555714593138917796941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63947037143062092611864627 95920555714593138917796941)
          ·
            refine ⟨35970208392972427094173853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95920555714593138917796941 35970208392972427094173853)
            ·
              refine ⟨13488828147364660160315195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35970208392972427094173853 13488828147364660160315195)
              ·
                refine ⟨20233242221046990240472793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13488828147364660160315195 20233242221046990240472793)
                ·
                  refine ⟨15174931665785242680354595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20233242221046990240472793 15174931665785242680354595)
                  ·
                    refine ⟨22762397498677864020531893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15174931665785242680354595 22762397498677864020531893)
                    ·
                      refine ⟨2133974765501049751924865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22762397498677864020531893 2133974765501049751924865)
                      ·
                        rfl

theorem cell23_4155901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_4155901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155901 prefixEnd_4155901 := by exact prefixLift 4155901
  have htrace : WordTrace (prefixWord ++ tailWord_4155901) baseStart_4155901 baseEnd_4155901 := by
    simpa [prefixWord, tailWord_4155901, baseEnd_4155901] using wordTrace_append hprefix tailTrace_4155901
  have hstable : (prefixWord ++ tailWord_4155901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155901).length < 2 ^ (prefixWord ++ tailWord_4155901).sum := by decide
  have hdescent : baseEnd_4155901 < baseStart_4155901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155910 : List Nat := [6, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_4155910 : Nat := 118140960795 + 4155910 * 2 ^ 59
def prefixEnd_4155910 : Nat := 4983230072969 + 3 ^ 40 * 4155910 * 2
def baseEnd_4155910 : Nat := 2133979386826940216712325

theorem tailTrace_4155910 : CollatzResearch.WordTrace tailWord_4155910 prefixEnd_4155910 2133979386826940216712325 := by
  unfold tailWord_4155910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736827824182978680162537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101052326915903545176800789 4736827824182978680162537)
  ·
    refine ⟨3552620868137234010121903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4736827824182978680162537 3552620868137234010121903)
    ·
      refine ⟨5328931302205851015182855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552620868137234010121903 5328931302205851015182855)
      ·
        refine ⟨7993396953308776522774283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328931302205851015182855 7993396953308776522774283)
        ·
          refine ⟨11990095429963164784161425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993396953308776522774283 11990095429963164784161425)
          ·
            refine ⟨8992571572472373588121069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11990095429963164784161425 8992571572472373588121069)
            ·
              refine ⟨3372214339677140095545401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8992571572472373588121069 3372214339677140095545401)
              ·
                refine ⟨2529160754757855071659051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372214339677140095545401 2529160754757855071659051)
                ·
                  refine ⟨3793741132136782607488577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529160754757855071659051 3793741132136782607488577)
                  ·
                    refine ⟨2845305849102586955616433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3793741132136782607488577 2845305849102586955616433)
                    ·
                      refine ⟨2133979386826940216712325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845305849102586955616433 2133979386826940216712325)
                      ·
                        rfl

theorem cell23_4155910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_4155910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155910 prefixEnd_4155910 := by exact prefixLift 4155910
  have htrace : WordTrace (prefixWord ++ tailWord_4155910) baseStart_4155910 baseEnd_4155910 := by
    simpa [prefixWord, tailWord_4155910, baseEnd_4155910] using wordTrace_append hprefix tailTrace_4155910
  have hstable : (prefixWord ++ tailWord_4155910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155910).length < 2 ^ (prefixWord ++ tailWord_4155910).sum := by decide
  have hdescent : baseEnd_4155910 < baseStart_4155910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155915 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 4, 2, 2]
def baseStart_4155915 : Nat := 118140960795 + 4155915 * 2 ^ 59
def prefixEnd_4155915 : Nat := 4983230072969 + 3 ^ 40 * 4155915 * 2
def baseEnd_4155915 : Nat := 2133981954230212697149801

theorem tailTrace_4155915 : CollatzResearch.WordTrace tailWord_4155915 prefixEnd_4155915 2133981954230212697149801 := by
  unfold tailWord_4155915
  simp only [CollatzResearch.WordTrace]
  refine ⟨151578672738837203619133199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101052448492558135746088799 151578672738837203619133199)
  ·
    refine ⟨227368009108255805428699799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151578672738837203619133199 227368009108255805428699799)
    ·
      refine ⟨341052013662383708143049699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227368009108255805428699799 341052013662383708143049699)
      ·
        refine ⟨511578020493575562214574549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341052013662383708143049699 511578020493575562214574549)
        ·
          refine ⟨11990109855318177239404091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 511578020493575562214574549 11990109855318177239404091)
          ·
            refine ⟨17985164782977265859106137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11990109855318177239404091 17985164782977265859106137)
            ·
              refine ⟨13488873587232949394329603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17985164782977265859106137 13488873587232949394329603)
              ·
                refine ⟨20233310380849424091494405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13488873587232949394329603 20233310380849424091494405)
                ·
                  refine ⟨3793745696409267017155201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20233310380849424091494405 3793745696409267017155201)
                  ·
                    refine ⟨2845309272306950262866401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3793745696409267017155201 2845309272306950262866401)
                    ·
                      refine ⟨2133981954230212697149801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845309272306950262866401 2133981954230212697149801)
                      ·
                        rfl

theorem cell23_4155915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 2, 2].length) (baseStart_4155915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155915 prefixEnd_4155915 := by exact prefixLift 4155915
  have htrace : WordTrace (prefixWord ++ tailWord_4155915) baseStart_4155915 baseEnd_4155915 := by
    simpa [prefixWord, tailWord_4155915, baseEnd_4155915] using wordTrace_append hprefix tailTrace_4155915
  have hstable : (prefixWord ++ tailWord_4155915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155915).length < 2 ^ (prefixWord ++ tailWord_4155915).sum := by decide
  have hdescent : baseEnd_4155915 < baseStart_4155915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155932 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_4155932 : Nat := 118140960795 + 4155932 * 2 ^ 59
def prefixEnd_4155932 : Nat := 4983230072969 + 3 ^ 40 * 4155932 * 2
def baseEnd_4155932 : Nat := 2133990683401339130637223

theorem tailTrace_4155932 : CollatzResearch.WordTrace tailWord_4155932 prefixEnd_4155932 2133990683401339130637223 := by
  unfold tailWord_4155932
  simp only [CollatzResearch.WordTrace]
  refine ⟨75789646389887807761251025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101052861853183743681668033 75789646389887807761251025)
  ·
    refine ⟨56842234792415855820938269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75789646389887807761251025 56842234792415855820938269)
    ·
      refine ⟨21315838047155945932851851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56842234792415855820938269 21315838047155945932851851)
      ·
        refine ⟨31973757070733918899277777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21315838047155945932851851 31973757070733918899277777)
        ·
          refine ⟨23980317803050439174458333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31973757070733918899277777 23980317803050439174458333)
          ·
            refine ⟨8992619176143914690421875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23980317803050439174458333 8992619176143914690421875)
            ·
              refine ⟨13488928764215872035632813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992619176143914690421875 13488928764215872035632813)
              ·
                refine ⟨5058348286580952013362305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13488928764215872035632813 5058348286580952013362305)
                ·
                  refine ⟨3793761214935714010021729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058348286580952013362305 3793761214935714010021729)
                  ·
                    refine ⟨2845320911201785507516297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3793761214935714010021729 2845320911201785507516297)
                    ·
                      refine ⟨2133990683401339130637223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845320911201785507516297 2133990683401339130637223)
                      ·
                        rfl

theorem cell23_4155932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_4155932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155932 prefixEnd_4155932 := by exact prefixLift 4155932
  have htrace : WordTrace (prefixWord ++ tailWord_4155932) baseStart_4155932 baseEnd_4155932 := by
    simpa [prefixWord, tailWord_4155932, baseEnd_4155932] using wordTrace_append hprefix tailTrace_4155932
  have hstable : (prefixWord ++ tailWord_4155932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155932).length < 2 ^ (prefixWord ++ tailWord_4155932).sum := by decide
  have hdescent : baseEnd_4155932 < baseStart_4155932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155961 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4155961 : Nat := 118140960795 + 4155961 * 2 ^ 59
def prefixEnd_4155961 : Nat := 4983230072969 + 3 ^ 40 * 4155961 * 2
def baseEnd_4155961 : Nat := 2134005574340319517174589

theorem tailTrace_4155961 : CollatzResearch.WordTrace tailWord_4155961 prefixEnd_4155961 2134005574340319517174589 := by
  unfold tailWord_4155961
  simp only [CollatzResearch.WordTrace]
  refine ⟨151580350496670553475307737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101053566997780368983538491 151580350496670553475307737)
  ·
    refine ⟨113685262872502915106480803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151580350496670553475307737 113685262872502915106480803)
    ·
      refine ⟨170527894308754372659721205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113685262872502915106480803 170527894308754372659721205)
      ·
        refine ⟨15986990091445722436848863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170527894308754372659721205 15986990091445722436848863)
        ·
          refine ⟨23980485137168583655273295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15986990091445722436848863 23980485137168583655273295)
          ·
            refine ⟨35970727705752875482909943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23980485137168583655273295 35970727705752875482909943)
            ·
              refine ⟨53956091558629313224364915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35970727705752875482909943 53956091558629313224364915)
              ·
                refine ⟨80934137337943969836547373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53956091558629313224364915 80934137337943969836547373)
                ·
                  refine ⟨30350301501728988688705265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80934137337943969836547373 30350301501728988688705265)
                  ·
                    refine ⟨22762726126296741516528949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30350301501728988688705265 22762726126296741516528949)
                    ·
                      refine ⟨2134005574340319517174589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22762726126296741516528949 2134005574340319517174589)
                      ·
                        rfl

theorem cell23_4155961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4155961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155961 prefixEnd_4155961 := by exact prefixLift 4155961
  have htrace : WordTrace (prefixWord ++ tailWord_4155961) baseStart_4155961 baseEnd_4155961 := by
    simpa [prefixWord, tailWord_4155961, baseEnd_4155961] using wordTrace_append hprefix tailTrace_4155961
  have hstable : (prefixWord ++ tailWord_4155961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155961).length < 2 ^ (prefixWord ++ tailWord_4155961).sum := by decide
  have hdescent : baseEnd_4155961 < baseStart_4155961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155966 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4155966 : Nat := 118140960795 + 4155966 * 2 ^ 59
def prefixEnd_4155966 : Nat := 4983230072969 + 3 ^ 40 * 4155966 * 2
def baseEnd_4155966 : Nat := 2134008141743591997612067

theorem tailTrace_4155966 : CollatzResearch.WordTrace tailWord_4155966 prefixEnd_4155966 2134008141743591997612067 := by
  unfold tailWord_4155966
  simp only [CollatzResearch.WordTrace]
  refine ⟨18947566607706554916154969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101053688574434959552826501 18947566607706554916154969)
  ·
    refine ⟨14210674955779916187116227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18947566607706554916154969 14210674955779916187116227)
    ·
      refine ⟨21316012433669874280674341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14210674955779916187116227 21316012433669874280674341)
      ·
        refine ⟨3996752331313101427626439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21316012433669874280674341 3996752331313101427626439)
        ·
          refine ⟨5995128496969652141439659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996752331313101427626439 5995128496969652141439659)
          ·
            refine ⟨8992692745454478212159489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5995128496969652141439659 8992692745454478212159489)
            ·
              refine ⟨6744519559090858659119617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8992692745454478212159489 6744519559090858659119617)
              ·
                refine ⟨5058389669318143994339713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6744519559090858659119617 5058389669318143994339713)
                ·
                  refine ⟨3793792251988607995754785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058389669318143994339713 3793792251988607995754785)
                  ·
                    refine ⟨2845344188991455996816089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3793792251988607995754785 2845344188991455996816089)
                    ·
                      refine ⟨2134008141743591997612067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845344188991455996816089 2134008141743591997612067)
                      ·
                        rfl

theorem cell23_4155966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4155966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4155966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4155966 prefixEnd_4155966 := by exact prefixLift 4155966
  have htrace : WordTrace (prefixWord ++ tailWord_4155966) baseStart_4155966 baseEnd_4155966 := by
    simpa [prefixWord, tailWord_4155966, baseEnd_4155966] using wordTrace_append hprefix tailTrace_4155966
  have hstable : (prefixWord ++ tailWord_4155966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155966).length < 2 ^ (prefixWord ++ tailWord_4155966).sum := by decide
  have hdescent : baseEnd_4155966 < baseStart_4155966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156015 : List Nat := [1, 1, 2, 1, 3, 2, 3, 5, 1, 4]
def baseStart_4156015 : Nat := 118140960795 + 4156015 * 2 ^ 59
def prefixEnd_4156015 : Nat := 4983230072969 + 3 ^ 40 * 4156015 * 2
def baseEnd_4156015 : Nat := 711344434098554101966447

theorem tailTrace_4156015 : CollatzResearch.WordTrace tailWord_4156015 prefixEnd_4156015 711344434098554101966447 := by
  unfold tailWord_4156015
  simp only [CollatzResearch.WordTrace]
  refine ⟨151582320038474920697773499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101054880025649947131848999 151582320038474920697773499)
  ·
    refine ⟨227373480057712381046660249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151582320038474920697773499 227373480057712381046660249)
    ·
      refine ⟨170530110043284285784995187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227373480057712381046660249 170530110043284285784995187)
      ·
        refine ⟨255795165064926428677492781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170530110043284285784995187 255795165064926428677492781)
        ·
          refine ⟨95923186899347410754059793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255795165064926428677492781 95923186899347410754059793)
          ·
            refine ⟨71942390174510558065544845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95923186899347410754059793 71942390174510558065544845)
            ·
              refine ⟨26978396315441459274579317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71942390174510558065544845 26978396315441459274579317)
              ·
                refine ⟨2529224654572636806991811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26978396315441459274579317 2529224654572636806991811)
                ·
                  refine ⟨3793836981858955210487717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529224654572636806991811 3793836981858955210487717)
                  ·
                    refine ⟨711344434098554101966447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3793836981858955210487717 711344434098554101966447)
                    ·
                      rfl

theorem cell23_4156015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 1, 4].length) (baseStart_4156015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156015 prefixEnd_4156015 := by exact prefixLift 4156015
  have htrace : WordTrace (prefixWord ++ tailWord_4156015) baseStart_4156015 baseEnd_4156015 := by
    simpa [prefixWord, tailWord_4156015, baseEnd_4156015] using wordTrace_append hprefix tailTrace_4156015
  have hstable : (prefixWord ++ tailWord_4156015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156015).length < 2 ^ (prefixWord ++ tailWord_4156015).sum := by decide
  have hdescent : baseEnd_4156015 < baseStart_4156015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156028 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 6]
def baseStart_4156028 : Nat := 118140960795 + 4156028 * 2 ^ 59
def prefixEnd_4156028 : Nat := 4983230072969 + 3 ^ 40 * 4156028 * 2
def baseEnd_4156028 : Nat := 237115553060463417226309

theorem tailTrace_4156028 : CollatzResearch.WordTrace tailWord_4156028 prefixEnd_4156028 237115553060463417226309 := by
  unfold tailWord_4156028
  simp only [CollatzResearch.WordTrace]
  refine ⟨75791397093713911958998369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101055196124951882611997825 75791397093713911958998369)
  ·
    refine ⟨56843547820285433969248777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75791397093713911958998369 56843547820285433969248777)
    ·
      refine ⟨42632660865214075476936583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56843547820285433969248777 42632660865214075476936583)
      ·
        refine ⟨63948991297821113215404875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42632660865214075476936583 63948991297821113215404875)
        ·
          refine ⟨95923486946731669823107313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63948991297821113215404875 95923486946731669823107313)
          ·
            refine ⟨71942615210048752367330485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95923486946731669823107313 71942615210048752367330485)
            ·
              refine ⟨6744620175942070534437233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71942615210048752367330485 6744620175942070534437233)
              ·
                refine ⟨5058465131956552900827925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6744620175942070534437233 5058465131956552900827925)
                ·
                  refine ⟨237115553060463417226309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5058465131956552900827925 237115553060463417226309)
                  ·
                    rfl

theorem cell23_4156028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_4156028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156028 prefixEnd_4156028 := by exact prefixLift 4156028
  have htrace : WordTrace (prefixWord ++ tailWord_4156028) baseStart_4156028 baseEnd_4156028 := by
    simpa [prefixWord, tailWord_4156028, baseEnd_4156028] using wordTrace_append hprefix tailTrace_4156028
  have hstable : (prefixWord ++ tailWord_4156028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156028).length < 2 ^ (prefixWord ++ tailWord_4156028).sum := by decide
  have hdescent : baseEnd_4156028 < baseStart_4156028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156055 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 3, 1, 3]
def baseStart_4156055 : Nat := 118140960795 + 4156055 * 2 ^ 59
def prefixEnd_4156055 : Nat := 4983230072969 + 3 ^ 40 * 4156055 * 2
def baseEnd_4156055 : Nat := 2134053841521842149399157

theorem tailTrace_4156055 : CollatzResearch.WordTrace tailWord_4156055 prefixEnd_4156055 2134053841521842149399157 := by
  unfold tailWord_4156055
  simp only [CollatzResearch.WordTrace]
  refine ⟨151583778958330007529229619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101055852638886671686153079 151583778958330007529229619)
  ·
    refine ⟨227375668437495011293844429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151583778958330007529229619 227375668437495011293844429)
    ·
      refine ⟨85265875664060629235191661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227375668437495011293844429 85265875664060629235191661)
      ·
        refine ⟨31974703374022735963196873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85265875664060629235191661 31974703374022735963196873)
        ·
          refine ⟨23981027530517051972397655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31974703374022735963196873 23981027530517051972397655)
          ·
            refine ⟨35971541295775577958596483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23981027530517051972397655 35971541295775577958596483)
            ·
              refine ⟨53957311943663366937894725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35971541295775577958596483 53957311943663366937894725)
              ·
                refine ⟨10116995989436881300855261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53957311943663366937894725 10116995989436881300855261)
                ·
                  refine ⟨3793873496038830487820723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10116995989436881300855261 3793873496038830487820723)
                  ·
                    refine ⟨5690810244058245731731085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3793873496038830487820723 5690810244058245731731085)
                    ·
                      refine ⟨2134053841521842149399157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5690810244058245731731085 2134053841521842149399157)
                      ·
                        rfl

theorem cell23_4156055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_4156055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156055 prefixEnd_4156055 := by exact prefixLift 4156055
  have htrace : WordTrace (prefixWord ++ tailWord_4156055) baseStart_4156055 baseEnd_4156055 := by
    simpa [prefixWord, tailWord_4156055, baseEnd_4156055] using wordTrace_append hprefix tailTrace_4156055
  have hstable : (prefixWord ++ tailWord_4156055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156055).length < 2 ^ (prefixWord ++ tailWord_4156055).sum := by decide
  have hdescent : baseEnd_4156055 < baseStart_4156055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156146 : List Nat := [3, 2, 1, 3, 1, 3, 1, 4, 1, 2, 2]
def baseStart_4156146 : Nat := 118140960795 + 4156146 * 2 ^ 59
def prefixEnd_4156146 : Nat := 4983230072969 + 3 ^ 40 * 4156146 * 2
def baseEnd_4156146 : Nat := 2134100568261401293361239

theorem tailTrace_4156146 : CollatzResearch.WordTrace tailWord_4156146 prefixEnd_4156146 2134100568261401293361239 := by
  unfold tailWord_4156146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37896774500250082517698073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101058065334000220047194861 37896774500250082517698073)
  ·
    refine ⟨28422580875187561888273555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37896774500250082517698073 28422580875187561888273555)
    ·
      refine ⟨42633871312781342832410333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28422580875187561888273555 42633871312781342832410333)
      ·
        refine ⟨15987701742293003562153875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42633871312781342832410333 15987701742293003562153875)
        ·
          refine ⟨23981552613439505343230813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15987701742293003562153875 23981552613439505343230813)
          ·
            refine ⟨8993082230039814503711555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23981552613439505343230813 8993082230039814503711555)
            ·
              refine ⟨13489623345059721755567333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993082230039814503711555 13489623345059721755567333)
              ·
                refine ⟨2529304377198697829168875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13489623345059721755567333 2529304377198697829168875)
                ·
                  refine ⟨3793956565798046743753313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529304377198697829168875 3793956565798046743753313)
                  ·
                    refine ⟨2845467424348535057814985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3793956565798046743753313 2845467424348535057814985)
                    ·
                      refine ⟨2134100568261401293361239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845467424348535057814985 2134100568261401293361239)
                      ·
                        rfl

theorem cell23_4156146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_4156146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156146 prefixEnd_4156146 := by exact prefixLift 4156146
  have htrace : WordTrace (prefixWord ++ tailWord_4156146) baseStart_4156146 baseEnd_4156146 := by
    simpa [prefixWord, tailWord_4156146, baseEnd_4156146] using wordTrace_append hprefix tailTrace_4156146
  have hstable : (prefixWord ++ tailWord_4156146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156146).length < 2 ^ (prefixWord ++ tailWord_4156146).sum := by decide
  have hdescent : baseEnd_4156146 < baseStart_4156146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156162 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_4156162 : Nat := 118140960795 + 4156162 * 2 ^ 59
def prefixEnd_4156162 : Nat := 4983230072969 + 3 ^ 40 * 4156162 * 2
def baseEnd_4156162 : Nat := 2134108783951873230761165

theorem tailTrace_4156162 : CollatzResearch.WordTrace tailWord_4156162 prefixEnd_4156162 2134108783951873230761165 := by
  unfold tailWord_4156162
  simp only [CollatzResearch.WordTrace]
  refine ⟨37896920392235591200843685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101058454379294909868916493 37896920392235591200843685)
  ·
    refine ⟨7105672573544173350158191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37896920392235591200843685 7105672573544173350158191)
    ·
      refine ⟨10658508860316260025237287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7105672573544173350158191 10658508860316260025237287)
      ·
        refine ⟨15987763290474390037855931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10658508860316260025237287 15987763290474390037855931)
        ·
          refine ⟨23981644935711585056783897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15987763290474390037855931 23981644935711585056783897)
          ·
            refine ⟨17986233701783688792587923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23981644935711585056783897 17986233701783688792587923)
            ·
              refine ⟨26979350552675533188881885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17986233701783688792587923 26979350552675533188881885)
              ·
                refine ⟨10117256457253324945830707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26979350552675533188881885 10117256457253324945830707)
                ·
                  refine ⟨15175884685879987418746061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10117256457253324945830707 15175884685879987418746061)
                  ·
                    refine ⟨5690956757204995282029773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15175884685879987418746061 5690956757204995282029773)
                    ·
                      refine ⟨2134108783951873230761165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5690956757204995282029773 2134108783951873230761165)
                      ·
                        rfl

theorem cell23_4156162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_4156162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156162 prefixEnd_4156162 := by exact prefixLift 4156162
  have htrace : WordTrace (prefixWord ++ tailWord_4156162) baseStart_4156162 baseEnd_4156162 := by
    simpa [prefixWord, tailWord_4156162, baseEnd_4156162] using wordTrace_append hprefix tailTrace_4156162
  have hstable : (prefixWord ++ tailWord_4156162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156162).length < 2 ^ (prefixWord ++ tailWord_4156162).sum := by decide
  have hdescent : baseEnd_4156162 < baseStart_4156162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156172 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 1, 3, 2]
def baseStart_4156172 : Nat := 118140960795 + 4156172 * 2 ^ 59
def prefixEnd_4156172 : Nat := 4983230072969 + 3 ^ 40 * 4156172 * 2
def baseEnd_4156172 : Nat := 2134113918758418191636119

theorem tailTrace_4156172 : CollatzResearch.WordTrace tailWord_4156172 prefixEnd_4156172 2134113918758418191636119 := by
  unfold tailWord_4156172
  simp only [CollatzResearch.WordTrace]
  refine ⟨75794023149453068255619385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101058697532604091007492513 75794023149453068255619385)
  ·
    refine ⟨56845517362089801191714539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75794023149453068255619385 56845517362089801191714539)
    ·
      refine ⟨85268276043134701787571809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56845517362089801191714539 85268276043134701787571809)
      ·
        refine ⟨63951207032351026340678857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85268276043134701787571809 63951207032351026340678857)
        ·
          refine ⟨47963405274263269755509143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63951207032351026340678857 47963405274263269755509143)
          ·
            refine ⟨71945107911394904633263715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47963405274263269755509143 71945107911394904633263715)
            ·
              refine ⟨107917661867092356949895573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71945107911394904633263715 107917661867092356949895573)
              ·
                refine ⟨5058640400019954232026355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107917661867092356949895573 5058640400019954232026355)
                ·
                  refine ⟨7587960600029931348039533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058640400019954232026355 7587960600029931348039533)
                  ·
                    refine ⟨2845485225011224255514825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7587960600029931348039533 2845485225011224255514825)
                    ·
                      refine ⟨2134113918758418191636119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845485225011224255514825 2134113918758418191636119)
                      ·
                        rfl

theorem cell23_4156172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_4156172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156172 prefixEnd_4156172 := by exact prefixLift 4156172
  have htrace : WordTrace (prefixWord ++ tailWord_4156172) baseStart_4156172 baseEnd_4156172 := by
    simpa [prefixWord, tailWord_4156172, baseEnd_4156172] using wordTrace_append hprefix tailTrace_4156172
  have hstable : (prefixWord ++ tailWord_4156172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156172).length < 2 ^ (prefixWord ++ tailWord_4156172).sum := by decide
  have hdescent : baseEnd_4156172 < baseStart_4156172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156185 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 3, 4, 2]
def baseStart_4156185 : Nat := 118140960795 + 4156185 * 2 ^ 59
def prefixEnd_4156185 : Nat := 4983230072969 + 3 ^ 40 * 4156185 * 2
def baseEnd_4156185 : Nat := 2134120594006926640773559

theorem tailTrace_4156185 : CollatzResearch.WordTrace tailWord_4156185 prefixEnd_4156185 2134120594006926640773559 := by
  unfold tailWord_4156185
  simp only [CollatzResearch.WordTrace]
  refine ⟨151588520447859039731462009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101059013631906026487641339 151588520447859039731462009)
  ·
    refine ⟨113691390335894279798596507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151588520447859039731462009 113691390335894279798596507)
    ·
      refine ⟨170537085503841419697894761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113691390335894279798596507 170537085503841419697894761)
      ·
        refine ⟨127902814127881064773421071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170537085503841419697894761 127902814127881064773421071)
        ·
          refine ⟨191854221191821597160131607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127902814127881064773421071 191854221191821597160131607)
          ·
            refine ⟨287781331787732395740197411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191854221191821597160131607 287781331787732395740197411)
            ·
              refine ⟨431671997681598593610296117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287781331787732395740197411 431671997681598593610296117)
              ·
                refine ⟨40469249782649868150965261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 431671997681598593610296117 40469249782649868150965261)
                ·
                  refine ⟨15175968668493700556611973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40469249782649868150965261 15175968668493700556611973)
                  ·
                    refine ⟨2845494125342568854364745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15175968668493700556611973 2845494125342568854364745)
                    ·
                      refine ⟨2134120594006926640773559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845494125342568854364745 2134120594006926640773559)
                      ·
                        rfl

theorem cell23_4156185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_4156185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156185 prefixEnd_4156185 := by exact prefixLift 4156185
  have htrace : WordTrace (prefixWord ++ tailWord_4156185) baseStart_4156185 baseEnd_4156185 := by
    simpa [prefixWord, tailWord_4156185, baseEnd_4156185] using wordTrace_append hprefix tailTrace_4156185
  have hstable : (prefixWord ++ tailWord_4156185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156185).length < 2 ^ (prefixWord ++ tailWord_4156185).sum := by decide
  have hdescent : baseEnd_4156185 < baseStart_4156185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156196 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_4156196 : Nat := 118140960795 + 4156196 * 2 ^ 59
def prefixEnd_4156196 : Nat := 4983230072969 + 3 ^ 40 * 4156196 * 2
def baseEnd_4156196 : Nat := 2134126242294126097736009

theorem tailTrace_4156196 : CollatzResearch.WordTrace tailWord_4156196 prefixEnd_4156196 2134126242294126097736009 := by
  unfold tailWord_4156196
  simp only [CollatzResearch.WordTrace]
  refine ⟨75794460825409594305056221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101059281100546125740074961 75794460825409594305056221)
  ·
    refine ⟨28422922809528597864396083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75794460825409594305056221 28422922809528597864396083)
    ·
      refine ⟨42634384214292896796594125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28422922809528597864396083 42634384214292896796594125)
      ·
        refine ⟨15987894080359836298722797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42634384214292896796594125 15987894080359836298722797)
        ·
          refine ⟨5995460280134938612021049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15987894080359836298722797 5995460280134938612021049)
          ·
            refine ⟨4496595210101203959015787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5995460280134938612021049 4496595210101203959015787)
            ·
              refine ⟨6744892815151805938523681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496595210101203959015787 6744892815151805938523681)
              ·
                refine ⟨5058669611363854453892761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6744892815151805938523681 5058669611363854453892761)
                ·
                  refine ⟨3794002208522890840419571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058669611363854453892761 3794002208522890840419571)
                  ·
                    refine ⟨5691003312784336260629357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3794002208522890840419571 5691003312784336260629357)
                    ·
                      refine ⟨2134126242294126097736009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5691003312784336260629357 2134126242294126097736009)
                      ·
                        rfl

theorem cell23_4156196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_4156196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156196 prefixEnd_4156196 := by exact prefixLift 4156196
  have htrace : WordTrace (prefixWord ++ tailWord_4156196) baseStart_4156196 baseEnd_4156196 := by
    simpa [prefixWord, tailWord_4156196, baseEnd_4156196] using wordTrace_append hprefix tailTrace_4156196
  have hstable : (prefixWord ++ tailWord_4156196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156196).length < 2 ^ (prefixWord ++ tailWord_4156196).sum := by decide
  have hdescent : baseEnd_4156196 < baseStart_4156196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156248 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_4156248 : Nat := 118140960795 + 4156248 * 2 ^ 59
def prefixEnd_4156248 : Nat := 4983230072969 + 3 ^ 40 * 4156248 * 2
def baseEnd_4156248 : Nat := 2134152943288159894285769

theorem tailTrace_4156248 : CollatzResearch.WordTrace tailWord_4156248 prefixEnd_4156248 2134152943288159894285769 := by
  unfold tailWord_4156248
  simp only [CollatzResearch.WordTrace]
  refine ⟨75795409123315400745502699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101060545497753867660670265 75795409123315400745502699)
  ·
    refine ⟨113693113684973101118254049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75795409123315400745502699 113693113684973101118254049)
    ·
      refine ⟨85269835263729825838690537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113693113684973101118254049 85269835263729825838690537)
      ·
        refine ⟨63952376447797369379017903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85269835263729825838690537 63952376447797369379017903)
        ·
          refine ⟨95928564671696054068526855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63952376447797369379017903 95928564671696054068526855)
          ·
            refine ⟨143892847007544081102790283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95928564671696054068526855 143892847007544081102790283)
            ·
              refine ⟨215839270511316121654185425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143892847007544081102790283 215839270511316121654185425)
              ·
                refine ⟨161879452883487091240639069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215839270511316121654185425 161879452883487091240639069)
                ·
                  refine ⟨60704794831307659215239651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161879452883487091240639069 60704794831307659215239651)
                  ·
                    refine ⟨91057192246961488822859477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60704794831307659215239651 91057192246961488822859477)
                    ·
                      refine ⟨2134152943288159894285769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91057192246961488822859477 2134152943288159894285769)
                      ·
                        rfl

theorem cell23_4156248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_4156248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156248 prefixEnd_4156248 := by exact prefixLift 4156248
  have htrace : WordTrace (prefixWord ++ tailWord_4156248) baseStart_4156248 baseEnd_4156248 := by
    simpa [prefixWord, tailWord_4156248, baseEnd_4156248] using wordTrace_append hprefix tailTrace_4156248
  have hstable : (prefixWord ++ tailWord_4156248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156248).length < 2 ^ (prefixWord ++ tailWord_4156248).sum := by decide
  have hdescent : baseEnd_4156248 < baseStart_4156248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156255 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 2, 5]
def baseStart_4156255 : Nat := 118140960795 + 4156255 * 2 ^ 59
def prefixEnd_4156255 : Nat := 4983230072969 + 3 ^ 40 * 4156255 * 2
def baseEnd_4156255 : Nat := 711385512550913788966079

theorem tailTrace_4156255 : CollatzResearch.WordTrace tailWord_4156255 prefixEnd_4156255 711385512550913788966079 := by
  unfold tailWord_4156255
  simp only [CollatzResearch.WordTrace]
  refine ⟨151591073557605441686510219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101060715705070294457673479 151591073557605441686510219)
  ·
    refine ⟨227386610336408162529765329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151591073557605441686510219 227386610336408162529765329)
    ·
      refine ⟨170539957752306121897323997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227386610336408162529765329 170539957752306121897323997)
      ·
        refine ⟨63952484157114795711496499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170539957752306121897323997 63952484157114795711496499)
        ·
          refine ⟨95928726235672193567244749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63952484157114795711496499 95928726235672193567244749)
          ·
            refine ⟨35973272338377072587716781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95928726235672193567244749 35973272338377072587716781)
            ·
              refine ⟨13489977126891402220393793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35973272338377072587716781 13489977126891402220393793)
              ·
                refine ⟨10117482845168551665295345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13489977126891402220393793 10117482845168551665295345)
                ·
                  refine ⟨7588112133876413748971509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10117482845168551665295345 7588112133876413748971509)
                  ·
                    refine ⟨711385512550913788966079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7588112133876413748971509 711385512550913788966079)
                    ·
                      rfl

theorem cell23_4156255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_4156255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156255 prefixEnd_4156255 := by exact prefixLift 4156255
  have htrace : WordTrace (prefixWord ++ tailWord_4156255) baseStart_4156255 baseEnd_4156255 := by
    simpa [prefixWord, tailWord_4156255, baseEnd_4156255] using wordTrace_append hprefix tailTrace_4156255
  have hstable : (prefixWord ++ tailWord_4156255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156255).length < 2 ^ (prefixWord ++ tailWord_4156255).sum := by decide
  have hdescent : baseEnd_4156255 < baseStart_4156255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156259 : List Nat := [1, 1, 1, 5, 3, 2, 3, 2, 5]
def baseStart_4156259 : Nat := 118140960795 + 4156259 * 2 ^ 59
def prefixEnd_4156259 : Nat := 4983230072969 + 3 ^ 40 * 4156259 * 2
def baseEnd_4156259 : Nat := 237128732397262150138691

theorem tailTrace_4156259 : CollatzResearch.WordTrace tailWord_4156259 prefixEnd_4156259 237128732397262150138691 := by
  unfold tailWord_4156259
  simp only [CollatzResearch.WordTrace]
  refine ⟨151591219449590950369655831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101060812966393966913103887 151591219449590950369655831)
  ·
    refine ⟨227386829174386425554483747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151591219449590950369655831 227386829174386425554483747)
    ·
      refine ⟨341080243761579638331725621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227386829174386425554483747 341080243761579638331725621)
      ·
        refine ⟨31976272852648091093599277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 341080243761579638331725621 31976272852648091093599277)
        ·
          refine ⟨11991102319743034160099729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31976272852648091093599277 11991102319743034160099729)
          ·
            refine ⟨8993326739807275620074797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11991102319743034160099729 8993326739807275620074797)
            ·
              refine ⟨3372497527427728357528049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8993326739807275620074797 3372497527427728357528049)
              ·
                refine ⟨2529373145570796268146037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372497527427728357528049 2529373145570796268146037)
                ·
                  refine ⟨237128732397262150138691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2529373145570796268146037 237128732397262150138691)
                  ·
                    rfl

theorem cell23_4156259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 5].length) (baseStart_4156259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156259 prefixEnd_4156259 := by exact prefixLift 4156259
  have htrace : WordTrace (prefixWord ++ tailWord_4156259) baseStart_4156259 baseEnd_4156259 := by
    simpa [prefixWord, tailWord_4156259, baseEnd_4156259] using wordTrace_append hprefix tailTrace_4156259
  have hstable : (prefixWord ++ tailWord_4156259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156259).length < 2 ^ (prefixWord ++ tailWord_4156259).sum := by decide
  have hdescent : baseEnd_4156259 < baseStart_4156259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156270 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_4156270 : Nat := 118140960795 + 4156270 * 2 ^ 59
def prefixEnd_4156270 : Nat := 4983230072969 + 3 ^ 40 * 4156270 * 2
def baseEnd_4156270 : Nat := 2134164239862558808210669

theorem tailTrace_4156270 : CollatzResearch.WordTrace tailWord_4156270 prefixEnd_4156270 2134164239862558808210669 := by
  unfold tailWord_4156270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18948952581568887406038283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101061080435034066165537509 18948952581568887406038283)
  ·
    refine ⟨28423428872353331109057425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18948952581568887406038283 28423428872353331109057425)
    ·
      refine ⟨21317571654264998331793069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28423428872353331109057425 21317571654264998331793069)
      ·
        refine ⟨7994089370349374374422401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21317571654264998331793069 7994089370349374374422401)
        ·
          refine ⟨5995567027762030780816801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7994089370349374374422401 5995567027762030780816801)
          ·
            refine ⟨4496675270821523085612601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5995567027762030780816801 4496675270821523085612601)
            ·
              refine ⟨3372506453116142314209451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496675270821523085612601 3372506453116142314209451)
              ·
                refine ⟨5058759679674213471314177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372506453116142314209451 5058759679674213471314177)
                ·
                  refine ⟨3794069759755660103485633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058759679674213471314177 3794069759755660103485633)
                  ·
                    refine ⟨2845552319816745077614225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3794069759755660103485633 2845552319816745077614225)
                    ·
                      refine ⟨2134164239862558808210669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845552319816745077614225 2134164239862558808210669)
                      ·
                        rfl

theorem cell23_4156270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_4156270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156270 prefixEnd_4156270 := by exact prefixLift 4156270
  have htrace : WordTrace (prefixWord ++ tailWord_4156270) baseStart_4156270 baseEnd_4156270 := by
    simpa [prefixWord, tailWord_4156270, baseEnd_4156270] using wordTrace_append hprefix tailTrace_4156270
  have hstable : (prefixWord ++ tailWord_4156270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156270).length < 2 ^ (prefixWord ++ tailWord_4156270).sum := by decide
  have hdescent : baseEnd_4156270 < baseStart_4156270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156292 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_4156292 : Nat := 118140960795 + 4156292 * 2 ^ 59
def prefixEnd_4156292 : Nat := 4983230072969 + 3 ^ 40 * 4156292 * 2
def baseEnd_4156292 : Nat := 2134175536436957722135567

theorem tailTrace_4156292 : CollatzResearch.WordTrace tailWord_4156292 prefixEnd_4156292 2134175536436957722135567 := by
  unfold tailWord_4156292
  simp only [CollatzResearch.WordTrace]
  refine ⟨75796211529235698502803565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101061615372314264670404753 75796211529235698502803565)
  ·
    refine ⟨28423579323463386938551337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75796211529235698502803565 28423579323463386938551337)
    ·
      refine ⟨21317684492597540203913503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28423579323463386938551337 21317684492597540203913503)
      ·
        refine ⟨31976526738896310305870255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21317684492597540203913503 31976526738896310305870255)
        ·
          refine ⟨47964790108344465458805383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31976526738896310305870255 47964790108344465458805383)
          ·
            refine ⟨71947185162516698188208075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47964790108344465458805383 71947185162516698188208075)
            ·
              refine ⟨107920777743775047282312113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71947185162516698188208075 107920777743775047282312113)
              ·
                refine ⟨80940583307831285461734085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107920777743775047282312113 80940583307831285461734085)
                ·
                  refine ⟨15176359370218366024075141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80940583307831285461734085 15176359370218366024075141)
                  ·
                    refine ⟨2845567381915943629514089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15176359370218366024075141 2845567381915943629514089)
                    ·
                      refine ⟨2134175536436957722135567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845567381915943629514089 2134175536436957722135567)
                      ·
                        rfl

theorem cell23_4156292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_4156292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156292 prefixEnd_4156292 := by exact prefixLift 4156292
  have htrace : WordTrace (prefixWord ++ tailWord_4156292) baseStart_4156292 baseEnd_4156292 := by
    simpa [prefixWord, tailWord_4156292, baseEnd_4156292] using wordTrace_append hprefix tailTrace_4156292
  have hstable : (prefixWord ++ tailWord_4156292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156292).length < 2 ^ (prefixWord ++ tailWord_4156292).sum := by decide
  have hdescent : baseEnd_4156292 < baseStart_4156292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156310 : List Nat := [5, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_4156310 : Nat := 118140960795 + 4156310 * 2 ^ 59
def prefixEnd_4156310 : Nat := 4983230072969 + 3 ^ 40 * 4156310 * 2
def baseEnd_4156310 : Nat := 237131642120970961301165

theorem tailTrace_4156310 : CollatzResearch.WordTrace tailWord_4156310 prefixEnd_4156310 237131642120970961301165 := by
  unfold tailWord_4156310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9474567473275386629985149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101062053048270790719841589 9474567473275386629985149)
  ·
    refine ⟨3552962802478269986244431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9474567473275386629985149 3552962802478269986244431)
    ·
      refine ⟨5329444203717404979366647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552962802478269986244431 5329444203717404979366647)
      ·
        refine ⟨7994166305576107469049971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329444203717404979366647 7994166305576107469049971)
        ·
          refine ⟨11991249458364161203574957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994166305576107469049971 11991249458364161203574957)
          ·
            refine ⟨4496718546886560451340609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11991249458364161203574957 4496718546886560451340609)
            ·
              refine ⟨3372538910164920338505457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496718546886560451340609 3372538910164920338505457)
              ·
                refine ⟨2529404182623690253879093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372538910164920338505457 2529404182623690253879093)
                ·
                  refine ⟨237131642120970961301165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2529404182623690253879093 237131642120970961301165)
                  ·
                    rfl

theorem cell23_4156310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_4156310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156310 prefixEnd_4156310 := by exact prefixLift 4156310
  have htrace : WordTrace (prefixWord ++ tailWord_4156310) baseStart_4156310 baseEnd_4156310 := by
    simpa [prefixWord, tailWord_4156310, baseEnd_4156310] using wordTrace_append hprefix tailTrace_4156310
  have hstable : (prefixWord ++ tailWord_4156310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156310).length < 2 ^ (prefixWord ++ tailWord_4156310).sum := by decide
  have hdescent : baseEnd_4156310 < baseStart_4156310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156325 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 4, 5, 3]
def baseStart_4156325 : Nat := 118140960795 + 4156325 * 2 ^ 59
def prefixEnd_4156325 : Nat := 4983230072969 + 3 ^ 40 * 4156325 * 2
def baseEnd_4156325 : Nat := 2134192481298556093022915

theorem tailTrace_4156325 : CollatzResearch.WordTrace tailWord_4156325 prefixEnd_4156325 2134192481298556093022915 := by
  unfold tailWord_4156325
  simp only [CollatzResearch.WordTrace]
  refine ⟨151593626667351843641558429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101062417778234562427705619 151593626667351843641558429)
  ·
    refine ⟨56847610000256941365584411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151593626667351843641558429 56847610000256941365584411)
    ·
      refine ⟨85271415000385412048376617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56847610000256941365584411 85271415000385412048376617)
      ·
        refine ⟨63953561250289059036282463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85271415000385412048376617 63953561250289059036282463)
        ·
          refine ⟨95930341875433588554423695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63953561250289059036282463 95930341875433588554423695)
          ·
            refine ⟨143895512813150382831635543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95930341875433588554423695 143895512813150382831635543)
            ·
              refine ⟨215843269219725574247453315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143895512813150382831635543 215843269219725574247453315)
              ·
                refine ⟨323764903829588361371179973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215843269219725574247453315 323764903829588361371179973)
                ·
                  refine ⟨60705919468047817757096245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323764903829588361371179973 60705919468047817757096245)
                  ·
                    refine ⟨5691179950129482914727773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60705919468047817757096245 5691179950129482914727773)
                    ·
                      refine ⟨2134192481298556093022915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5691179950129482914727773 2134192481298556093022915)
                      ·
                        rfl

theorem cell23_4156325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_4156325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156325 prefixEnd_4156325 := by exact prefixLift 4156325
  have htrace : WordTrace (prefixWord ++ tailWord_4156325) baseStart_4156325 baseEnd_4156325 := by
    simpa [prefixWord, tailWord_4156325, baseEnd_4156325] using wordTrace_append hprefix tailTrace_4156325
  have hstable : (prefixWord ++ tailWord_4156325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156325).length < 2 ^ (prefixWord ++ tailWord_4156325).sum := by decide
  have hdescent : baseEnd_4156325 < baseStart_4156325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156376 : List Nat := [2, 1, 2, 2, 2, 3, 2, 4, 1, 1, 3]
def baseStart_4156376 : Nat := 118140960795 + 4156376 * 2 ^ 59
def prefixEnd_4156376 : Nat := 4983230072969 + 3 ^ 40 * 4156376 * 2
def baseEnd_4156376 : Nat := 2134218668811935393485181

theorem tailTrace_4156376 : CollatzResearch.WordTrace tailWord_4156376 prefixEnd_4156376 2134218668811935393485181 := by
  unfold tailWord_4156376
  simp only [CollatzResearch.WordTrace]
  refine ⟨75797743395083539675832491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101063657860111386234443321 75797743395083539675832491)
  ·
    refine ⟨113696615092625309513748737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75797743395083539675832491 113696615092625309513748737)
    ·
      refine ⟨85272461319468982135311553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113696615092625309513748737 85272461319468982135311553)
      ·
        refine ⟨63954345989601736601483665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85272461319468982135311553 63954345989601736601483665)
        ·
          refine ⟨47965759492201302451112749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63954345989601736601483665 47965759492201302451112749)
          ·
            refine ⟨17987159809575488419167281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47965759492201302451112749 17987159809575488419167281)
            ·
              refine ⟨13490369857181616314375461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17987159809575488419167281 13490369857181616314375461)
              ·
                refine ⟨2529444348221553058945399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13490369857181616314375461 2529444348221553058945399)
                ·
                  refine ⟨3794166522332329588418099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529444348221553058945399 3794166522332329588418099)
                  ·
                    refine ⟨5691249783498494382627149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3794166522332329588418099 5691249783498494382627149)
                    ·
                      refine ⟨2134218668811935393485181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5691249783498494382627149 2134218668811935393485181)
                      ·
                        rfl

theorem cell23_4156376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_4156376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156376 prefixEnd_4156376 := by exact prefixLift 4156376
  have htrace : WordTrace (prefixWord ++ tailWord_4156376) baseStart_4156376 baseEnd_4156376 := by
    simpa [prefixWord, tailWord_4156376, baseEnd_4156376] using wordTrace_append hprefix tailTrace_4156376
  have hstable : (prefixWord ++ tailWord_4156376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156376).length < 2 ^ (prefixWord ++ tailWord_4156376).sum := by decide
  have hdescent : baseEnd_4156376 < baseStart_4156376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156386 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4156386 : Nat := 118140960795 + 4156386 * 2 ^ 59
def prefixEnd_4156386 : Nat := 4983230072969 + 3 ^ 40 * 4156386 * 2
def baseEnd_4156386 : Nat := 2134223803618480354360135

theorem tailTrace_4156386 : CollatzResearch.WordTrace tailWord_4156386 prefixEnd_4156386 2134223803618480354360135 := by
  unfold tailWord_4156386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37898962880032712764882253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101063901013420567373019341 37898962880032712764882253)
  ·
    refine ⟨14212111080012267286830845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37898962880032712764882253 14212111080012267286830845)
    ·
      refine ⟨5329541655004600232561567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14212111080012267286830845 5329541655004600232561567)
      ·
        refine ⟨7994312482506900348842351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329541655004600232561567 7994312482506900348842351)
        ·
          refine ⟨11991468723760350523263527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994312482506900348842351 11991468723760350523263527)
          ·
            refine ⟨17987203085640525784895291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11991468723760350523263527 17987203085640525784895291)
            ·
              refine ⟨26980804628460788677342937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17987203085640525784895291 26980804628460788677342937)
              ·
                refine ⟨20235603471345591508007203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26980804628460788677342937 20235603471345591508007203)
                ·
                  refine ⟨30353405207018387262010805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20235603471345591508007203 30353405207018387262010805)
                  ·
                    refine ⟨2845631738157973805813513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30353405207018387262010805 2845631738157973805813513)
                    ·
                      refine ⟨2134223803618480354360135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845631738157973805813513 2134223803618480354360135)
                      ·
                        rfl

theorem cell23_4156386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4156386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156386 prefixEnd_4156386 := by exact prefixLift 4156386
  have htrace : WordTrace (prefixWord ++ tailWord_4156386) baseStart_4156386 baseEnd_4156386 := by
    simpa [prefixWord, tailWord_4156386, baseEnd_4156386] using wordTrace_append hprefix tailTrace_4156386
  have hstable : (prefixWord ++ tailWord_4156386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156386).length < 2 ^ (prefixWord ++ tailWord_4156386).sum := by decide
  have hdescent : baseEnd_4156386 < baseStart_4156386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156392 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 1, 6]
def baseStart_4156392 : Nat := 118140960795 + 4156392 * 2 ^ 59
def prefixEnd_4156392 : Nat := 4983230072969 + 3 ^ 40 * 4156392 * 2
def baseEnd_4156392 : Nat := 711408961500802443628369

theorem tailTrace_4156392 : CollatzResearch.WordTrace tailWord_4156392 prefixEnd_4156392 711408961500802443628369 := by
  unfold tailWord_4156392
  simp only [CollatzResearch.WordTrace]
  refine ⟨75798035179054557042123715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101064046905406076056164953 75798035179054557042123715)
  ·
    refine ⟨113697052768581835563185573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75798035179054557042123715 113697052768581835563185573)
    ·
      refine ⟨21318197394109094168097295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113697052768581835563185573 21318197394109094168097295)
      ·
        refine ⟨31977296091163641252145943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21318197394109094168097295 31977296091163641252145943)
        ·
          refine ⟨47965944136745461878218915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31977296091163641252145943 47965944136745461878218915)
          ·
            refine ⟨71948916205118192817328373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47965944136745461878218915 71948916205118192817328373)
            ·
              refine ⟨6745210894229830576624535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71948916205118192817328373 6745210894229830576624535)
              ·
                refine ⟨10117816341344745864936803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6745210894229830576624535 10117816341344745864936803)
                ·
                  refine ⟨15176724512017118797405205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10117816341344745864936803 15176724512017118797405205)
                  ·
                    refine ⟨711408961500802443628369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15176724512017118797405205 711408961500802443628369)
                    ·
                      rfl

theorem cell23_4156392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_4156392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156392 prefixEnd_4156392 := by exact prefixLift 4156392
  have htrace : WordTrace (prefixWord ++ tailWord_4156392) baseStart_4156392 baseEnd_4156392 := by
    simpa [prefixWord, tailWord_4156392, baseEnd_4156392] using wordTrace_append hprefix tailTrace_4156392
  have hstable : (prefixWord ++ tailWord_4156392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156392).length < 2 ^ (prefixWord ++ tailWord_4156392).sum := by decide
  have hdescent : baseEnd_4156392 < baseStart_4156392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156399 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 4]
def baseStart_4156399 : Nat := 118140960795 + 4156399 * 2 ^ 59
def prefixEnd_4156399 : Nat := 4983230072969 + 3 ^ 40 * 4156399 * 2
def baseEnd_4156399 : Nat := 2134230478866988803497575

theorem tailTrace_4156399 : CollatzResearch.WordTrace tailWord_4156399 prefixEnd_4156399 2134230478866988803497575 := by
  unfold tailWord_4156399
  simp only [CollatzResearch.WordTrace]
  refine ⟨151596325669083754279752251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101064217112722502853168167 151596325669083754279752251)
  ·
    refine ⟨227394488503625631419628377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151596325669083754279752251 227394488503625631419628377)
    ·
      refine ⟨170545866377719223564721283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227394488503625631419628377 170545866377719223564721283)
      ·
        refine ⟨255818799566578835347081925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170545866377719223564721283 255818799566578835347081925)
        ·
          refine ⟨47966024918733531627577861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255818799566578835347081925 47966024918733531627577861)
          ·
            refine ⟨8993629672262537180170849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47966024918733531627577861 8993629672262537180170849)
            ·
              refine ⟨6745222254196902885128137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8993629672262537180170849 6745222254196902885128137)
              ·
                refine ⟨5058916690647677163846103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6745222254196902885128137 5058916690647677163846103)
                ·
                  refine ⟨7588375035971515745769155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058916690647677163846103 7588375035971515745769155)
                  ·
                    refine ⟨11382562553957273618653733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588375035971515745769155 11382562553957273618653733)
                    ·
                      refine ⟨2134230478866988803497575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11382562553957273618653733 2134230478866988803497575)
                      ·
                        rfl

theorem cell23_4156399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 4].length) (baseStart_4156399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156399 prefixEnd_4156399 := by exact prefixLift 4156399
  have htrace : WordTrace (prefixWord ++ tailWord_4156399) baseStart_4156399 baseEnd_4156399 := by
    simpa [prefixWord, tailWord_4156399, baseEnd_4156399] using wordTrace_append hprefix tailTrace_4156399
  have hstable : (prefixWord ++ tailWord_4156399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156399).length < 2 ^ (prefixWord ++ tailWord_4156399).sum := by decide
  have hdescent : baseEnd_4156399 < baseStart_4156399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156404 : List Nat := [2, 6, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4156404 : Nat := 118140960795 + 4156404 * 2 ^ 59
def prefixEnd_4156404 : Nat := 4983230072969 + 3 ^ 40 * 4156404 * 2
def baseEnd_4156404 : Nat := 711411015423420427978351

theorem tailTrace_4156404 : CollatzResearch.WordTrace tailWord_4156404 prefixEnd_4156404 711411015423420427978351 := by
  unfold tailWord_4156404
  simp only [CollatzResearch.WordTrace]
  refine ⟨75798254017032820066842133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101064338689377093422456177 75798254017032820066842133)
  ·
    refine ⟨3553043157048413440633225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75798254017032820066842133 3553043157048413440633225)
    ·
      refine ⟨2664782367786310080474919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3553043157048413440633225 2664782367786310080474919)
      ·
        refine ⟨3997173551679465120712379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664782367786310080474919 3997173551679465120712379)
        ·
          refine ⟨5995760327519197681068569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997173551679465120712379 5995760327519197681068569)
          ·
            refine ⟨4496820245639398260801427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5995760327519197681068569 4496820245639398260801427)
            ·
              refine ⟨6745230368459097391202141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496820245639398260801427 6745230368459097391202141)
              ·
                refine ⟨2529461388172161521700803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6745230368459097391202141 2529461388172161521700803)
                ·
                  refine ⟨3794192082258242282551205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529461388172161521700803 3794192082258242282551205)
                  ·
                    refine ⟨711411015423420427978351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3794192082258242282551205 711411015423420427978351)
                    ·
                      rfl

theorem cell23_4156404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4156404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156404 prefixEnd_4156404 := by exact prefixLift 4156404
  have htrace : WordTrace (prefixWord ++ tailWord_4156404) baseStart_4156404 baseEnd_4156404 := by
    simpa [prefixWord, tailWord_4156404, baseEnd_4156404] using wordTrace_append hprefix tailTrace_4156404
  have hstable : (prefixWord ++ tailWord_4156404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156404).length < 2 ^ (prefixWord ++ tailWord_4156404).sum := by decide
  have hdescent : baseEnd_4156404 < baseStart_4156404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156435 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 2, 7]
def baseStart_4156435 : Nat := 118140960795 + 4156435 * 2 ^ 59
def prefixEnd_4156435 : Nat := 4983230072969 + 3 ^ 40 * 4156435 * 2
def baseEnd_4156435 : Nat := 711416321390183554215803

theorem tailTrace_4156435 : CollatzResearch.WordTrace tailWord_4156435 prefixEnd_4156435 711416321390183554215803 := by
  unfold tailWord_4156435
  simp only [CollatzResearch.WordTrace]
  refine ⟨151597638696953332428062759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101065092464635554952041839 151597638696953332428062759)
  ·
    refine ⟨227396458045429998642094139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151597638696953332428062759 227396458045429998642094139)
    ·
      refine ⟨341094687068144997963141209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227396458045429998642094139 341094687068144997963141209)
      ·
        refine ⟨255821015301108748472355907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341094687068144997963141209 255821015301108748472355907)
        ·
          refine ⟨383731522951663122708533861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255821015301108748472355907 383731522951663122708533861)
          ·
            refine ⟨71949660553436835507850099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383731522951663122708533861 71949660553436835507850099)
            ·
              refine ⟨107924490830155253261775149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71949660553436835507850099 107924490830155253261775149)
              ·
                refine ⟨40471684061308219973165681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107924490830155253261775149 40471684061308219973165681)
                ·
                  refine ⟨30353763045981164979874261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40471684061308219973165681 30353763045981164979874261)
                  ·
                    refine ⟨711416321390183554215803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30353763045981164979874261 711416321390183554215803)
                    ·
                      rfl

theorem cell23_4156435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 7].length) (baseStart_4156435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156435 prefixEnd_4156435 := by exact prefixLift 4156435
  have htrace : WordTrace (prefixWord ++ tailWord_4156435) baseStart_4156435 baseEnd_4156435 := by
    simpa [prefixWord, tailWord_4156435, baseEnd_4156435] using wordTrace_append hprefix tailTrace_4156435
  have hstable : (prefixWord ++ tailWord_4156435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156435).length < 2 ^ (prefixWord ++ tailWord_4156435).sum := by decide
  have hdescent : baseEnd_4156435 < baseStart_4156435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156459 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 3, 3, 2]
def baseStart_4156459 : Nat := 118140960795 + 4156459 * 2 ^ 59
def prefixEnd_4156459 : Nat := 4983230072969 + 3 ^ 40 * 4156459 * 2
def baseEnd_4156459 : Nat := 2134261287706258568747299

theorem tailTrace_4156459 : CollatzResearch.WordTrace tailWord_4156459 prefixEnd_4156459 2134261287706258568747299 := by
  unfold tailWord_4156459
  simp only [CollatzResearch.WordTrace]
  refine ⟨151598514048866384526936431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101065676032577589684624287 151598514048866384526936431)
  ·
    refine ⟨227397771073299576790404647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151598514048866384526936431 227397771073299576790404647)
    ·
      refine ⟨341096656609949365185606971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227397771073299576790404647 341096656609949365185606971)
      ·
        refine ⟨511644984914924047778410457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341096656609949365185606971 511644984914924047778410457)
        ·
          refine ⟨383733738686193035833807843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511644984914924047778410457 383733738686193035833807843)
          ·
            refine ⟨575600608029289553750711765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383733738686193035833807843 575600608029289553750711765)
            ·
              refine ⟨13490639250686473916032307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 575600608029289553750711765 13490639250686473916032307)
              ·
                refine ⟨20235958876029710874048461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13490639250686473916032307 20235958876029710874048461)
                ·
                  refine ⟨7588484578511141577768173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20235958876029710874048461 7588484578511141577768173)
                  ·
                    refine ⟨2845681716941678091663065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7588484578511141577768173 2845681716941678091663065)
                    ·
                      refine ⟨2134261287706258568747299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845681716941678091663065 2134261287706258568747299)
                      ·
                        rfl

theorem cell23_4156459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 3, 2].length) (baseStart_4156459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156459 prefixEnd_4156459 := by exact prefixLift 4156459
  have htrace : WordTrace (prefixWord ++ tailWord_4156459) baseStart_4156459 baseEnd_4156459 := by
    simpa [prefixWord, tailWord_4156459, baseEnd_4156459] using wordTrace_append hprefix tailTrace_4156459
  have hstable : (prefixWord ++ tailWord_4156459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156459).length < 2 ^ (prefixWord ++ tailWord_4156459).sum := by decide
  have hdescent : baseEnd_4156459 < baseStart_4156459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156510 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_4156510 : Nat := 118140960795 + 4156510 * 2 ^ 59
def prefixEnd_4156510 : Nat := 4983230072969 + 3 ^ 40 * 4156510 * 2
def baseEnd_4156510 : Nat := 2134287475219637869209565

theorem tailTrace_4156510 : CollatzResearch.WordTrace tailWord_4156510 prefixEnd_4156510 2134287475219637869209565 := by
  unfold tailWord_4156510
  simp only [CollatzResearch.WordTrace]
  refine ⟨18950046771460202529630373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101066916114454413491361989 18950046771460202529630373)
  ·
    refine ⟨3553133769648787974305695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18950046771460202529630373 3553133769648787974305695)
    ·
      refine ⟨5329700654473181961458543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3553133769648787974305695 5329700654473181961458543)
      ·
        refine ⟨7994550981709772942187815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329700654473181961458543 7994550981709772942187815)
        ·
          refine ⟨11991826472564659413281723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994550981709772942187815 11991826472564659413281723)
          ·
            refine ⟨17987739708846989119922585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11991826472564659413281723 17987739708846989119922585)
            ·
              refine ⟨13490804781635241839941939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17987739708846989119922585 13490804781635241839941939)
              ·
                refine ⟨20236207172452862759912909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13490804781635241839941939 20236207172452862759912909)
                ·
                  refine ⟨7588577689669823534967341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20236207172452862759912909 7588577689669823534967341)
                  ·
                    refine ⟨2845716633626183825612753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7588577689669823534967341 2845716633626183825612753)
                    ·
                      refine ⟨2134287475219637869209565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845716633626183825612753 2134287475219637869209565)
                      ·
                        rfl

theorem cell23_4156510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_4156510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156510 prefixEnd_4156510 := by exact prefixLift 4156510
  have htrace : WordTrace (prefixWord ++ tailWord_4156510) baseStart_4156510 baseEnd_4156510 := by
    simpa [prefixWord, tailWord_4156510, baseEnd_4156510] using wordTrace_append hprefix tailTrace_4156510
  have hstable : (prefixWord ++ tailWord_4156510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156510).length < 2 ^ (prefixWord ++ tailWord_4156510).sum := by decide
  have hdescent : baseEnd_4156510 < baseStart_4156510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156512 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 7]
def baseStart_4156512 : Nat := 118140960795 + 4156512 * 2 ^ 59
def prefixEnd_4156512 : Nat := 4983230072969 + 3 ^ 40 * 4156512 * 2
def baseEnd_4156512 : Nat := 237143166908994095709395

theorem tailTrace_4156512 : CollatzResearch.WordTrace tailWord_4156512 prefixEnd_4156512 237143166908994095709395 := by
  unfold tailWord_4156512
  simp only [CollatzResearch.WordTrace]
  refine ⟨75800223558837187289307895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101066964745116249719077193 75800223558837187289307895)
  ·
    refine ⟨113700335338255780933961843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75800223558837187289307895 113700335338255780933961843)
    ·
      refine ⟨170550503007383671400942765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113700335338255780933961843 170550503007383671400942765)
      ·
        refine ⟨63956438627768876775353537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170550503007383671400942765 63956438627768876775353537)
        ·
          refine ⟨47967328970826657581515153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63956438627768876775353537 47967328970826657581515153)
          ·
            refine ⟨35975496728119993186136365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47967328970826657581515153 35975496728119993186136365)
            ·
              refine ⟨13490811273044997444801137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35975496728119993186136365 13490811273044997444801137)
              ·
                refine ⟨10118108454783748083600853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13490811273044997444801137 10118108454783748083600853)
                ·
                  refine ⟨237143166908994095709395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10118108454783748083600853 237143166908994095709395)
                  ·
                    rfl

theorem cell23_4156512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 7].length) (baseStart_4156512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156512 prefixEnd_4156512 := by exact prefixLift 4156512
  have htrace : WordTrace (prefixWord ++ tailWord_4156512) baseStart_4156512 baseEnd_4156512 := by
    simpa [prefixWord, tailWord_4156512, baseEnd_4156512] using wordTrace_append hprefix tailTrace_4156512
  have hstable : (prefixWord ++ tailWord_4156512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156512).length < 2 ^ (prefixWord ++ tailWord_4156512).sum := by decide
  have hdescent : baseEnd_4156512 < baseStart_4156512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156579 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 1, 6, 2]
def baseStart_4156579 : Nat := 118140960795 + 4156579 * 2 ^ 59
def prefixEnd_4156579 : Nat := 4983230072969 + 3 ^ 40 * 4156579 * 2
def baseEnd_4156579 : Nat := 2134322905384798099246747

theorem tailTrace_4156579 : CollatzResearch.WordTrace tailWord_4156579 prefixEnd_4156579 2134322905384798099246747 := by
  unfold tailWord_4156579
  simp only [CollatzResearch.WordTrace]
  refine ⟨151602890808431645021304791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101068593872287763347536527 151602890808431645021304791)
  ·
    refine ⟨227404336212647467531957187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151602890808431645021304791 227404336212647467531957187)
    ·
      refine ⟨341106504318971201297935781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227404336212647467531957187 341106504318971201297935781)
      ·
        refine ⟨63957469559807100243362959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341106504318971201297935781 63957469559807100243362959)
        ·
          refine ⟨95936204339710650365044439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63957469559807100243362959 95936204339710650365044439)
          ·
            refine ⟨143904306509565975547566659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95936204339710650365044439 143904306509565975547566659)
            ·
              refine ⟨215856459764348963321349989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143904306509565975547566659 215856459764348963321349989)
              ·
                refine ⟨40473086205815430622753123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215856459764348963321349989 40473086205815430622753123)
                ·
                  refine ⟨60709629308723145934129685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40473086205815430622753123 60709629308723145934129685)
                  ·
                    refine ⟨2845763873846397465662329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60709629308723145934129685 2845763873846397465662329)
                    ·
                      refine ⟨2134322905384798099246747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845763873846397465662329 2134322905384798099246747)
                      ·
                        rfl

theorem cell23_4156579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_4156579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156579 prefixEnd_4156579 := by exact prefixLift 4156579
  have htrace : WordTrace (prefixWord ++ tailWord_4156579) baseStart_4156579 baseEnd_4156579 := by
    simpa [prefixWord, tailWord_4156579, baseEnd_4156579] using wordTrace_append hprefix tailTrace_4156579
  have hstable : (prefixWord ++ tailWord_4156579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156579).length < 2 ^ (prefixWord ++ tailWord_4156579).sum := by decide
  have hdescent : baseEnd_4156579 < baseStart_4156579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156592 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_4156592 : Nat := 118140960795 + 4156592 * 2 ^ 59
def prefixEnd_4156592 : Nat := 4983230072969 + 3 ^ 40 * 4156592 * 2
def baseEnd_4156592 : Nat := 2134329580633306548384187

theorem tailTrace_4156592 : CollatzResearch.WordTrace tailWord_4156592 prefixEnd_4156592 2134329580633306548384187 := by
  unfold tailWord_4156592
  simp only [CollatzResearch.WordTrace]
  refine ⟨75801682478692274120764015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101068909971589698827685353 75801682478692274120764015)
  ·
    refine ⟨113702523718038411181146023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75801682478692274120764015 113702523718038411181146023)
    ·
      refine ⟨170553785577057616771719035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113702523718038411181146023 170553785577057616771719035)
      ·
        refine ⟨255830678365586425157578553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170553785577057616771719035 255830678365586425157578553)
        ·
          refine ⟨191873008774189818868183915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255830678365586425157578553 191873008774189818868183915)
          ·
            refine ⟨287809513161284728302275873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191873008774189818868183915 287809513161284728302275873)
            ·
              refine ⟨215857134870963546226706905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287809513161284728302275873 215857134870963546226706905)
              ·
                refine ⟨161892851153222659670030179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215857134870963546226706905 161892851153222659670030179)
                ·
                  refine ⟨242839276729833989505045269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161892851153222659670030179 242839276729833989505045269)
                  ·
                    refine ⟨11383091096710968258048997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 242839276729833989505045269 11383091096710968258048997)
                    ·
                      refine ⟨2134329580633306548384187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11383091096710968258048997 2134329580633306548384187)
                      ·
                        rfl

theorem cell23_4156592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_4156592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156592 prefixEnd_4156592 := by exact prefixLift 4156592
  have htrace : WordTrace (prefixWord ++ tailWord_4156592) baseStart_4156592 baseEnd_4156592 := by
    simpa [prefixWord, tailWord_4156592, baseEnd_4156592] using wordTrace_append hprefix tailTrace_4156592
  have hstable : (prefixWord ++ tailWord_4156592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156592).length < 2 ^ (prefixWord ++ tailWord_4156592).sum := by decide
  have hdescent : baseEnd_4156592 < baseStart_4156592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
