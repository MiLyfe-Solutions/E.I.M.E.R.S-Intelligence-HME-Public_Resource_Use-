import V185TrunkScan23Chunk0006

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_40482 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_40482 : Nat := 118140960795 + 40482 * 2 ^ 59
def prefixEnd_40482 : Nat := 4983230072969 + 3 ^ 40 * 40482 * 2
def baseEnd_40482 : Nat := 20786723855415847688833

theorem tailTrace_40482 : CollatzResearch.WordTrace tailWord_40482 prefixEnd_40482 20786723855415847688833 := by
  unfold tailWord_40482
  simp only [CollatzResearch.WordTrace]
  refine ⟨369124959837025655068925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 984333226232068413517133 369124959837025655068925)
  ·
    refine ⟨138421859938884620650847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 369124959837025655068925 138421859938884620650847)
    ·
      refine ⟨207632789908326930976271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138421859938884620650847 207632789908326930976271)
      ·
        refine ⟨311449184862490396464407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207632789908326930976271 311449184862490396464407)
        ·
          refine ⟨467173777293735594696611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311449184862490396464407 467173777293735594696611)
          ·
            refine ⟨700760665940603392044917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467173777293735594696611 700760665940603392044917)
            ·
              refine ⟨65696312431931568004211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 700760665940603392044917 65696312431931568004211)
              ·
                refine ⟨98544468647897352006317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65696312431931568004211 98544468647897352006317)
                ·
                  refine ⟨36954175742961507002369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98544468647897352006317 36954175742961507002369)
                  ·
                    refine ⟨27715631807221130251777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36954175742961507002369 27715631807221130251777)
                    ·
                      refine ⟨20786723855415847688833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 27715631807221130251777 20786723855415847688833)
                      ·
                        rfl

theorem cell23_40482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_40482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40482 prefixEnd_40482 := by exact prefixLift 40482
  have htrace : WordTrace (prefixWord ++ tailWord_40482) baseStart_40482 baseEnd_40482 := by
    simpa [prefixWord, tailWord_40482, baseEnd_40482] using wordTrace_append hprefix tailTrace_40482
  have hstable : (prefixWord ++ tailWord_40482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40482).length < 2 ^ (prefixWord ++ tailWord_40482).sum := by decide
  have hdescent : baseEnd_40482 < baseStart_40482 := by decide
  rcases family_descends (prefixWord ++ tailWord_40482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40498 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_40498 : Nat := 118140960795 + 40498 * 2 ^ 59
def prefixEnd_40498 : Nat := 4983230072969 + 3 ^ 40 * 40498 * 2
def baseEnd_40498 : Nat := 20794939545887785088759

theorem tailTrace_40498 : CollatzResearch.WordTrace tailWord_40498 prefixEnd_40498 20794939545887785088759 := by
  unfold tailWord_40498
  simp only [CollatzResearch.WordTrace]
  refine ⟨369270851822534338214537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 984722271526758235238765 369270851822534338214537)
  ·
    refine ⟨276953138866900753660903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 369270851822534338214537 276953138866900753660903)
    ·
      refine ⟨415429708300351130491355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276953138866900753660903 415429708300351130491355)
      ·
        refine ⟨623144562450526695737033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415429708300351130491355 623144562450526695737033)
        ·
          refine ⟨467358421837895021802775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623144562450526695737033 467358421837895021802775)
          ·
            refine ⟨701037632756842532704163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467358421837895021802775 701037632756842532704163)
            ·
              refine ⟨1051556449135263799056245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701037632756842532704163 1051556449135263799056245)
              ·
                refine ⟨98583417106430981161523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1051556449135263799056245 98583417106430981161523)
                ·
                  refine ⟨147875125659646471742285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98583417106430981161523 147875125659646471742285)
                  ·
                    refine ⟨55453172122367426903357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147875125659646471742285 55453172122367426903357)
                    ·
                      refine ⟨20794939545887785088759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 55453172122367426903357 20794939545887785088759)
                      ·
                        rfl

theorem cell23_40498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_40498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40498 prefixEnd_40498 := by exact prefixLift 40498
  have htrace : WordTrace (prefixWord ++ tailWord_40498) baseStart_40498 baseEnd_40498 := by
    simpa [prefixWord, tailWord_40498, baseEnd_40498] using wordTrace_append hprefix tailTrace_40498
  have hstable : (prefixWord ++ tailWord_40498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40498).length < 2 ^ (prefixWord ++ tailWord_40498).sum := by decide
  have hdescent : baseEnd_40498 < baseStart_40498 := by decide
  rcases family_descends (prefixWord ++ tailWord_40498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40502 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_40502 : Nat := 118140960795 + 40502 * 2 ^ 59
def prefixEnd_40502 : Nat := 4983230072969 + 3 ^ 40 * 40502 * 2
def baseEnd_40502 : Nat := 20796993468505769438741

theorem tailTrace_40502 : CollatzResearch.WordTrace tailWord_40502 prefixEnd_40502 20796993468505769438741 := by
  unfold tailWord_40502
  simp only [CollatzResearch.WordTrace]
  refine ⟨92326831204727877250235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 984819532850430690669173 92326831204727877250235)
  ·
    refine ⟨138490246807091815875353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92326831204727877250235 138490246807091815875353)
    ·
      refine ⟨103867685105318861906515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138490246807091815875353 103867685105318861906515)
      ·
        refine ⟨155801527657978292859773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103867685105318861906515 155801527657978292859773)
        ·
          refine ⟨58425572871741859822415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155801527657978292859773 58425572871741859822415)
          ·
            refine ⟨87638359307612789733623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58425572871741859822415 87638359307612789733623)
            ·
              refine ⟨131457538961419184600435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87638359307612789733623 131457538961419184600435)
              ·
                refine ⟨197186308442128776900653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131457538961419184600435 197186308442128776900653)
                ·
                  refine ⟨73944865665798291337745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197186308442128776900653 73944865665798291337745)
                  ·
                    refine ⟨55458649249348718503309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73944865665798291337745 55458649249348718503309)
                    ·
                      refine ⟨20796993468505769438741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 55458649249348718503309 20796993468505769438741)
                      ·
                        rfl

theorem cell23_40502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_40502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40502 prefixEnd_40502 := by exact prefixLift 40502
  have htrace : WordTrace (prefixWord ++ tailWord_40502) baseStart_40502 baseEnd_40502 := by
    simpa [prefixWord, tailWord_40502, baseEnd_40502] using wordTrace_append hprefix tailTrace_40502
  have hstable : (prefixWord ++ tailWord_40502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40502).length < 2 ^ (prefixWord ++ tailWord_40502).sum := by decide
  have hdescent : baseEnd_40502 < baseStart_40502 := by decide
  rcases family_descends (prefixWord ++ tailWord_40502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40521 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_40521 : Nat := 118140960795 + 40521 * 2 ^ 59
def prefixEnd_40521 : Nat := 4983230072969 + 3 ^ 40 * 40521 * 2
def baseEnd_40521 : Nat := 20806749600941195101153

theorem tailTrace_40521 : CollatzResearch.WordTrace tailWord_40521 prefixEnd_40521 20806749600941195101153 := by
  unfold tailWord_40521
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477922286206812280945417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 985281524137874853963611 1477922286206812280945417)
  ·
    refine ⟨1108441714655109210709063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1477922286206812280945417 1108441714655109210709063)
    ·
      refine ⟨1662662571982663816063595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108441714655109210709063 1662662571982663816063595)
      ·
        refine ⟨2493993857973995724095393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1662662571982663816063595 2493993857973995724095393)
        ·
          refine ⟨1870495393480496793071545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2493993857973995724095393 1870495393480496793071545)
          ·
            refine ⟨1402871545110372594803659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1870495393480496793071545 1402871545110372594803659)
            ·
              refine ⟨2104307317665558892205489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402871545110372594803659 2104307317665558892205489)
              ·
                refine ⟨1578230488249169169154117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2104307317665558892205489 1578230488249169169154117)
                ·
                  refine ⟨295918216546719219216397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578230488249169169154117 295918216546719219216397)
                  ·
                    refine ⟨110969331205019707206149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295918216546719219216397 110969331205019707206149)
                    ·
                      refine ⟨20806749600941195101153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 110969331205019707206149 20806749600941195101153)
                      ·
                        rfl

theorem cell23_40521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_40521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40521 prefixEnd_40521 := by exact prefixLift 40521
  have htrace : WordTrace (prefixWord ++ tailWord_40521) baseStart_40521 baseEnd_40521 := by
    simpa [prefixWord, tailWord_40521, baseEnd_40521] using wordTrace_append hprefix tailTrace_40521
  have hstable : (prefixWord ++ tailWord_40521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40521).length < 2 ^ (prefixWord ++ tailWord_40521).sum := by decide
  have hdescent : baseEnd_40521 < baseStart_40521 := by decide
  rcases family_descends (prefixWord ++ tailWord_40521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40532 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_40532 : Nat := 118140960795 + 40532 * 2 ^ 59
def prefixEnd_40532 : Nat := 4983230072969 + 3 ^ 40 * 40532 * 2
def baseEnd_40532 : Nat := 20812397888140652063603

theorem tailTrace_40532 : CollatzResearch.WordTrace tailWord_40532 prefixEnd_40532 20812397888140652063603 := by
  unfold tailWord_40532
  simp only [CollatzResearch.WordTrace]
  refine ⟨739161744583480579797925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 985548992777974106397233 739161744583480579797925)
  ·
    refine ⟨138592827109402608712111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 739161744583480579797925 138592827109402608712111)
    ·
      refine ⟨207889240664103913068167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138592827109402608712111 207889240664103913068167)
      ·
        refine ⟨311833860996155869602251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207889240664103913068167 311833860996155869602251)
        ·
          refine ⟨467750791494233804403377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311833860996155869602251 467750791494233804403377)
          ·
            refine ⟨350813093620675353302533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 467750791494233804403377 350813093620675353302533)
            ·
              refine ⟨65777455053876628744225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 350813093620675353302533 65777455053876628744225)
              ·
                refine ⟨49333091290407471558169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65777455053876628744225 49333091290407471558169)
                ·
                  refine ⟨36999818467805603668627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49333091290407471558169 36999818467805603668627)
                  ·
                    refine ⟨55499727701708405502941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36999818467805603668627 55499727701708405502941)
                    ·
                      refine ⟨20812397888140652063603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 55499727701708405502941 20812397888140652063603)
                      ·
                        rfl

theorem cell23_40532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_40532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40532 prefixEnd_40532 := by exact prefixLift 40532
  have htrace : WordTrace (prefixWord ++ tailWord_40532) baseStart_40532 baseEnd_40532 := by
    simpa [prefixWord, tailWord_40532, baseEnd_40532] using wordTrace_append hprefix tailTrace_40532
  have hstable : (prefixWord ++ tailWord_40532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40532).length < 2 ^ (prefixWord ++ tailWord_40532).sum := by decide
  have hdescent : baseEnd_40532 < baseStart_40532 := by decide
  rcases family_descends (prefixWord ++ tailWord_40532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40548 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_40548 : Nat := 118140960795 + 40548 * 2 ^ 59
def prefixEnd_40548 : Nat := 4983230072969 + 3 ^ 40 * 40548 * 2
def baseEnd_40548 : Nat := 6940204526204196487843

theorem tailTrace_40548 : CollatzResearch.WordTrace tailWord_40548 prefixEnd_40548 6940204526204196487843 := by
  unfold tailWord_40548
  simp only [CollatzResearch.WordTrace]
  refine ⟨739453528554497946089149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 985938038072663928118865 739453528554497946089149)
  ·
    refine ⟨277295073207936729783431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 739453528554497946089149 277295073207936729783431)
    ·
      refine ⟨415942609811905094675147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277295073207936729783431 415942609811905094675147)
      ·
        refine ⟨623913914717857642012721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415942609811905094675147 623913914717857642012721)
        ·
          refine ⟨467935436038393231509541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623913914717857642012721 467935436038393231509541)
          ·
            refine ⟨87737894257198730908039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 467935436038393231509541 87737894257198730908039)
            ·
              refine ⟨131606841385798096362059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87737894257198730908039 131606841385798096362059)
              ·
                refine ⟨197410262078697144543089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131606841385798096362059 197410262078697144543089)
                ·
                  refine ⟨148057696559022858407317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197410262078697144543089 148057696559022858407317)
                  ·
                    refine ⟨6940204526204196487843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148057696559022858407317 6940204526204196487843)
                    ·
                      rfl

theorem cell23_40548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_40548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40548 prefixEnd_40548 := by exact prefixLift 40548
  have htrace : WordTrace (prefixWord ++ tailWord_40548) baseStart_40548 baseEnd_40548 := by
    simpa [prefixWord, tailWord_40548, baseEnd_40548] using wordTrace_append hprefix tailTrace_40548
  have hstable : (prefixWord ++ tailWord_40548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40548).length < 2 ^ (prefixWord ++ tailWord_40548).sum := by decide
  have hdescent : baseEnd_40548 < baseStart_40548 := by decide
  rcases family_descends (prefixWord ++ tailWord_40548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40588 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 4, 3, 3]
def baseStart_40588 : Nat := 118140960795 + 40588 * 2 ^ 59
def prefixEnd_40588 : Nat := 4983230072969 + 3 ^ 40 * 40588 * 2
def baseEnd_40588 : Nat := 20841152804792432963345

theorem tailTrace_40588 : CollatzResearch.WordTrace tailWord_40588 prefixEnd_40588 20841152804792432963345 := by
  unfold tailWord_40588
  simp only [CollatzResearch.WordTrace]
  refine ⟨740182988482041361817209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 986910651309388482422945 740182988482041361817209)
  ·
    refine ⟨555137241361531021362907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 740182988482041361817209 555137241361531021362907)
    ·
      refine ⟨832705862042296532044361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555137241361531021362907 832705862042296532044361)
      ·
        refine ⟨624529396531722399033271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 832705862042296532044361 624529396531722399033271)
        ·
          refine ⟨936794094797583598549907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624529396531722399033271 936794094797583598549907)
          ·
            refine ⟨1405191142196375397824861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936794094797583598549907 1405191142196375397824861)
            ·
              refine ⟨526946678323640774184323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1405191142196375397824861 526946678323640774184323)
              ·
                refine ⟨790420017485461161276485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526946678323640774184323 790420017485461161276485)
                ·
                  refine ⟨148203753278523967739341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790420017485461161276485 148203753278523967739341)
                  ·
                    refine ⟨55576407479446487902253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148203753278523967739341 55576407479446487902253)
                    ·
                      refine ⟨20841152804792432963345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 55576407479446487902253 20841152804792432963345)
                      ·
                        rfl

theorem cell23_40588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_40588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40588 prefixEnd_40588 := by exact prefixLift 40588
  have htrace : WordTrace (prefixWord ++ tailWord_40588) baseStart_40588 baseEnd_40588 := by
    simpa [prefixWord, tailWord_40588, baseEnd_40588] using wordTrace_append hprefix tailTrace_40588
  have hstable : (prefixWord ++ tailWord_40588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40588).length < 2 ^ (prefixWord ++ tailWord_40588).sum := by decide
  have hdescent : baseEnd_40588 < baseStart_40588 := by decide
  rcases family_descends (prefixWord ++ tailWord_40588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40591 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 5, 7]
def baseStart_40591 : Nat := 118140960795 + 40591 * 2 ^ 59
def prefixEnd_40591 : Nat := 4983230072969 + 3 ^ 40 * 40591 * 2
def baseEnd_40591 : Nat := 6947564415585307075277

theorem tailTrace_40591 : CollatzResearch.WordTrace tailWord_40591 prefixEnd_40591 6947564415585307075277 := by
  unfold tailWord_40591
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480475395953214235993627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 986983597302142823995751 1480475395953214235993627)
  ·
    refine ⟨2220713093929821353990441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1480475395953214235993627 2220713093929821353990441)
    ·
      refine ⟨1665534820447366015492831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2220713093929821353990441 1665534820447366015492831)
      ·
        refine ⟨2498302230671049023239247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665534820447366015492831 2498302230671049023239247)
        ·
          refine ⟨3747453346006573534858871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498302230671049023239247 3747453346006573534858871)
          ·
            refine ⟨5621180019009860302288307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747453346006573534858871 5621180019009860302288307)
            ·
              refine ⟨8431770028514790453432461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5621180019009860302288307 8431770028514790453432461)
              ·
                refine ⟨3161913760693046420037173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8431770028514790453432461 3161913760693046420037173)
                ·
                  refine ⟨296429415064973101878485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3161913760693046420037173 296429415064973101878485)
                  ·
                    refine ⟨6947564415585307075277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 296429415064973101878485 6947564415585307075277)
                    ·
                      rfl

theorem cell23_40591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_40591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40591 prefixEnd_40591 := by exact prefixLift 40591
  have htrace : WordTrace (prefixWord ++ tailWord_40591) baseStart_40591 baseEnd_40591 := by
    simpa [prefixWord, tailWord_40591, baseEnd_40591] using wordTrace_append hprefix tailTrace_40591
  have hstable : (prefixWord ++ tailWord_40591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40591).length < 2 ^ (prefixWord ++ tailWord_40591).sum := by decide
  have hdescent : baseEnd_40591 < baseStart_40591 := by decide
  rcases family_descends (prefixWord ++ tailWord_40591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40608 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 1, 7]
def baseStart_40608 : Nat := 118140960795 + 40608 * 2 ^ 59
def prefixEnd_40608 : Nat := 4983230072969 + 3 ^ 40 * 40608 * 2
def baseEnd_40608 : Nat := 6950474139294118237751

theorem tailTrace_40608 : CollatzResearch.WordTrace tailWord_40608 prefixEnd_40608 6950474139294118237751 := by
  unfold tailWord_40608
  simp only [CollatzResearch.WordTrace]
  refine ⟨740547718445813069681239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 987396957927750759574985 740547718445813069681239)
  ·
    refine ⟨1110821577668719604521859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 740547718445813069681239 1110821577668719604521859)
    ·
      refine ⟨1666232366503079406782789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110821577668719604521859 1666232366503079406782789)
      ·
        refine ⟨312418568719327388771773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1666232366503079406782789 312418568719327388771773)
        ·
          refine ⟨117156963269747770789415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312418568719327388771773 117156963269747770789415)
          ·
            refine ⟨175735444904621656184123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117156963269747770789415 175735444904621656184123)
            ·
              refine ⟨263603167356932484276185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175735444904621656184123 263603167356932484276185)
              ·
                refine ⟨197702375517699363207139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263603167356932484276185 197702375517699363207139)
                ·
                  refine ⟨296553563276549044810709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197702375517699363207139 296553563276549044810709)
                  ·
                    refine ⟨6950474139294118237751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 296553563276549044810709 6950474139294118237751)
                    ·
                      rfl

theorem cell23_40608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_40608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40608 prefixEnd_40608 := by exact prefixLift 40608
  have htrace : WordTrace (prefixWord ++ tailWord_40608) baseStart_40608 baseEnd_40608 := by
    simpa [prefixWord, tailWord_40608, baseEnd_40608] using wordTrace_append hprefix tailTrace_40608
  have hstable : (prefixWord ++ tailWord_40608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40608).length < 2 ^ (prefixWord ++ tailWord_40608).sum := by decide
  have hdescent : baseEnd_40608 < baseStart_40608 := by decide
  rcases family_descends (prefixWord ++ tailWord_40608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40629 : List Nat := [1, 3, 3, 3, 2, 2, 1, 3, 5]
def baseStart_40629 : Nat := 118140960795 + 40629 * 2 ^ 59
def prefixEnd_40629 : Nat := 4983230072969 + 3 ^ 40 * 40629 * 2
def baseEnd_40629 : Nat := 2318022834625196950073

theorem tailTrace_40629 : CollatzResearch.WordTrace tailWord_40629 prefixEnd_40629 2318022834625196950073 := by
  unfold tailWord_40629
  simp only [CollatzResearch.WordTrace]
  refine ⟨1481861369815546725876941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 987907579877031150584627 1481861369815546725876941)
  ·
    refine ⟨555698013680830022203853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1481861369815546725876941 555698013680830022203853)
    ·
      refine ⟨208386755130311258326445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 555698013680830022203853 208386755130311258326445)
      ·
        refine ⟨78145033173866721872417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208386755130311258326445 78145033173866721872417)
        ·
          refine ⟨58608774880400041404313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78145033173866721872417 58608774880400041404313)
          ·
            refine ⟨43956581160300031053235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58608774880400041404313 43956581160300031053235)
            ·
              refine ⟨65934871740450046579853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43956581160300031053235 65934871740450046579853)
              ·
                refine ⟨24725576902668767467445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65934871740450046579853 24725576902668767467445)
                ·
                  refine ⟨2318022834625196950073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24725576902668767467445 2318022834625196950073)
                  ·
                    rfl

theorem cell23_40629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_40629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40629 prefixEnd_40629 := by exact prefixLift 40629
  have htrace : WordTrace (prefixWord ++ tailWord_40629) baseStart_40629 baseEnd_40629 := by
    simpa [prefixWord, tailWord_40629, baseEnd_40629] using wordTrace_append hprefix tailTrace_40629
  have hstable : (prefixWord ++ tailWord_40629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40629).length < 2 ^ (prefixWord ++ tailWord_40629).sum := by decide
  have hdescent : baseEnd_40629 < baseStart_40629 := by decide
  rcases family_descends (prefixWord ++ tailWord_40629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40679 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_40679 : Nat := 118140960795 + 40679 * 2 ^ 59
def prefixEnd_40679 : Nat := 4983230072969 + 3 ^ 40 * 40679 * 2
def baseEnd_40679 : Nat := 20887879544351576925427

theorem tailTrace_40679 : CollatzResearch.WordTrace tailWord_40679 prefixEnd_40679 20887879544351576925427 := by
  unfold tailWord_40679
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483685019634405265197091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 989123346422936843464727 1483685019634405265197091)
  ·
    refine ⟨2225527529451607897795637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1483685019634405265197091 2225527529451607897795637)
    ·
      refine ⟨208643205886088240418341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2225527529451607897795637 208643205886088240418341)
      ·
        refine ⟨39120601103641545078439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208643205886088240418341 39120601103641545078439)
        ·
          refine ⟨58680901655462317617659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39120601103641545078439 58680901655462317617659)
          ·
            refine ⟨88021352483193476426489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58680901655462317617659 88021352483193476426489)
            ·
              refine ⟨66016014362395107319867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88021352483193476426489 66016014362395107319867)
              ·
                refine ⟨99024021543592660979801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66016014362395107319867 99024021543592660979801)
                ·
                  refine ⟨74268016157694495734851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99024021543592660979801 74268016157694495734851)
                  ·
                    refine ⟨111402024236541743602277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74268016157694495734851 111402024236541743602277)
                    ·
                      refine ⟨20887879544351576925427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 111402024236541743602277 20887879544351576925427)
                      ·
                        rfl

theorem cell23_40679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_40679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40679 prefixEnd_40679 := by exact prefixLift 40679
  have htrace : WordTrace (prefixWord ++ tailWord_40679) baseStart_40679 baseEnd_40679 := by
    simpa [prefixWord, tailWord_40679, baseEnd_40679] using wordTrace_append hprefix tailTrace_40679
  have hstable : (prefixWord ++ tailWord_40679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40679).length < 2 ^ (prefixWord ++ tailWord_40679).sum := by decide
  have hdescent : baseEnd_40679 < baseStart_40679 := by decide
  rcases family_descends (prefixWord ++ tailWord_40679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40712 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_40712 : Nat := 118140960795 + 40712 * 2 ^ 59
def prefixEnd_40712 : Nat := 4983230072969 + 3 ^ 40 * 40712 * 2
def baseEnd_40712 : Nat := 20904824405949947812775

theorem tailTrace_40712 : CollatzResearch.WordTrace tailWord_40712 prefixEnd_40712 20904824405949947812775 := by
  unfold tailWord_40712
  simp only [CollatzResearch.WordTrace]
  refine ⟨742444314257425950574195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 989925752343234600765593 742444314257425950574195)
  ·
    refine ⟨1113666471386138925861293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 742444314257425950574195 1113666471386138925861293)
    ·
      refine ⟨417624926769802097197985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1113666471386138925861293 417624926769802097197985)
      ·
        refine ⟨313218695077351572898489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417624926769802097197985 313218695077351572898489)
        ·
          refine ⟨234914021308013679673867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313218695077351572898489 234914021308013679673867)
          ·
            refine ⟨352371031962020519510801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234914021308013679673867 352371031962020519510801)
            ·
              refine ⟨264278273971515389633101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352371031962020519510801 264278273971515389633101)
              ·
                refine ⟨99104352739318271112413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264278273971515389633101 99104352739318271112413)
                ·
                  refine ⟨37164132277244351667155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99104352739318271112413 37164132277244351667155)
                  ·
                    refine ⟨55746198415866527500733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37164132277244351667155 55746198415866527500733)
                    ·
                      refine ⟨20904824405949947812775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 55746198415866527500733 20904824405949947812775)
                      ·
                        rfl

theorem cell23_40712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_40712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40712 prefixEnd_40712 := by exact prefixLift 40712
  have htrace : WordTrace (prefixWord ++ tailWord_40712) baseStart_40712 baseEnd_40712 := by
    simpa [prefixWord, tailWord_40712, baseEnd_40712] using wordTrace_append hprefix tailTrace_40712
  have hstable : (prefixWord ++ tailWord_40712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40712).length < 2 ^ (prefixWord ++ tailWord_40712).sum := by decide
  have hdescent : baseEnd_40712 < baseStart_40712 := by decide
  rcases family_descends (prefixWord ++ tailWord_40712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40735 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 4]
def baseStart_40735 : Nat := 118140960795 + 40735 * 2 ^ 59
def prefixEnd_40735 : Nat := 4983230072969 + 3 ^ 40 * 40735 * 2
def baseEnd_40735 : Nat := 20916634461003357825169

theorem tailTrace_40735 : CollatzResearch.WordTrace tailWord_40735 prefixEnd_40735 20916634461003357825169 := by
  unfold tailWord_40735
  simp only [CollatzResearch.WordTrace]
  refine ⟨1485727507431526829235659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 990485004954351219490439 1485727507431526829235659)
  ·
    refine ⟨2228591261147290243853489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1485727507431526829235659 2228591261147290243853489)
    ·
      refine ⟨1671443445860467682890117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2228591261147290243853489 1671443445860467682890117)
      ·
        refine ⟨313395646098837690541897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1671443445860467682890117 313395646098837690541897)
        ·
          refine ⟨235046734574128267906423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313395646098837690541897 235046734574128267906423)
          ·
            refine ⟨352570101861192401859635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235046734574128267906423 352570101861192401859635)
            ·
              refine ⟨528855152791788602789453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352570101861192401859635 528855152791788602789453)
              ·
                refine ⟨198320682296920726046045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528855152791788602789453 198320682296920726046045)
                ·
                  refine ⟨74370255861345272267267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198320682296920726046045 74370255861345272267267)
                  ·
                    refine ⟨111555383792017908400901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74370255861345272267267 111555383792017908400901)
                    ·
                      refine ⟨20916634461003357825169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 111555383792017908400901 20916634461003357825169)
                      ·
                        rfl

theorem cell23_40735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_40735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40735 prefixEnd_40735 := by exact prefixLift 40735
  have htrace : WordTrace (prefixWord ++ tailWord_40735) baseStart_40735 baseEnd_40735 := by
    simpa [prefixWord, tailWord_40735, baseEnd_40735] using wordTrace_append hprefix tailTrace_40735
  have hstable : (prefixWord ++ tailWord_40735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40735).length < 2 ^ (prefixWord ++ tailWord_40735).sum := by decide
  have hdescent : baseEnd_40735 < baseStart_40735 := by decide
  rcases family_descends (prefixWord ++ tailWord_40735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40762 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_40762 : Nat := 118140960795 + 40762 * 2 ^ 59
def prefixEnd_40762 : Nat := 4983230072969 + 3 ^ 40 * 40762 * 2
def baseEnd_40762 : Nat := 6976832812891584062515

theorem tailTrace_40762 : CollatzResearch.WordTrace tailWord_40762 prefixEnd_40762 6976832812891584062515 := by
  unfold tailWord_40762
  simp only [CollatzResearch.WordTrace]
  refine ⟨371678069583427610117135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 991141518889140293645693 371678069583427610117135)
  ·
    refine ⟨557517104375141415175703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 371678069583427610117135 557517104375141415175703)
    ·
      refine ⟨836275656562712122763555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557517104375141415175703 836275656562712122763555)
      ·
        refine ⟨1254413484844068184145333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836275656562712122763555 1254413484844068184145333)
        ·
          refine ⟨117601264204131392263625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1254413484844068184145333 117601264204131392263625)
          ·
            refine ⟨88200948153098544197719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117601264204131392263625 88200948153098544197719)
            ·
              refine ⟨132301422229647816296579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88200948153098544197719 132301422229647816296579)
              ·
                refine ⟨198452133344471724444869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132301422229647816296579 198452133344471724444869)
                ·
                  refine ⟨37209775002088448333413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198452133344471724444869 37209775002088448333413)
                  ·
                    refine ⟨6976832812891584062515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37209775002088448333413 6976832812891584062515)
                    ·
                      rfl

theorem cell23_40762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_40762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40762 prefixEnd_40762 := by exact prefixLift 40762
  have htrace : WordTrace (prefixWord ++ tailWord_40762) baseStart_40762 baseEnd_40762 := by
    simpa [prefixWord, tailWord_40762, baseEnd_40762] using wordTrace_append hprefix tailTrace_40762
  have hstable : (prefixWord ++ tailWord_40762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40762).length < 2 ^ (prefixWord ++ tailWord_40762).sum := by decide
  have hdescent : baseEnd_40762 < baseStart_40762 := by decide
  rcases family_descends (prefixWord ++ tailWord_40762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40768 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_40768 : Nat := 118140960795 + 40768 * 2 ^ 59
def prefixEnd_40768 : Nat := 4983230072969 + 3 ^ 40 * 40768 * 2
def baseEnd_40768 : Nat := 20933579322601728712517

theorem tailTrace_40768 : CollatzResearch.WordTrace tailWord_40768 prefixEnd_40768 20933579322601728712517 := by
  unfold tailWord_40768
  simp only [CollatzResearch.WordTrace]
  refine ⟨743465558155986732593479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 991287410874648976791305 743465558155986732593479)
  ·
    refine ⟨1115198337233980098890219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 743465558155986732593479 1115198337233980098890219)
    ·
      refine ⟨1672797505850970148335329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115198337233980098890219 1672797505850970148335329)
      ·
        refine ⟨1254598129388227611251497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1672797505850970148335329 1254598129388227611251497)
        ·
          refine ⟨940948597041170708438623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1254598129388227611251497 940948597041170708438623)
          ·
            refine ⟨1411422895561756062657935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940948597041170708438623 1411422895561756062657935)
            ·
              refine ⟨2117134343342634093986903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411422895561756062657935 2117134343342634093986903)
              ·
                refine ⟨3175701515013951140980355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117134343342634093986903 3175701515013951140980355)
                ·
                  refine ⟨4763552272520926711470533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175701515013951140980355 4763552272520926711470533)
                  ·
                    refine ⟨893166051097673758400725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763552272520926711470533 893166051097673758400725)
                    ·
                      refine ⟨20933579322601728712517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 893166051097673758400725 20933579322601728712517)
                      ·
                        rfl

theorem cell23_40768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_40768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40768 prefixEnd_40768 := by exact prefixLift 40768
  have htrace : WordTrace (prefixWord ++ tailWord_40768) baseStart_40768 baseEnd_40768 := by
    simpa [prefixWord, tailWord_40768, baseEnd_40768] using wordTrace_append hprefix tailTrace_40768
  have hstable : (prefixWord ++ tailWord_40768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40768).length < 2 ^ (prefixWord ++ tailWord_40768).sum := by decide
  have hdescent : baseEnd_40768 < baseStart_40768 := by decide
  rcases family_descends (prefixWord ++ tailWord_40768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40789 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_40789 : Nat := 118140960795 + 40789 * 2 ^ 59
def prefixEnd_40789 : Nat := 4983230072969 + 3 ^ 40 * 40789 * 2
def baseEnd_40789 : Nat := 20944362416346146549921

theorem tailTrace_40789 : CollatzResearch.WordTrace tailWord_40789 prefixEnd_40789 20944362416346146549921 := by
  unfold tailWord_40789
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487697049235894051701421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 991798032823929367800947 1487697049235894051701421)
  ·
    refine ⟨557886393463460269388033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1487697049235894051701421 557886393463460269388033)
    ·
      refine ⟨418414795097595202041025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 557886393463460269388033 418414795097595202041025)
      ·
        refine ⟨313811096323196401530769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418414795097595202041025 313811096323196401530769)
        ·
          refine ⟨235358322242397301148077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313811096323196401530769 235358322242397301148077)
          ·
            refine ⟨88259370840898987930529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235358322242397301148077 88259370840898987930529)
            ·
              refine ⟨66194528130674240947897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88259370840898987930529 66194528130674240947897)
              ·
                refine ⟨49645896098005680710923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66194528130674240947897 49645896098005680710923)
                ·
                  refine ⟨74468844147008521066385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49645896098005680710923 74468844147008521066385)
                  ·
                    refine ⟨55851633110256390799789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74468844147008521066385 55851633110256390799789)
                    ·
                      refine ⟨20944362416346146549921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 55851633110256390799789 20944362416346146549921)
                      ·
                        rfl

theorem cell23_40789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_40789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40789 prefixEnd_40789 := by exact prefixLift 40789
  have htrace : WordTrace (prefixWord ++ tailWord_40789) baseStart_40789 baseEnd_40789 := by
    simpa [prefixWord, tailWord_40789, baseEnd_40789] using wordTrace_append hprefix tailTrace_40789
  have hstable : (prefixWord ++ tailWord_40789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40789).length < 2 ^ (prefixWord ++ tailWord_40789).sum := by decide
  have hdescent : baseEnd_40789 < baseStart_40789 := by decide
  rcases family_descends (prefixWord ++ tailWord_40789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40825 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_40825 : Nat := 118140960795 + 40825 * 2 ^ 59
def prefixEnd_40825 : Nat := 4983230072969 + 3 ^ 40 * 40825 * 2
def baseEnd_40825 : Nat := 20962847719908005699755

theorem tailTrace_40825 : CollatzResearch.WordTrace tailWord_40825 prefixEnd_40825 20962847719908005699755 := by
  unfold tailWord_40825
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489010077105472200011929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 992673384736981466674619 1489010077105472200011929)
  ·
    refine ⟨1116757557829104150008947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1489010077105472200011929 1116757557829104150008947)
    ·
      refine ⟨1675136336743656225013421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116757557829104150008947 1675136336743656225013421)
      ·
        refine ⟨628176126278871084380033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1675136336743656225013421 628176126278871084380033)
        ·
          refine ⟨471132094709153313285025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 628176126278871084380033 471132094709153313285025)
          ·
            refine ⟨353349071031864984963769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471132094709153313285025 353349071031864984963769)
            ·
              refine ⟨265011803273898738722827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353349071031864984963769 265011803273898738722827)
              ·
                refine ⟨397517704910848108084241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265011803273898738722827 397517704910848108084241)
                ·
                  refine ⟨298138278683136081063181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397517704910848108084241 298138278683136081063181)
                  ·
                    refine ⟨111801854506176030398693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 298138278683136081063181 111801854506176030398693)
                    ·
                      refine ⟨20962847719908005699755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 111801854506176030398693 20962847719908005699755)
                      ·
                        rfl

theorem cell23_40825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_40825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40825 prefixEnd_40825 := by exact prefixLift 40825
  have htrace : WordTrace (prefixWord ++ tailWord_40825) baseStart_40825 baseEnd_40825 := by
    simpa [prefixWord, tailWord_40825, baseEnd_40825] using wordTrace_append hprefix tailTrace_40825
  have hstable : (prefixWord ++ tailWord_40825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40825).length < 2 ^ (prefixWord ++ tailWord_40825).sum := by decide
  have hdescent : baseEnd_40825 < baseStart_40825 := by decide
  rcases family_descends (prefixWord ++ tailWord_40825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40836 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_40836 : Nat := 118140960795 + 40836 * 2 ^ 59
def prefixEnd_40836 : Nat := 4983230072969 + 3 ^ 40 * 40836 * 2
def baseEnd_40836 : Nat := 20968496007107462662205

theorem tailTrace_40836 : CollatzResearch.WordTrace tailWord_40836 prefixEnd_40836 20968496007107462662205 := by
  unfold tailWord_40836
  simp only [CollatzResearch.WordTrace]
  refine ⟨744705640032810539331181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 992940853377080719108241 744705640032810539331181)
  ·
    refine ⟨279264615012303952249193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 744705640032810539331181 279264615012303952249193)
    ·
      refine ⟨209448461259227964186895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279264615012303952249193 209448461259227964186895)
      ·
        refine ⟨314172691888841946280343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209448461259227964186895 314172691888841946280343)
        ·
          refine ⟨471259037833262919420515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314172691888841946280343 471259037833262919420515)
          ·
            refine ⟨706888556749894379130773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471259037833262919420515 706888556749894379130773)
            ·
              refine ⟨33135401097651299021755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 706888556749894379130773 33135401097651299021755)
              ·
                refine ⟨49703101646476948532633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33135401097651299021755 49703101646476948532633)
                ·
                  refine ⟨37277326234857711399475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49703101646476948532633 37277326234857711399475)
                  ·
                    refine ⟨55915989352286567099213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37277326234857711399475 55915989352286567099213)
                    ·
                      refine ⟨20968496007107462662205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 55915989352286567099213 20968496007107462662205)
                      ·
                        rfl

theorem cell23_40836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_40836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40836 prefixEnd_40836 := by exact prefixLift 40836
  have htrace : WordTrace (prefixWord ++ tailWord_40836) baseStart_40836 baseEnd_40836 := by
    simpa [prefixWord, tailWord_40836, baseEnd_40836] using wordTrace_append hprefix tailTrace_40836
  have hstable : (prefixWord ++ tailWord_40836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40836).length < 2 ^ (prefixWord ++ tailWord_40836).sum := by decide
  have hdescent : baseEnd_40836 < baseStart_40836 := by decide
  rcases family_descends (prefixWord ++ tailWord_40836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40863 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 1, 3, 2]
def baseStart_40863 : Nat := 118140960795 + 40863 * 2 ^ 59
def prefixEnd_40863 : Nat := 4983230072969 + 3 ^ 40 * 40863 * 2
def baseEnd_40863 : Nat := 20982359984778857024581

theorem tailTrace_40863 : CollatzResearch.WordTrace tailWord_40863 prefixEnd_40863 20982359984778857024581 := by
  unfold tailWord_40863
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490396050967804689895243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 993597367311869793263495 1490396050967804689895243)
  ·
    refine ⟨2235594076451707034842865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1490396050967804689895243 2235594076451707034842865)
    ·
      refine ⟨1676695557338780276132149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2235594076451707034842865 1676695557338780276132149)
      ·
        refine ⟨157190208500510650887389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1676695557338780276132149 157190208500510650887389)
        ·
          refine ⟨58946328187691494082771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157190208500510650887389 58946328187691494082771)
          ·
            refine ⟨88419492281537241124157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58946328187691494082771 88419492281537241124157)
            ·
              refine ⟨33157309605576465421559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88419492281537241124157 33157309605576465421559)
              ·
                refine ⟨49735964408364698132339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33157309605576465421559 49735964408364698132339)
                ·
                  refine ⟨74603946612547047198509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49735964408364698132339 74603946612547047198509)
                  ·
                    refine ⟨27976479979705142699441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74603946612547047198509 27976479979705142699441)
                    ·
                      refine ⟨20982359984778857024581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 27976479979705142699441 20982359984778857024581)
                      ·
                        rfl

theorem cell23_40863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_40863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40863 prefixEnd_40863 := by exact prefixLift 40863
  have htrace : WordTrace (prefixWord ++ tailWord_40863) baseStart_40863 baseEnd_40863 := by
    simpa [prefixWord, tailWord_40863, baseEnd_40863] using wordTrace_append hprefix tailTrace_40863
  have hstable : (prefixWord ++ tailWord_40863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40863).length < 2 ^ (prefixWord ++ tailWord_40863).sum := by decide
  have hdescent : baseEnd_40863 < baseStart_40863 := by decide
  rcases family_descends (prefixWord ++ tailWord_40863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40895 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 1, 7]
def baseStart_40895 : Nat := 118140960795 + 40895 * 2 ^ 59
def prefixEnd_40895 : Nat := 4983230072969 + 3 ^ 40 * 40895 * 2
def baseEnd_40895 : Nat := 6999597121907577274811

theorem tailTrace_40895 : CollatzResearch.WordTrace tailWord_40895 prefixEnd_40895 6999597121907577274811 := by
  unfold tailWord_40895
  simp only [CollatzResearch.WordTrace]
  refine ⟨1491563186851874155060139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 994375457901249436706759 1491563186851874155060139)
  ·
    refine ⟨2237344780277811232590209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1491563186851874155060139 2237344780277811232590209)
    ·
      refine ⟨1678008585208358424442657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2237344780277811232590209 1678008585208358424442657)
      ·
        refine ⟨1258506438906268818331993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1678008585208358424442657 1258506438906268818331993)
        ·
          refine ⟨943879829179701613748995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258506438906268818331993 943879829179701613748995)
          ·
            refine ⟨1415819743769552420623493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943879829179701613748995 1415819743769552420623493)
            ·
              refine ⟨265466201956791078866905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1415819743769552420623493 265466201956791078866905)
              ·
                refine ⟨199099651467593309150179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265466201956791078866905 199099651467593309150179)
                ·
                  refine ⟨298649477201389963725269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199099651467593309150179 298649477201389963725269)
                  ·
                    refine ⟨6999597121907577274811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 298649477201389963725269 6999597121907577274811)
                    ·
                      rfl

theorem cell23_40895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_40895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40895 prefixEnd_40895 := by exact prefixLift 40895
  have htrace : WordTrace (prefixWord ++ tailWord_40895) baseStart_40895 baseEnd_40895 := by
    simpa [prefixWord, tailWord_40895, baseEnd_40895] using wordTrace_append hprefix tailTrace_40895
  have hstable : (prefixWord ++ tailWord_40895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40895).length < 2 ^ (prefixWord ++ tailWord_40895).sum := by decide
  have hdescent : baseEnd_40895 < baseStart_40895 := by decide
  rcases family_descends (prefixWord ++ tailWord_40895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40912 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 2, 5]
def baseStart_40912 : Nat := 118140960795 + 40912 * 2 ^ 59
def prefixEnd_40912 : Nat := 4983230072969 + 3 ^ 40 * 40912 * 2
def baseEnd_40912 : Nat := 7002506845616388437285

theorem tailTrace_40912 : CollatzResearch.WordTrace tailWord_40912 prefixEnd_40912 7002506845616388437285 := by
  unfold tailWord_40912
  simp only [CollatzResearch.WordTrace]
  refine ⟨746091613895143029214495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 994788818526857372285993 746091613895143029214495)
  ·
    refine ⟨1119137420842714543821743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 746091613895143029214495 1119137420842714543821743)
    ·
      refine ⟨1678706131264071815732615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1119137420842714543821743 1678706131264071815732615)
      ·
        refine ⟨2518059196896107723598923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678706131264071815732615 2518059196896107723598923)
        ·
          refine ⟨3777088795344161585398385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518059196896107723598923 3777088795344161585398385)
          ·
            refine ⟨2832816596508121189048789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3777088795344161585398385 2832816596508121189048789)
            ·
              refine ⟨66394138980659090368331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2832816596508121189048789 66394138980659090368331)
              ·
                refine ⟨99591208470988635552497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66394138980659090368331 99591208470988635552497)
                ·
                  refine ⟨74693406353241476664373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99591208470988635552497 74693406353241476664373)
                  ·
                    refine ⟨7002506845616388437285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74693406353241476664373 7002506845616388437285)
                    ·
                      rfl

theorem cell23_40912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 5].length) (baseStart_40912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40912 prefixEnd_40912 := by exact prefixLift 40912
  have htrace : WordTrace (prefixWord ++ tailWord_40912) baseStart_40912 baseEnd_40912 := by
    simpa [prefixWord, tailWord_40912, baseEnd_40912] using wordTrace_append hprefix tailTrace_40912
  have hstable : (prefixWord ++ tailWord_40912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40912).length < 2 ^ (prefixWord ++ tailWord_40912).sum := by decide
  have hdescent : baseEnd_40912 < baseStart_40912 := by decide
  rcases family_descends (prefixWord ++ tailWord_40912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40932 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_40932 : Nat := 118140960795 + 40932 * 2 ^ 59
def prefixEnd_40932 : Nat := 4983230072969 + 3 ^ 40 * 40932 * 2
def baseEnd_40932 : Nat := 21017790149939087061763

theorem tailTrace_40932 : CollatzResearch.WordTrace tailWord_40932 prefixEnd_40932 21017790149939087061763 := by
  unfold tailWord_40932
  simp only [CollatzResearch.WordTrace]
  refine ⟨746456343858914737078525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 995275125145219649438033 746456343858914737078525)
  ·
    refine ⟨279921128947093026404447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 746456343858914737078525 279921128947093026404447)
    ·
      refine ⟨419881693420639539606671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279921128947093026404447 419881693420639539606671)
      ·
        refine ⟨629822540130959309410007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419881693420639539606671 629822540130959309410007)
        ·
          refine ⟨944733810196438964115011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629822540130959309410007 944733810196438964115011)
          ·
            refine ⟨1417100715294658446172517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944733810196438964115011 1417100715294658446172517)
            ·
              refine ⟨265706384117748458657347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1417100715294658446172517 265706384117748458657347)
              ·
                refine ⟨398559576176622687986021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265706384117748458657347 398559576176622687986021)
                ·
                  refine ⟨74729920533116753997379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 398559576176622687986021 74729920533116753997379)
                  ·
                    refine ⟨112094880799675130996069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74729920533116753997379 112094880799675130996069)
                    ·
                      refine ⟨21017790149939087061763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 112094880799675130996069 21017790149939087061763)
                      ·
                        rfl

theorem cell23_40932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_40932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40932 prefixEnd_40932 := by exact prefixLift 40932
  have htrace : WordTrace (prefixWord ++ tailWord_40932) baseStart_40932 baseEnd_40932 := by
    simpa [prefixWord, tailWord_40932, baseEnd_40932] using wordTrace_append hprefix tailTrace_40932
  have hstable : (prefixWord ++ tailWord_40932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40932).length < 2 ^ (prefixWord ++ tailWord_40932).sum := by decide
  have hdescent : baseEnd_40932 < baseStart_40932 := by decide
  rcases family_descends (prefixWord ++ tailWord_40932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40952 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 1, 4, 3]
def baseStart_40952 : Nat := 118140960795 + 40952 * 2 ^ 59
def prefixEnd_40952 : Nat := 4983230072969 + 3 ^ 40 * 40952 * 2
def baseEnd_40952 : Nat := 21028059763029008811671

theorem tailTrace_40952 : CollatzResearch.WordTrace tailWord_40952 prefixEnd_40952 21028059763029008811671 := by
  unfold tailWord_40952
  simp only [CollatzResearch.WordTrace]
  refine ⟨746821073822686444942555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 995761431763581926590073 746821073822686444942555)
  ·
    refine ⟨1120231610734029667413833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 746821073822686444942555 1120231610734029667413833)
    ·
      refine ⟨840173708050522250560375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1120231610734029667413833 840173708050522250560375)
      ·
        refine ⟨1260260562075783375840563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840173708050522250560375 1260260562075783375840563)
        ·
          refine ⟨1890390843113675063760845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1260260562075783375840563 1890390843113675063760845)
          ·
            refine ⟨708896566167628148910317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1890390843113675063760845 708896566167628148910317)
            ·
              refine ⟨265836212312860555841369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 708896566167628148910317 265836212312860555841369)
              ·
                refine ⟨199377159234645416881027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265836212312860555841369 199377159234645416881027)
                ·
                  refine ⟨299065738851968125321541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199377159234645416881027 299065738851968125321541)
                  ·
                    refine ⟨56074826034744023497789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 299065738851968125321541 56074826034744023497789)
                    ·
                      refine ⟨21028059763029008811671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 56074826034744023497789 21028059763029008811671)
                      ·
                        rfl

theorem cell23_40952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_40952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40952 prefixEnd_40952 := by exact prefixLift 40952
  have htrace : WordTrace (prefixWord ++ tailWord_40952) baseStart_40952 baseEnd_40952 := by
    simpa [prefixWord, tailWord_40952, baseEnd_40952] using wordTrace_append hprefix tailTrace_40952
  have hstable : (prefixWord ++ tailWord_40952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40952).length < 2 ^ (prefixWord ++ tailWord_40952).sum := by decide
  have hdescent : baseEnd_40952 < baseStart_40952 := by decide
  rcases family_descends (prefixWord ++ tailWord_40952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40993 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 3, 4]
def baseStart_40993 : Nat := 118140960795 + 40993 * 2 ^ 59
def prefixEnd_40993 : Nat := 4983230072969 + 3 ^ 40 * 40993 * 2
def baseEnd_40993 : Nat := 7016370823287782799661

theorem tailTrace_40993 : CollatzResearch.WordTrace tailWord_40993 prefixEnd_40993 7016370823287782799661 := by
  unfold tailWord_40993
  simp only [CollatzResearch.WordTrace]
  refine ⟨1495137540496836892127633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 996758360331224594751755 1495137540496836892127633)
  ·
    refine ⟨1121353155372627669095725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1495137540496836892127633 1121353155372627669095725)
    ·
      refine ⟨420507433264735375910897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1121353155372627669095725 420507433264735375910897)
      ·
        refine ⟨315380574948551531933173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420507433264735375910897 315380574948551531933173)
        ·
          refine ⟨29566928901426706118735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 315380574948551531933173 29566928901426706118735)
          ·
            refine ⟨44350393352140059178103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29566928901426706118735 44350393352140059178103)
            ·
              refine ⟨66525590028210088767155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44350393352140059178103 66525590028210088767155)
              ·
                refine ⟨99788385042315133150733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66525590028210088767155 99788385042315133150733)
                ·
                  refine ⟨37420644390868174931525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99788385042315133150733 37420644390868174931525)
                  ·
                    refine ⟨7016370823287782799661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37420644390868174931525 7016370823287782799661)
                    ·
                      rfl

theorem cell23_40993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_40993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40993 prefixEnd_40993 := by exact prefixLift 40993
  have htrace : WordTrace (prefixWord ++ tailWord_40993) baseStart_40993 baseEnd_40993 := by
    simpa [prefixWord, tailWord_40993, baseEnd_40993] using wordTrace_append hprefix tailTrace_40993
  have hstable : (prefixWord ++ tailWord_40993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40993).length < 2 ^ (prefixWord ++ tailWord_40993).sum := by decide
  have hdescent : baseEnd_40993 < baseStart_40993 := by decide
  rcases family_descends (prefixWord ++ tailWord_40993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41006 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_41006 : Nat := 118140960795 + 41006 * 2 ^ 59
def prefixEnd_41006 : Nat := 4983230072969 + 3 ^ 40 * 41006 * 2
def baseEnd_41006 : Nat := 2339531968707977504047

theorem tailTrace_41006 : CollatzResearch.WordTrace tailWord_41006 prefixEnd_41006 2339531968707977504047 := by
  unfold tailWord_41006
  simp only [CollatzResearch.WordTrace]
  refine ⟨186951461181217514043859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 997074459633160074900581 186951461181217514043859)
  ·
    refine ⟨280427191771826271065789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186951461181217514043859 280427191771826271065789)
    ·
      refine ⟨105160196914434851649671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280427191771826271065789 105160196914434851649671)
      ·
        refine ⟨157740295371652277474507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105160196914434851649671 157740295371652277474507)
        ·
          refine ⟨236610443057478416211761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157740295371652277474507 236610443057478416211761)
          ·
            refine ⟨177457832293108812158821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236610443057478416211761 177457832293108812158821)
            ·
              refine ⟨33273343554957902279779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177457832293108812158821 33273343554957902279779)
              ·
                refine ⟨49910015332436853419669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33273343554957902279779 49910015332436853419669)
                ·
                  refine ⟨2339531968707977504047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49910015332436853419669 2339531968707977504047)
                  ·
                    rfl

theorem cell23_41006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_41006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41006 prefixEnd_41006 := by exact prefixLift 41006
  have htrace : WordTrace (prefixWord ++ tailWord_41006) baseStart_41006 baseEnd_41006 := by
    simpa [prefixWord, tailWord_41006, baseEnd_41006] using wordTrace_append hprefix tailTrace_41006
  have hstable : (prefixWord ++ tailWord_41006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41006).length < 2 ^ (prefixWord ++ tailWord_41006).sum := by decide
  have hdescent : baseEnd_41006 < baseStart_41006 := by decide
  rcases family_descends (prefixWord ++ tailWord_41006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41059 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 3]
def baseStart_41059 : Nat := 118140960795 + 41059 * 2 ^ 59
def prefixEnd_41059 : Nat := 4983230072969 + 3 ^ 40 * 41059 * 2
def baseEnd_41059 : Nat := 21083002193060090173679

theorem tailTrace_41059 : CollatzResearch.WordTrace tailWord_41059 prefixEnd_41059 21083002193060090173679 := by
  unfold tailWord_41059
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497544758257730164030231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 998363172171820109353487 1497544758257730164030231)
  ·
    refine ⟨2246317137386595246045347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1497544758257730164030231 2246317137386595246045347)
    ·
      refine ⟨3369475706079892869068021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246317137386595246045347 3369475706079892869068021)
      ·
        refine ⟨315888347444989956475127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3369475706079892869068021 315888347444989956475127)
        ·
          refine ⟨473832521167484934712691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315888347444989956475127 473832521167484934712691)
          ·
            refine ⟨710748781751227402069037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473832521167484934712691 710748781751227402069037)
            ·
              refine ⟨266530793156710275775889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 710748781751227402069037 266530793156710275775889)
              ·
                refine ⟨199898094867532706831917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266530793156710275775889 199898094867532706831917)
                ·
                  refine ⟨74961785575324765061969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199898094867532706831917 74961785575324765061969)
                  ·
                    refine ⟨56221339181493573796477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74961785575324765061969 56221339181493573796477)
                    ·
                      refine ⟨21083002193060090173679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 56221339181493573796477 21083002193060090173679)
                      ·
                        rfl

theorem cell23_41059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_41059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41059 prefixEnd_41059 := by exact prefixLift 41059
  have htrace : WordTrace (prefixWord ++ tailWord_41059) baseStart_41059 baseEnd_41059 := by
    simpa [prefixWord, tailWord_41059, baseEnd_41059] using wordTrace_append hprefix tailTrace_41059
  have hstable : (prefixWord ++ tailWord_41059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41059).length < 2 ^ (prefixWord ++ tailWord_41059).sum := by decide
  have hdescent : baseEnd_41059 < baseStart_41059 := by decide
  rcases family_descends (prefixWord ++ tailWord_41059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41066 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_41066 : Nat := 118140960795 + 41066 * 2 ^ 59
def prefixEnd_41066 : Nat := 4983230072969 + 3 ^ 40 * 41066 * 2
def baseEnd_41066 : Nat := 7028865519213854262049

theorem tailTrace_41066 : CollatzResearch.WordTrace tailWord_41066 prefixEnd_41066 7028865519213854262049 := by
  unfold tailWord_41066
  simp only [CollatzResearch.WordTrace]
  refine ⟨374450017308092589883763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 998533379488246906356701 374450017308092589883763)
  ·
    refine ⟨561675025962138884825645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 374450017308092589883763 561675025962138884825645)
    ·
      refine ⟨210628134735802081809617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 561675025962138884825645 210628134735802081809617)
      ·
        refine ⟨157971101051851561357213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210628134735802081809617 157971101051851561357213)
        ·
          refine ⟨59239162894444335508955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157971101051851561357213 59239162894444335508955)
          ·
            refine ⟨88858744341666503263433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59239162894444335508955 88858744341666503263433)
            ·
              refine ⟨66644058256249877447575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88858744341666503263433 66644058256249877447575)
              ·
                refine ⟨99966087384374816171363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66644058256249877447575 99966087384374816171363)
                ·
                  refine ⟨149949131076562224257045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99966087384374816171363 149949131076562224257045)
                  ·
                    refine ⟨7028865519213854262049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 149949131076562224257045 7028865519213854262049)
                    ·
                      rfl

theorem cell23_41066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_41066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41066 prefixEnd_41066 := by exact prefixLift 41066
  have htrace : WordTrace (prefixWord ++ tailWord_41066) baseStart_41066 baseEnd_41066 := by
    simpa [prefixWord, tailWord_41066, baseEnd_41066] using wordTrace_append hprefix tailTrace_41066
  have hstable : (prefixWord ++ tailWord_41066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41066).length < 2 ^ (prefixWord ++ tailWord_41066).sum := by decide
  have hdescent : baseEnd_41066 < baseStart_41066 := by decide
  rcases family_descends (prefixWord ++ tailWord_41066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41079 : List Nat := [1, 1, 3, 1, 1, 6, 3, 7]
def baseStart_41079 : Nat := 118140960795 + 41079 * 2 ^ 59
def prefixEnd_41079 : Nat := 4983230072969 + 3 ^ 40 * 41079 * 2
def baseEnd_41079 : Nat := 781232289116667108281

theorem tailTrace_41079 : CollatzResearch.WordTrace tailWord_41079 prefixEnd_41079 781232289116667108281 := by
  unfold tailWord_41079
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498274218185273579758291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 998849478790182386505527 1498274218185273579758291)
  ·
    refine ⟨2247411327277910369637437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1498274218185273579758291 2247411327277910369637437)
    ·
      refine ⟨842779247729216388614039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2247411327277910369637437 842779247729216388614039)
      ·
        refine ⟨1264168871593824582921059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842779247729216388614039 1264168871593824582921059)
        ·
          refine ⟨1896253307390736874381589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264168871593824582921059 1896253307390736874381589)
          ·
            refine ⟨88886873783940790986637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1896253307390736874381589 88886873783940790986637)
            ·
              refine ⟨33332577668977796619989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88886873783940790986637 33332577668977796619989)
              ·
                refine ⟨781232289116667108281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33332577668977796619989 781232289116667108281)
                ·
                  rfl

theorem cell23_41079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 7].length) (baseStart_41079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41079 prefixEnd_41079 := by exact prefixLift 41079
  have htrace : WordTrace (prefixWord ++ tailWord_41079) baseStart_41079 baseEnd_41079 := by
    simpa [prefixWord, tailWord_41079, baseEnd_41079] using wordTrace_append hprefix tailTrace_41079
  have hstable : (prefixWord ++ tailWord_41079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41079).length < 2 ^ (prefixWord ++ tailWord_41079).sum := by decide
  have hdescent : baseEnd_41079 < baseStart_41079 := by decide
  rcases family_descends (prefixWord ++ tailWord_41079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41093 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 1, 2, 3]
def baseStart_41093 : Nat := 118140960795 + 41093 * 2 ^ 59
def prefixEnd_41093 : Nat := 4983230072969 + 3 ^ 40 * 41093 * 2
def baseEnd_41093 : Nat := 21100460535312957148523

theorem tailTrace_41093 : CollatzResearch.WordTrace tailWord_41093 prefixEnd_41093 21100460535312957148523 := by
  unfold tailWord_41093
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498784840134553970767933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 999189893423035980511955 1498784840134553970767933)
  ·
    refine ⟨562044315050457739037975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1498784840134553970767933 562044315050457739037975)
    ·
      refine ⟨843066472575686608556963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 562044315050457739037975 843066472575686608556963)
      ·
        refine ⟨1264599708863529912835445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843066472575686608556963 1264599708863529912835445)
        ·
          refine ⟨118556222705955929328323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1264599708863529912835445 118556222705955929328323)
          ·
            refine ⟨177834334058933893992485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118556222705955929328323 177834334058933893992485)
            ·
              refine ⟨33343937636050105123591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177834334058933893992485 33343937636050105123591)
              ·
                refine ⟨50015906454075157685387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33343937636050105123591 50015906454075157685387)
                ·
                  refine ⟨75023859681112736528081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50015906454075157685387 75023859681112736528081)
                  ·
                    refine ⟨56267894760834552396061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75023859681112736528081 56267894760834552396061)
                    ·
                      refine ⟨21100460535312957148523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 56267894760834552396061 21100460535312957148523)
                      ·
                        rfl

theorem cell23_41093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_41093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41093 prefixEnd_41093 := by exact prefixLift 41093
  have htrace : WordTrace (prefixWord ++ tailWord_41093) baseStart_41093 baseEnd_41093 := by
    simpa [prefixWord, tailWord_41093, baseEnd_41093] using wordTrace_append hprefix tailTrace_41093
  have hstable : (prefixWord ++ tailWord_41093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41093).length < 2 ^ (prefixWord ++ tailWord_41093).sum := by decide
  have hdescent : baseEnd_41093 < baseStart_41093 := by decide
  rcases family_descends (prefixWord ++ tailWord_41093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41130 : List Nat := [3, 1, 5, 1, 3, 1, 2, 7]
def baseStart_41130 : Nat := 118140960795 + 41130 * 2 ^ 59
def prefixEnd_41130 : Nat := 4983230072969 + 3 ^ 40 * 41130 * 2
def baseEnd_41130 : Nat := 782202197019604162439

theorem tailTrace_41130 : CollatzResearch.WordTrace tailWord_41130 prefixEnd_41130 782202197019604162439 := by
  unfold tailWord_41130
  simp only [CollatzResearch.WordTrace]
  refine ⟨375033585250127322466211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1000089560667006193243229 375033585250127322466211)
  ·
    refine ⟨562550377875190983699317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 375033585250127322466211 562550377875190983699317)
    ·
      refine ⟨52739097925799154721811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 562550377875190983699317 52739097925799154721811)
      ·
        refine ⟨79108646888698732082717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52739097925799154721811 79108646888698732082717)
        ·
          refine ⟨29665742583262024531019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79108646888698732082717 29665742583262024531019)
          ·
            refine ⟨44498613874893036796529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29665742583262024531019 44498613874893036796529)
            ·
              refine ⟨33373960406169777597397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44498613874893036796529 33373960406169777597397)
              ·
                refine ⟨782202197019604162439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33373960406169777597397 782202197019604162439)
                ·
                  rfl

theorem cell23_41130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 7].length) (baseStart_41130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41130 prefixEnd_41130 := by exact prefixLift 41130
  have htrace : WordTrace (prefixWord ++ tailWord_41130) baseStart_41130 baseEnd_41130 := by
    simpa [prefixWord, tailWord_41130, baseEnd_41130] using wordTrace_append hprefix tailTrace_41130
  have hstable : (prefixWord ++ tailWord_41130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41130).length < 2 ^ (prefixWord ++ tailWord_41130).sum := by decide
  have hdescent : baseEnd_41130 < baseStart_41130 := by decide
  rcases family_descends (prefixWord ++ tailWord_41130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41141 : List Nat := [1, 3, 3, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_41141 : Nat := 118140960795 + 41141 * 2 ^ 59
def prefixEnd_41141 : Nat := 4983230072969 + 3 ^ 40 * 41141 * 2
def baseEnd_41141 : Nat := 21125107606728769348303

theorem tailTrace_41141 : CollatzResearch.WordTrace tailWord_41141 prefixEnd_41141 21125107606728769348303 := by
  unfold tailWord_41141
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500535543960658168515277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1000357029307105445676851 1500535543960658168515277)
  ·
    refine ⟨562700828985246813193229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1500535543960658168515277 562700828985246813193229)
    ·
      refine ⟨211012810869467554947461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 562700828985246813193229 211012810869467554947461)
      ·
        refine ⟨39564902038025166552649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211012810869467554947461 39564902038025166552649)
        ·
          refine ⟨29673676528518874914487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39564902038025166552649 29673676528518874914487)
          ·
            refine ⟨44510514792778312371731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29673676528518874914487 44510514792778312371731)
            ·
              refine ⟨66765772189167468557597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44510514792778312371731 66765772189167468557597)
              ·
                refine ⟨25037164570937800709099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66765772189167468557597 25037164570937800709099)
                ·
                  refine ⟨37555746856406701063649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25037164570937800709099 37555746856406701063649)
                  ·
                    refine ⟨28166810142305025797737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37555746856406701063649 28166810142305025797737)
                    ·
                      refine ⟨21125107606728769348303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28166810142305025797737 21125107606728769348303)
                      ·
                        rfl

theorem cell23_41141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_41141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41141 prefixEnd_41141 := by exact prefixLift 41141
  have htrace : WordTrace (prefixWord ++ tailWord_41141) baseStart_41141 baseEnd_41141 := by
    simpa [prefixWord, tailWord_41141, baseEnd_41141] using wordTrace_append hprefix tailTrace_41141
  have hstable : (prefixWord ++ tailWord_41141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41141).length < 2 ^ (prefixWord ++ tailWord_41141).sum := by decide
  have hdescent : baseEnd_41141 < baseStart_41141 := by decide
  rcases family_descends (prefixWord ++ tailWord_41141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41146 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2]
def baseStart_41146 : Nat := 118140960795 + 41146 * 2 ^ 59
def prefixEnd_41146 : Nat := 4983230072969 + 3 ^ 40 * 41146 * 2
def baseEnd_41146 : Nat := 21127675010001249785779

theorem tailTrace_41146 : CollatzResearch.WordTrace tailWord_41146 prefixEnd_41146 21127675010001249785779 := by
  unfold tailWord_41146
  simp only [CollatzResearch.WordTrace]
  refine ⟨375179477235636005611823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1000478605961696014964861 375179477235636005611823)
  ·
    refine ⟨562769215853454008417735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 375179477235636005611823 562769215853454008417735)
    ·
      refine ⟨844153823780181012626603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 562769215853454008417735 844153823780181012626603)
      ·
        refine ⟨1266230735670271518939905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844153823780181012626603 1266230735670271518939905)
        ·
          refine ⟨949673051752703639204929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1266230735670271518939905 949673051752703639204929)
          ·
            refine ⟨712254788814527729403697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 949673051752703639204929 712254788814527729403697)
            ·
              refine ⟨534191091610895797052773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712254788814527729403697 534191091610895797052773)
              ·
                refine ⟨100160829677042961947395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 534191091610895797052773 100160829677042961947395)
                ·
                  refine ⟨150241244515564442921093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100160829677042961947395 150241244515564442921093)
                  ·
                    refine ⟨28170233346668333047705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150241244515564442921093 28170233346668333047705)
                    ·
                      refine ⟨21127675010001249785779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28170233346668333047705 21127675010001249785779)
                      ·
                        rfl

theorem cell23_41146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_41146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41146 prefixEnd_41146 := by exact prefixLift 41146
  have htrace : WordTrace (prefixWord ++ tailWord_41146) baseStart_41146 baseEnd_41146 := by
    simpa [prefixWord, tailWord_41146, baseEnd_41146] using wordTrace_append hprefix tailTrace_41146
  have hstable : (prefixWord ++ tailWord_41146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41146).length < 2 ^ (prefixWord ++ tailWord_41146).sum := by decide
  have hdescent : baseEnd_41146 < baseStart_41146 := by decide
  rcases family_descends (prefixWord ++ tailWord_41146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41149 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_41149 : Nat := 118140960795 + 41149 * 2 ^ 59
def prefixEnd_41149 : Nat := 4983230072969 + 3 ^ 40 * 41149 * 2
def baseEnd_41149 : Nat := 21129215451964738048265

theorem tailTrace_41149 : CollatzResearch.WordTrace tailWord_41149 prefixEnd_41149 21129215451964738048265 := by
  unfold tailWord_41149
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500827327931675534806501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1000551551954450356537667 1500827327931675534806501)
  ·
    refine ⟨281405123987189162776219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1500827327931675534806501 281405123987189162776219)
    ·
      refine ⟨422107685980783744164329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281405123987189162776219 422107685980783744164329)
      ·
        refine ⟨316580764485587808123247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422107685980783744164329 316580764485587808123247)
        ·
          refine ⟨474871146728381712184871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316580764485587808123247 474871146728381712184871)
          ·
            refine ⟨712306720092572568277307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474871146728381712184871 712306720092572568277307)
            ·
              refine ⟨1068460080138858852415961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712306720092572568277307 1068460080138858852415961)
              ·
                refine ⟨801345060104144139311971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068460080138858852415961 801345060104144139311971)
                ·
                  refine ⟨1202017590156216208967957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801345060104144139311971 1202017590156216208967957)
                  ·
                    refine ⟨56344574538572634795373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1202017590156216208967957 56344574538572634795373)
                    ·
                      refine ⟨21129215451964738048265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 56344574538572634795373 21129215451964738048265)
                      ·
                        rfl

theorem cell23_41149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_41149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41149 prefixEnd_41149 := by exact prefixLift 41149
  have htrace : WordTrace (prefixWord ++ tailWord_41149) baseStart_41149 baseEnd_41149 := by
    simpa [prefixWord, tailWord_41149, baseEnd_41149] using wordTrace_append hprefix tailTrace_41149
  have hstable : (prefixWord ++ tailWord_41149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41149).length < 2 ^ (prefixWord ++ tailWord_41149).sum := by decide
  have hdescent : baseEnd_41149 < baseStart_41149 := by decide
  rcases family_descends (prefixWord ++ tailWord_41149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41163 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 2, 2, 2]
def baseStart_41163 : Nat := 118140960795 + 41163 * 2 ^ 59
def prefixEnd_41163 : Nat := 4983230072969 + 3 ^ 40 * 41163 * 2
def baseEnd_41163 : Nat := 21136404181127683273201

theorem tailTrace_41163 : CollatzResearch.WordTrace tailWord_41163 prefixEnd_41163 21136404181127683273201 := by
  unfold tailWord_41163
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501337949880955925816143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1000891966587303950544095 1501337949880955925816143)
  ·
    refine ⟨2252006924821433888724215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1501337949880955925816143 2252006924821433888724215)
    ·
      refine ⟨3378010387232150833086323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2252006924821433888724215 3378010387232150833086323)
      ·
        refine ⟨5067015580848226249629485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3378010387232150833086323 5067015580848226249629485)
        ·
          refine ⟨1900130842818084843611057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5067015580848226249629485 1900130842818084843611057)
          ·
            refine ⟨1425098132113563632708293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1900130842818084843611057 1425098132113563632708293)
            ·
              refine ⟨267205899771293181132805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1425098132113563632708293 267205899771293181132805)
              ·
                refine ⟨50101106207117471462401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 267205899771293181132805 50101106207117471462401)
                ·
                  refine ⟨37575829655338103596801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50101106207117471462401 37575829655338103596801)
                  ·
                    refine ⟨28181872241503577697601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37575829655338103596801 28181872241503577697601)
                    ·
                      refine ⟨21136404181127683273201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28181872241503577697601 21136404181127683273201)
                      ·
                        rfl

theorem cell23_41163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 2, 2].length) (baseStart_41163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41163 prefixEnd_41163 := by exact prefixLift 41163
  have htrace : WordTrace (prefixWord ++ tailWord_41163) baseStart_41163 baseEnd_41163 := by
    simpa [prefixWord, tailWord_41163, baseEnd_41163] using wordTrace_append hprefix tailTrace_41163
  have hstable : (prefixWord ++ tailWord_41163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41163).length < 2 ^ (prefixWord ++ tailWord_41163).sum := by decide
  have hdescent : baseEnd_41163 < baseStart_41163 := by decide
  rcases family_descends (prefixWord ++ tailWord_41163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41169 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 7]
def baseStart_41169 : Nat := 118140960795 + 41169 * 2 ^ 59
def prefixEnd_41169 : Nat := 4983230072969 + 3 ^ 40 * 41169 * 2
def baseEnd_41169 : Nat := 2348831673894962199797

theorem tailTrace_41169 : CollatzResearch.WordTrace tailWord_41169 prefixEnd_41169 2348831673894962199797 := by
  unfold tailWord_41169
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501556787859218950534561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1001037858572812633689707 1501556787859218950534561)
  ·
    refine ⟨1126167590894414212900921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1501556787859218950534561 1126167590894414212900921)
    ·
      refine ⟨844625693170810659675691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1126167590894414212900921 844625693170810659675691)
      ·
        refine ⟨1266938539756215989513537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844625693170810659675691 1266938539756215989513537)
        ·
          refine ⟨950203904817161992135153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1266938539756215989513537 950203904817161992135153)
          ·
            refine ⟨712652928612871494101365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950203904817161992135153 712652928612871494101365)
            ·
              refine ⟨66811212057456702572003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 712652928612871494101365 66811212057456702572003)
              ·
                refine ⟨100216818086185053858005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66811212057456702572003 100216818086185053858005)
                ·
                  refine ⟨2348831673894962199797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 100216818086185053858005 2348831673894962199797)
                  ·
                    rfl

theorem cell23_41169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 7].length) (baseStart_41169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41169 prefixEnd_41169 := by exact prefixLift 41169
  have htrace : WordTrace (prefixWord ++ tailWord_41169) baseStart_41169 baseEnd_41169 := by
    simpa [prefixWord, tailWord_41169, baseEnd_41169] using wordTrace_append hprefix tailTrace_41169
  have hstable : (prefixWord ++ tailWord_41169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41169).length < 2 ^ (prefixWord ++ tailWord_41169).sum := by decide
  have hdescent : baseEnd_41169 < baseStart_41169 := by decide
  rcases family_descends (prefixWord ++ tailWord_41169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41174 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_41174 : Nat := 118140960795 + 41174 * 2 ^ 59
def prefixEnd_41174 : Nat := 4983230072969 + 3 ^ 40 * 41174 * 2
def baseEnd_41174 : Nat := 21142052468327140235651

theorem tailTrace_41174 : CollatzResearch.WordTrace tailWord_41174 prefixEnd_41174 21142052468327140235651 := by
  unfold tailWord_41174
  simp only [CollatzResearch.WordTrace]
  refine ⟨93858697052569050279161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1001159435227403202977717 93858697052569050279161)
  ·
    refine ⟨70394022789426787709371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93858697052569050279161 70394022789426787709371)
    ·
      refine ⟨105591034184140181564057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70394022789426787709371 105591034184140181564057)
      ·
        refine ⟨79193275638105136173043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105591034184140181564057 79193275638105136173043)
        ·
          refine ⟨118789913457157704259565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79193275638105136173043 118789913457157704259565)
          ·
            refine ⟨44546217546434139097337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118789913457157704259565 44546217546434139097337)
            ·
              refine ⟨33409663159825604323003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44546217546434139097337 33409663159825604323003)
              ·
                refine ⟨50114494739738406484505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33409663159825604323003 50114494739738406484505)
                ·
                  refine ⟨37585871054803804863379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50114494739738406484505 37585871054803804863379)
                  ·
                    refine ⟨56378806582205707295069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37585871054803804863379 56378806582205707295069)
                    ·
                      refine ⟨21142052468327140235651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 56378806582205707295069 21142052468327140235651)
                      ·
                        rfl

theorem cell23_41174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_41174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41174 prefixEnd_41174 := by exact prefixLift 41174
  have htrace : WordTrace (prefixWord ++ tailWord_41174) baseStart_41174 baseEnd_41174 := by
    simpa [prefixWord, tailWord_41174, baseEnd_41174] using wordTrace_append hprefix tailTrace_41174
  have hstable : (prefixWord ++ tailWord_41174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41174).length < 2 ^ (prefixWord ++ tailWord_41174).sum := by decide
  have hdescent : baseEnd_41174 < baseStart_41174 := by decide
  rcases family_descends (prefixWord ++ tailWord_41174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41263 : List Nat := [1, 1, 2, 1, 2, 1, 5, 5, 1, 4]
def baseStart_41263 : Nat := 118140960795 + 41263 * 2 ^ 59
def prefixEnd_41263 : Nat := 4983230072969 + 3 ^ 40 * 41263 * 2
def baseEnd_41263 : Nat := 7062584082192430674247

theorem tailTrace_41263 : CollatzResearch.WordTrace tailWord_41263 prefixEnd_41263 7062584082192430674247 := by
  unfold tailWord_41263
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504985249518673004456443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1003323499679115336304295 1504985249518673004456443)
  ·
    refine ⟨2257477874278009506684665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1504985249518673004456443 2257477874278009506684665)
    ·
      refine ⟨1693108405708507130013499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2257477874278009506684665 1693108405708507130013499)
      ·
        refine ⟨2539662608562760695020249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1693108405708507130013499 2539662608562760695020249)
        ·
          refine ⟨1904746956422070521265187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2539662608562760695020249 1904746956422070521265187)
          ·
            refine ⟨2857120434633105781897781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904746956422070521265187 2857120434633105781897781)
            ·
              refine ⟨267855040746853667052917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2857120434633105781897781 267855040746853667052917)
              ·
                refine ⟨25111410070017531286211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 267855040746853667052917 25111410070017531286211)
                ·
                  refine ⟨37667115105026296929317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25111410070017531286211 37667115105026296929317)
                  ·
                    refine ⟨7062584082192430674247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37667115105026296929317 7062584082192430674247)
                    ·
                      rfl

theorem cell23_41263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 1, 4].length) (baseStart_41263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41263 prefixEnd_41263 := by exact prefixLift 41263
  have htrace : WordTrace (prefixWord ++ tailWord_41263) baseStart_41263 baseEnd_41263 := by
    simpa [prefixWord, tailWord_41263, baseEnd_41263] using wordTrace_append hprefix tailTrace_41263
  have hstable : (prefixWord ++ tailWord_41263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41263).length < 2 ^ (prefixWord ++ tailWord_41263).sum := by decide
  have hdescent : baseEnd_41263 < baseStart_41263 := by decide
  rcases family_descends (prefixWord ++ tailWord_41263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41279 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_41279 : Nat := 118140960795 + 41279 * 2 ^ 59
def prefixEnd_41279 : Nat := 4983230072969 + 3 ^ 40 * 41279 * 2
def baseEnd_41279 : Nat := 21195967937049229422667

theorem tailTrace_41279 : CollatzResearch.WordTrace tailWord_41279 prefixEnd_41279 21195967937049229422667 := by
  unfold tailWord_41279
  simp only [CollatzResearch.WordTrace]
  refine ⟨1505568817460707737038891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1003712544973805158025927 1505568817460707737038891)
  ·
    refine ⟨2258353226191061605558337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1505568817460707737038891 2258353226191061605558337)
    ·
      refine ⟨1693764919643296204168753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2258353226191061605558337 1693764919643296204168753)
      ·
        refine ⟨1270323689732472153126565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1693764919643296204168753 1270323689732472153126565)
        ·
          refine ⟨238185691824838528711231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1270323689732472153126565 238185691824838528711231)
          ·
            refine ⟨357278537737257793066847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238185691824838528711231 357278537737257793066847)
            ·
              refine ⟨535917806605886689600271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357278537737257793066847 535917806605886689600271)
              ·
                refine ⟨803876709908830034400407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535917806605886689600271 803876709908830034400407)
                ·
                  refine ⟨1205815064863245051600611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803876709908830034400407 1205815064863245051600611)
                  ·
                    refine ⟨1808722597294867577400917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1205815064863245051600611 1808722597294867577400917)
                    ·
                      refine ⟨21195967937049229422667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 1808722597294867577400917 21195967937049229422667)
                      ·
                        rfl

theorem cell23_41279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_41279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41279 prefixEnd_41279 := by exact prefixLift 41279
  have htrace : WordTrace (prefixWord ++ tailWord_41279) baseStart_41279 baseEnd_41279 := by
    simpa [prefixWord, tailWord_41279, baseEnd_41279] using wordTrace_append hprefix tailTrace_41279
  have hstable : (prefixWord ++ tailWord_41279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41279).length < 2 ^ (prefixWord ++ tailWord_41279).sum := by decide
  have hdescent : baseEnd_41279 < baseStart_41279 := by decide
  rcases family_descends (prefixWord ++ tailWord_41279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41303 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 3, 1, 3]
def baseStart_41303 : Nat := 118140960795 + 41303 * 2 ^ 59
def prefixEnd_41303 : Nat := 4983230072969 + 3 ^ 40 * 41303 * 2
def baseEnd_41303 : Nat := 21208291472757135522557

theorem tailTrace_41303 : CollatzResearch.WordTrace tailWord_41303 prefixEnd_41303 21208291472757135522557 := by
  unfold tailWord_41303
  simp only [CollatzResearch.WordTrace]
  refine ⟨1506444169373759835912563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1004296112915839890608375 1506444169373759835912563)
  ·
    refine ⟨2259666254060639753868845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1506444169373759835912563 2259666254060639753868845)
    ·
      refine ⟨847374845272739907700817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2259666254060639753868845 847374845272739907700817)
      ·
        refine ⟨635531133954554930775613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 847374845272739907700817 635531133954554930775613)
        ·
          refine ⟨238324175232958099040855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 635531133954554930775613 238324175232958099040855)
          ·
            refine ⟨357486262849437148561283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238324175232958099040855 357486262849437148561283)
            ·
              refine ⟨536229394274155722841925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357486262849437148561283 536229394274155722841925)
              ·
                refine ⟨100543011426404198032861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 536229394274155722841925 100543011426404198032861)
                ·
                  refine ⟨37703629284901574262323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100543011426404198032861 37703629284901574262323)
                  ·
                    refine ⟨56555443927352361393485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37703629284901574262323 56555443927352361393485)
                    ·
                      refine ⟨21208291472757135522557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 56555443927352361393485 21208291472757135522557)
                      ·
                        rfl

theorem cell23_41303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_41303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41303 prefixEnd_41303 := by exact prefixLift 41303
  have htrace : WordTrace (prefixWord ++ tailWord_41303) baseStart_41303 baseEnd_41303 := by
    simpa [prefixWord, tailWord_41303, baseEnd_41303] using wordTrace_append hprefix tailTrace_41303
  have hstable : (prefixWord ++ tailWord_41303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41303).length < 2 ^ (prefixWord ++ tailWord_41303).sum := by decide
  have hdescent : baseEnd_41303 < baseStart_41303 := by decide
  rcases family_descends (prefixWord ++ tailWord_41303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41330 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 2, 3, 2]
def baseStart_41330 : Nat := 118140960795 + 41330 * 2 ^ 59
def prefixEnd_41330 : Nat := 4983230072969 + 3 ^ 40 * 41330 * 2
def baseEnd_41330 : Nat := 21222155450428529884933

theorem tailTrace_41330 : CollatzResearch.WordTrace tailWord_41330 prefixEnd_41330 21222155450428529884933 := by
  unfold tailWord_41330
  simp only [CollatzResearch.WordTrace]
  refine ⟨376857235068985861786361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1004952626850628964763629 376857235068985861786361)
  ·
    refine ⟨282642926301739396339771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 376857235068985861786361 282642926301739396339771)
    ·
      refine ⟨423964389452609094509657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282642926301739396339771 423964389452609094509657)
      ·
        refine ⟨317973292089456820882243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423964389452609094509657 317973292089456820882243)
        ·
          refine ⟨476959938134185231323365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317973292089456820882243 476959938134185231323365)
          ·
            refine ⟨89429988400159730873131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 476959938134185231323365 89429988400159730873131)
            ·
              refine ⟨134144982600239596309697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89429988400159730873131 134144982600239596309697)
              ·
                refine ⟨100608736950179697232273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134144982600239596309697 100608736950179697232273)
                ·
                  refine ⟨75456552712634772924205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100608736950179697232273 75456552712634772924205)
                  ·
                    refine ⟨28296207267238039846577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75456552712634772924205 28296207267238039846577)
                    ·
                      refine ⟨21222155450428529884933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28296207267238039846577 21222155450428529884933)
                      ·
                        rfl

theorem cell23_41330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_41330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41330 prefixEnd_41330 := by exact prefixLift 41330
  have htrace : WordTrace (prefixWord ++ tailWord_41330) baseStart_41330 baseEnd_41330 := by
    simpa [prefixWord, tailWord_41330, baseEnd_41330] using wordTrace_append hprefix tailTrace_41330
  have hstable : (prefixWord ++ tailWord_41330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41330).length < 2 ^ (prefixWord ++ tailWord_41330).sum := by decide
  have hdescent : baseEnd_41330 < baseStart_41330 := by decide
  rcases family_descends (prefixWord ++ tailWord_41330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41356 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_41356 : Nat := 118140960795 + 41356 * 2 ^ 59
def prefixEnd_41356 : Nat := 4983230072969 + 3 ^ 40 * 41356 * 2
def baseEnd_41356 : Nat := 21235505947445428159813

theorem tailTrace_41356 : CollatzResearch.WordTrace tailWord_41356 prefixEnd_41356 21235505947445428159813 := by
  unfold tailWord_41356
  simp only [CollatzResearch.WordTrace]
  refine ⟨754188619090874943795961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1005584825454499925061281 754188619090874943795961)
  ·
    refine ⟨565641464318156207846971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 754188619090874943795961 565641464318156207846971)
    ·
      refine ⟨848462196477234311770457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565641464318156207846971 848462196477234311770457)
      ·
        refine ⟨636346647357925733827843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 848462196477234311770457 636346647357925733827843)
        ·
          refine ⟨954519971036888600741765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636346647357925733827843 954519971036888600741765)
          ·
            refine ⟨178972494569416612639081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 954519971036888600741765 178972494569416612639081)
            ·
              refine ⟨134229370927062459479311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178972494569416612639081 134229370927062459479311)
              ·
                refine ⟨201344056390593689218967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134229370927062459479311 201344056390593689218967)
                ·
                  refine ⟨302016084585890533828451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201344056390593689218967 302016084585890533828451)
                  ·
                    refine ⟨453024126878835800742677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 302016084585890533828451 453024126878835800742677)
                    ·
                      refine ⟨21235505947445428159813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 453024126878835800742677 21235505947445428159813)
                      ·
                        rfl

theorem cell23_41356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_41356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41356 prefixEnd_41356 := by exact prefixLift 41356
  have htrace : WordTrace (prefixWord ++ tailWord_41356) baseStart_41356 baseEnd_41356 := by
    simpa [prefixWord, tailWord_41356, baseEnd_41356] using wordTrace_append hprefix tailTrace_41356
  have hstable : (prefixWord ++ tailWord_41356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41356).length < 2 ^ (prefixWord ++ tailWord_41356).sum := by decide
  have hdescent : baseEnd_41356 < baseStart_41356 := by decide
  rcases family_descends (prefixWord ++ tailWord_41356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41437 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_41437 : Nat := 118140960795 + 41437 * 2 ^ 59
def prefixEnd_41437 : Nat := 4983230072969 + 3 ^ 40 * 41437 * 2
def baseEnd_41437 : Nat := 21277097880459611246941

theorem tailTrace_41437 : CollatzResearch.WordTrace tailWord_41437 prefixEnd_41437 21277097880459611246941 := by
  unfold tailWord_41437
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511331550888300721290565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1007554367258867147527043 1511331550888300721290565)
  ·
    refine ⟨283374665791556385241981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1511331550888300721290565 283374665791556385241981)
    ·
      refine ⟨106265499671833644465743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283374665791556385241981 106265499671833644465743)
      ·
        refine ⟨159398249507750466698615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106265499671833644465743 159398249507750466698615)
        ·
          refine ⟨239097374261625700047923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159398249507750466698615 239097374261625700047923)
          ·
            refine ⟨358646061392438550071885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239097374261625700047923 358646061392438550071885)
            ·
              refine ⟨134492273022164456276957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358646061392438550071885 134492273022164456276957)
              ·
                refine ⟨50434602383311671103859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134492273022164456276957 50434602383311671103859)
                ·
                  refine ⟨75651903574967506655789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50434602383311671103859 75651903574967506655789)
                  ·
                    refine ⟨28369463840612814995921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75651903574967506655789 28369463840612814995921)
                    ·
                      refine ⟨21277097880459611246941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28369463840612814995921 21277097880459611246941)
                      ·
                        rfl

theorem cell23_41437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_41437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41437 prefixEnd_41437 := by exact prefixLift 41437
  have htrace : WordTrace (prefixWord ++ tailWord_41437) baseStart_41437 baseEnd_41437 := by
    simpa [prefixWord, tailWord_41437, baseEnd_41437] using wordTrace_append hprefix tailTrace_41437
  have hstable : (prefixWord ++ tailWord_41437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41437).length < 2 ^ (prefixWord ++ tailWord_41437).sum := by decide
  have hdescent : baseEnd_41437 < baseStart_41437 := by decide
  rcases family_descends (prefixWord ++ tailWord_41437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41461 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_41461 : Nat := 118140960795 + 41461 * 2 ^ 59
def prefixEnd_41461 : Nat := 4983230072969 + 3 ^ 40 * 41461 * 2
def baseEnd_41461 : Nat := 21289421416167517346831

theorem tailTrace_41461 : CollatzResearch.WordTrace tailWord_41461 prefixEnd_41461 21289421416167517346831 := by
  unfold tailWord_41461
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512206902801352820164237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1008137935200901880109491 1512206902801352820164237)
  ·
    refine ⟨567077588550507307561589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1512206902801352820164237 567077588550507307561589)
    ·
      refine ⟨53163523926610060083899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 567077588550507307561589 53163523926610060083899)
      ·
        refine ⟨79745285889915090125849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53163523926610060083899 79745285889915090125849)
        ·
          refine ⟨59808964417436317594387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79745285889915090125849 59808964417436317594387)
          ·
            refine ⟨89713446626154476391581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59808964417436317594387 89713446626154476391581)
            ·
              refine ⟨33642542484807928646843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89713446626154476391581 33642542484807928646843)
              ·
                refine ⟨50463813727211892970265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33642542484807928646843 50463813727211892970265)
                ·
                  refine ⟨37847860295408919727699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50463813727211892970265 37847860295408919727699)
                  ·
                    refine ⟨56771790443113379591549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37847860295408919727699 56771790443113379591549)
                    ·
                      refine ⟨21289421416167517346831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 56771790443113379591549 21289421416167517346831)
                      ·
                        rfl

theorem cell23_41461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_41461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41461 prefixEnd_41461 := by exact prefixLift 41461
  have htrace : WordTrace (prefixWord ++ tailWord_41461) baseStart_41461 baseEnd_41461 := by
    simpa [prefixWord, tailWord_41461, baseEnd_41461] using wordTrace_append hprefix tailTrace_41461
  have hstable : (prefixWord ++ tailWord_41461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41461).length < 2 ^ (prefixWord ++ tailWord_41461).sum := by decide
  have hdescent : baseEnd_41461 < baseStart_41461 := by decide
  rcases family_descends (prefixWord ++ tailWord_41461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41473 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 7]
def baseStart_41473 : Nat := 118140960795 + 41473 * 2 ^ 59
def prefixEnd_41473 : Nat := 4983230072969 + 3 ^ 40 * 41473 * 2
def baseEnd_41473 : Nat := 2366175909335718932975

theorem tailTrace_41473 : CollatzResearch.WordTrace tailWord_41473 prefixEnd_41473 2366175909335718932975 := by
  unfold tailWord_41473
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512644578757878869601073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1008429719171919246400715 1512644578757878869601073)
  ·
    refine ⟨1134483434068409152200805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1512644578757878869601073 1134483434068409152200805)
    ·
      refine ⟨212715643887826716037651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1134483434068409152200805 212715643887826716037651)
      ·
        refine ⟨319073465831740074056477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212715643887826716037651 319073465831740074056477)
        ·
          refine ⟨119652549686902527771179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319073465831740074056477 119652549686902527771179)
          ·
            refine ⟨179478824530353791656769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119652549686902527771179 179478824530353791656769)
            ·
              refine ⟨134609118397765343742577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179478824530353791656769 134609118397765343742577)
              ·
                refine ⟨100956838798324007806933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134609118397765343742577 100956838798324007806933)
                ·
                  refine ⟨2366175909335718932975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 100956838798324007806933 2366175909335718932975)
                  ·
                    rfl

theorem cell23_41473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 7].length) (baseStart_41473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41473 prefixEnd_41473 := by exact prefixLift 41473
  have htrace : WordTrace (prefixWord ++ tailWord_41473) baseStart_41473 baseEnd_41473 := by
    simpa [prefixWord, tailWord_41473, baseEnd_41473] using wordTrace_append hprefix tailTrace_41473
  have hstable : (prefixWord ++ tailWord_41473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41473).length < 2 ^ (prefixWord ++ tailWord_41473).sum := by decide
  have hdescent : baseEnd_41473 < baseStart_41473 := by decide
  rcases family_descends (prefixWord ++ tailWord_41473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41507 : List Nat := [1, 1, 1, 4, 4, 2, 3, 2, 5]
def baseStart_41507 : Nat := 118140960795 + 41507 * 2 ^ 59
def prefixEnd_41507 : Nat := 4983230072969 + 3 ^ 40 * 41507 * 2
def baseEnd_41507 : Nat := 2368115725141593041291

theorem tailTrace_41507 : CollatzResearch.WordTrace tailWord_41507 prefixEnd_41507 2368115725141593041291 := by
  unfold tailWord_41507
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513884660634702676338775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1009256440423135117559183 1513884660634702676338775)
  ·
    refine ⟨2270826990952054014508163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1513884660634702676338775 2270826990952054014508163)
    ·
      refine ⟨3406240486428081021762245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270826990952054014508163 3406240486428081021762245)
      ·
        refine ⟨638670091205265191580421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3406240486428081021762245 638670091205265191580421)
        ·
          refine ⟨119750642100987223421329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 638670091205265191580421 119750642100987223421329)
          ·
            refine ⟨89812981575740417565997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119750642100987223421329 89812981575740417565997)
            ·
              refine ⟨33679868090902656587249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89812981575740417565997 33679868090902656587249)
              ·
                refine ⟨25259901068176992440437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33679868090902656587249 25259901068176992440437)
                ·
                  refine ⟨2368115725141593041291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25259901068176992440437 2368115725141593041291)
                  ·
                    rfl

theorem cell23_41507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 5].length) (baseStart_41507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41507 prefixEnd_41507 := by exact prefixLift 41507
  have htrace : WordTrace (prefixWord ++ tailWord_41507) baseStart_41507 baseEnd_41507 := by
    simpa [prefixWord, tailWord_41507, baseEnd_41507] using wordTrace_append hprefix tailTrace_41507
  have hstable : (prefixWord ++ tailWord_41507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41507).length < 2 ^ (prefixWord ++ tailWord_41507).sum := by decide
  have hdescent : baseEnd_41507 < baseStart_41507 := by decide
  rcases family_descends (prefixWord ++ tailWord_41507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41518 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_41518 : Nat := 118140960795 + 41518 * 2 ^ 59
def prefixEnd_41518 : Nat := 4983230072969 + 3 ^ 40 * 41518 * 2
def baseEnd_41518 : Nat := 21318689813473794334069

theorem tailTrace_41518 : CollatzResearch.WordTrace tailWord_41518 prefixEnd_41518 21318689813473794334069 := by
  unfold tailWord_41518
  simp only [CollatzResearch.WordTrace]
  refine ⟨189285732949356444373651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1009523909063234369992805 189285732949356444373651)
  ·
    refine ⟨283928599424034666560477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189285732949356444373651 283928599424034666560477)
    ·
      refine ⟨106473224784012999960179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283928599424034666560477 106473224784012999960179)
      ·
        refine ⟨159709837176019499940269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106473224784012999960179 159709837176019499940269)
        ·
          refine ⟨59891188941007312477601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159709837176019499940269 59891188941007312477601)
          ·
            refine ⟨44918391705755484358201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59891188941007312477601 44918391705755484358201)
            ·
              refine ⟨33688793779316613268651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44918391705755484358201 33688793779316613268651)
              ·
                refine ⟨50533190668974919902977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33688793779316613268651 50533190668974919902977)
                ·
                  refine ⟨37899893001731189927233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50533190668974919902977 37899893001731189927233)
                  ·
                    refine ⟨28424919751298392445425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37899893001731189927233 28424919751298392445425)
                    ·
                      refine ⟨21318689813473794334069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28424919751298392445425 21318689813473794334069)
                      ·
                        rfl

theorem cell23_41518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_41518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41518 prefixEnd_41518 := by exact prefixLift 41518
  have htrace : WordTrace (prefixWord ++ tailWord_41518) baseStart_41518 baseEnd_41518 := by
    simpa [prefixWord, tailWord_41518, baseEnd_41518] using wordTrace_append hprefix tailTrace_41518
  have hstable : (prefixWord ++ tailWord_41518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41518).length < 2 ^ (prefixWord ++ tailWord_41518).sum := by decide
  have hdescent : baseEnd_41518 < baseStart_41518 := by decide
  rcases family_descends (prefixWord ++ tailWord_41518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41523 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 4]
def baseStart_41523 : Nat := 118140960795 + 41523 * 2 ^ 59
def prefixEnd_41523 : Nat := 4983230072969 + 3 ^ 40 * 41523 * 2
def baseEnd_41523 : Nat := 21321257216746274771545

theorem tailTrace_41523 : CollatzResearch.WordTrace tailWord_41523 prefixEnd_41523 21321257216746274771545 := by
  unfold tailWord_41523
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514468228576737408921223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1009645485717824939280815 1514468228576737408921223)
  ·
    refine ⟨2271702342865106113381835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1514468228576737408921223 2271702342865106113381835)
    ·
      refine ⟨3407553514297659170072753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2271702342865106113381835 3407553514297659170072753)
      ·
        refine ⟨2555665135723244377554565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3407553514297659170072753 2555665135723244377554565)
        ·
          refine ⟨479187212948108320791481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2555665135723244377554565 479187212948108320791481)
          ·
            refine ⟨359390409711081240593611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479187212948108320791481 359390409711081240593611)
            ·
              refine ⟨539085614566621860890417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359390409711081240593611 539085614566621860890417)
              ·
                refine ⟨404314210924966395667813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539085614566621860890417 404314210924966395667813)
                ·
                  refine ⟨75808914548431199187715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404314210924966395667813 75808914548431199187715)
                  ·
                    refine ⟨113713371822646798781573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75808914548431199187715 113713371822646798781573)
                    ·
                      refine ⟨21321257216746274771545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 113713371822646798781573 21321257216746274771545)
                      ·
                        rfl

theorem cell23_41523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_41523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41523 prefixEnd_41523 := by exact prefixLift 41523
  have htrace : WordTrace (prefixWord ++ tailWord_41523) baseStart_41523 baseEnd_41523 := by
    simpa [prefixWord, tailWord_41523, baseEnd_41523] using wordTrace_append hprefix tailTrace_41523
  have hstable : (prefixWord ++ tailWord_41523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41523).length < 2 ^ (prefixWord ++ tailWord_41523).sum := by decide
  have hdescent : baseEnd_41523 < baseStart_41523 := by decide
  rcases family_descends (prefixWord ++ tailWord_41523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41560 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 2, 2, 3]
def baseStart_41560 : Nat := 118140960795 + 41560 * 2 ^ 59
def prefixEnd_41560 : Nat := 4983230072969 + 3 ^ 40 * 41560 * 2
def baseEnd_41560 : Nat := 21340256000962630008875

theorem tailTrace_41560 : CollatzResearch.WordTrace tailWord_41560 prefixEnd_41560 21340256000962630008875 := by
  unfold tailWord_41560
  simp only [CollatzResearch.WordTrace]
  refine ⟨757908864721346364009067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1010545152961795152012089 757908864721346364009067)
  ·
    refine ⟨1136863297082019546013601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 757908864721346364009067 1136863297082019546013601)
    ·
      refine ⟨852647472811514659510201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1136863297082019546013601 852647472811514659510201)
      ·
        refine ⟨639485604608635994632651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 852647472811514659510201 639485604608635994632651)
        ·
          refine ⟨959228406912953991948977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639485604608635994632651 959228406912953991948977)
          ·
            refine ⟨719421305184715493961733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959228406912953991948977 719421305184715493961733)
            ·
              refine ⟨134891494722134155117825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 719421305184715493961733 134891494722134155117825)
              ·
                refine ⟨101168621041600616338369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134891494722134155117825 101168621041600616338369)
                ·
                  refine ⟨75876465781200462253777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101168621041600616338369 75876465781200462253777)
                  ·
                    refine ⟨56907349335900346690333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75876465781200462253777 56907349335900346690333)
                    ·
                      refine ⟨21340256000962630008875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 56907349335900346690333 21340256000962630008875)
                      ·
                        rfl

theorem cell23_41560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_41560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41560 prefixEnd_41560 := by exact prefixLift 41560
  have htrace : WordTrace (prefixWord ++ tailWord_41560) baseStart_41560 baseEnd_41560 := by
    simpa [prefixWord, tailWord_41560, baseEnd_41560] using wordTrace_append hprefix tailTrace_41560
  have hstable : (prefixWord ++ tailWord_41560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41560).length < 2 ^ (prefixWord ++ tailWord_41560).sum := by decide
  have hdescent : baseEnd_41560 < baseStart_41560 := by decide
  rcases family_descends (prefixWord ++ tailWord_41560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41624 : List Nat := [2, 1, 2, 4, 1, 1, 1, 6, 1, 1, 3]
def baseStart_41624 : Nat := 118140960795 + 41624 * 2 ^ 59
def prefixEnd_41624 : Nat := 4983230072969 + 3 ^ 40 * 41624 * 2
def baseEnd_41624 : Nat := 21373118762850379608581

theorem tailTrace_41624 : CollatzResearch.WordTrace tailWord_41624 prefixEnd_41624 21373118762850379608581 := by
  unfold tailWord_41624
  simp only [CollatzResearch.WordTrace]
  refine ⟨759076000605415829173963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1012101334140554438898617 759076000605415829173963)
  ·
    refine ⟨1138614000908123743760945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 759076000605415829173963 1138614000908123743760945)
    ·
      refine ⟨853960500681092807820709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1138614000908123743760945 853960500681092807820709)
      ·
        refine ⟨160117593877704901466383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 853960500681092807820709 160117593877704901466383)
        ·
          refine ⟨240176390816557352199575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160117593877704901466383 240176390816557352199575)
          ·
            refine ⟨360264586224836028299363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240176390816557352199575 360264586224836028299363)
            ·
              refine ⟨540396879337254042449045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360264586224836028299363 540396879337254042449045)
              ·
                refine ⟨25331103718933783239799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 540396879337254042449045 25331103718933783239799)
                ·
                  refine ⟨37996655578400674859699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25331103718933783239799 37996655578400674859699)
                  ·
                    refine ⟨56994983367601012289549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37996655578400674859699 56994983367601012289549)
                    ·
                      refine ⟨21373118762850379608581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 56994983367601012289549 21373118762850379608581)
                      ·
                        rfl

theorem cell23_41624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_41624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41624 prefixEnd_41624 := by exact prefixLift 41624
  have htrace : WordTrace (prefixWord ++ tailWord_41624) baseStart_41624 baseEnd_41624 := by
    simpa [prefixWord, tailWord_41624, baseEnd_41624] using wordTrace_append hprefix tailTrace_41624
  have hstable : (prefixWord ++ tailWord_41624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41624).length < 2 ^ (prefixWord ++ tailWord_41624).sum := by decide
  have hdescent : baseEnd_41624 < baseStart_41624 := by decide
  rcases family_descends (prefixWord ++ tailWord_41624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41647 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 4]
def baseStart_41647 : Nat := 118140960795 + 41647 * 2 ^ 59
def prefixEnd_41647 : Nat := 4983230072969 + 3 ^ 40 * 41647 * 2
def baseEnd_41647 : Nat := 21384928817903789620975

theorem tailTrace_41647 : CollatzResearch.WordTrace tailWord_41647 prefixEnd_41647 21384928817903789620975 := by
  unfold tailWord_41647
  simp only [CollatzResearch.WordTrace]
  refine ⟨1518990880127506586435195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1012660586751671057623463 1518990880127506586435195)
  ·
    refine ⟨2278486320191259879652793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1518990880127506586435195 2278486320191259879652793)
    ·
      refine ⟨1708864740143444909739595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2278486320191259879652793 1708864740143444909739595)
      ·
        refine ⟨2563297110215167364609393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1708864740143444909739595 2563297110215167364609393)
        ·
          refine ⟨1922472832661375523457045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2563297110215167364609393 1922472832661375523457045)
          ·
            refine ⟨90115914031001977662049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1922472832661375523457045 90115914031001977662049)
            ·
              refine ⟨67586935523251483246537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90115914031001977662049 67586935523251483246537)
              ·
                refine ⟨50690201642438612434903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67586935523251483246537 50690201642438612434903)
                ·
                  refine ⟨76035302463657918652355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50690201642438612434903 76035302463657918652355)
                  ·
                    refine ⟨114052953695486877978533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76035302463657918652355 114052953695486877978533)
                    ·
                      refine ⟨21384928817903789620975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 114052953695486877978533 21384928817903789620975)
                      ·
                        rfl

theorem cell23_41647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 4].length) (baseStart_41647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41647 prefixEnd_41647 := by exact prefixLift 41647
  have htrace : WordTrace (prefixWord ++ tailWord_41647) baseStart_41647 baseEnd_41647 := by
    simpa [prefixWord, tailWord_41647, baseEnd_41647] using wordTrace_append hprefix tailTrace_41647
  have hstable : (prefixWord ++ tailWord_41647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41647).length < 2 ^ (prefixWord ++ tailWord_41647).sum := by decide
  have hdescent : baseEnd_41647 < baseStart_41647 := by decide
  rcases family_descends (prefixWord ++ tailWord_41647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41660 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_41660 : Nat := 118140960795 + 41660 * 2 ^ 59
def prefixEnd_41660 : Nat := 4983230072969 + 3 ^ 40 * 41660 * 2
def baseEnd_41660 : Nat := 21391604066412238758415

theorem tailTrace_41660 : CollatzResearch.WordTrace tailWord_41660 prefixEnd_41660 21391604066412238758415 := by
  unfold tailWord_41660
  simp only [CollatzResearch.WordTrace]
  refine ⟨759732514540204903329217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1012976686053606537772289 759732514540204903329217)
  ·
    refine ⟨569799385905153677496913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 759732514540204903329217 569799385905153677496913)
    ·
      refine ⟨427349539428865258122685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 569799385905153677496913 427349539428865258122685)
      ·
        refine ⟨160256077285824471796007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 427349539428865258122685 160256077285824471796007)
        ·
          refine ⟨240384115928736707694011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160256077285824471796007 240384115928736707694011)
          ·
            refine ⟨360576173893105061541017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240384115928736707694011 360576173893105061541017)
            ·
              refine ⟨270432130419828796155763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360576173893105061541017 270432130419828796155763)
              ·
                refine ⟨405648195629743194233645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270432130419828796155763 405648195629743194233645)
                ·
                  refine ⟨152118073361153697837617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405648195629743194233645 152118073361153697837617)
                  ·
                    refine ⟨114088555020865273378213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152118073361153697837617 114088555020865273378213)
                    ·
                      refine ⟨21391604066412238758415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 114088555020865273378213 21391604066412238758415)
                      ·
                        rfl

theorem cell23_41660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_41660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41660 prefixEnd_41660 := by exact prefixLift 41660
  have htrace : WordTrace (prefixWord ++ tailWord_41660) baseStart_41660 baseEnd_41660 := by
    simpa [prefixWord, tailWord_41660, baseEnd_41660] using wordTrace_append hprefix tailTrace_41660
  have hstable : (prefixWord ++ tailWord_41660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41660).length < 2 ^ (prefixWord ++ tailWord_41660).sum := by decide
  have hdescent : baseEnd_41660 < baseStart_41660 := by decide
  rcases family_descends (prefixWord ++ tailWord_41660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41754 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2]
def baseStart_41754 : Nat := 118140960795 + 41754 * 2 ^ 59
def prefixEnd_41754 : Nat := 4983230072969 + 3 ^ 40 * 41754 * 2
def baseEnd_41754 : Nat := 21439871247934870982983

theorem tailTrace_41754 : CollatzResearch.WordTrace tailWord_41754 prefixEnd_41754 21439871247934870982983 := by
  unfold tailWord_41754
  simp only [CollatzResearch.WordTrace]
  refine ⟨380723372684965965145079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1015262327159909240386877 380723372684965965145079)
  ·
    refine ⟨571085059027448947717619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 380723372684965965145079 571085059027448947717619)
    ·
      refine ⟨856627588541173421576429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571085059027448947717619 856627588541173421576429)
      ·
        refine ⟨321235345702940033091161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 856627588541173421576429 321235345702940033091161)
        ·
          refine ⟨240926509277205024818371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321235345702940033091161 240926509277205024818371)
          ·
            refine ⟨361389763915807537227557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240926509277205024818371 361389763915807537227557)
            ·
              refine ⟨67760580734213913230167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 361389763915807537227557 67760580734213913230167)
              ·
                refine ⟨101640871101320869845251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67760580734213913230167 101640871101320869845251)
                ·
                  refine ⟨152461306651981304767877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101640871101320869845251 152461306651981304767877)
                  ·
                    refine ⟨28586494997246494643977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 152461306651981304767877 28586494997246494643977)
                    ·
                      refine ⟨21439871247934870982983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28586494997246494643977 21439871247934870982983)
                      ·
                        rfl

theorem cell23_41754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_41754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41754 prefixEnd_41754 := by exact prefixLift 41754
  have htrace : WordTrace (prefixWord ++ tailWord_41754) baseStart_41754 baseEnd_41754 := by
    simpa [prefixWord, tailWord_41754, baseEnd_41754] using wordTrace_append hprefix tailTrace_41754
  have hstable : (prefixWord ++ tailWord_41754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41754).length < 2 ^ (prefixWord ++ tailWord_41754).sum := by decide
  have hdescent : baseEnd_41754 < baseStart_41754 := by decide
  rcases family_descends (prefixWord ++ tailWord_41754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41760 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 9]
def baseStart_41760 : Nat := 118140960795 + 41760 * 2 ^ 59
def prefixEnd_41760 : Nat := 4983230072969 + 3 ^ 40 * 41760 * 2
def baseEnd_41760 : Nat := 2382550236873538611995

theorem tailTrace_41760 : CollatzResearch.WordTrace tailWord_41760 prefixEnd_41760 2382550236873538611995 := by
  unfold tailWord_41760
  simp only [CollatzResearch.WordTrace]
  refine ⟨761556164359063442649367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1015408219145417923532489 761556164359063442649367)
  ·
    refine ⟨1142334246538595163974051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 761556164359063442649367 1142334246538595163974051)
    ·
      refine ⟨1713501369807892745961077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1142334246538595163974051 1713501369807892745961077)
      ·
        refine ⟨160640753419489944933851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1713501369807892745961077 160640753419489944933851)
        ·
          refine ⟨240961130129234917400777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160640753419489944933851 240961130129234917400777)
          ·
            refine ⟨180720847596926188050583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240961130129234917400777 180720847596926188050583)
            ·
              refine ⟨271081271395389282075875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180720847596926188050583 271081271395389282075875)
              ·
                refine ⟨406621907093083923113813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271081271395389282075875 406621907093083923113813)
                ·
                  refine ⟨2382550236873538611995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 406621907093083923113813 2382550236873538611995)
                  ·
                    rfl

theorem cell23_41760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 9].length) (baseStart_41760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41760 prefixEnd_41760 := by exact prefixLift 41760
  have htrace : WordTrace (prefixWord ++ tailWord_41760) baseStart_41760 baseEnd_41760 := by
    simpa [prefixWord, tailWord_41760, baseEnd_41760] using wordTrace_append hprefix tailTrace_41760
  have hstable : (prefixWord ++ tailWord_41760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41760).length < 2 ^ (prefixWord ++ tailWord_41760).sum := by decide
  have hdescent : baseEnd_41760 < baseStart_41760 := by decide
  rcases family_descends (prefixWord ++ tailWord_41760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41797 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 2, 5, 2]
def baseStart_41797 : Nat := 118140960795 + 41797 * 2 ^ 59
def prefixEnd_41797 : Nat := 4983230072969 + 3 ^ 40 * 41797 * 2
def baseEnd_41797 : Nat := 21461950916078202745285

theorem tailTrace_41797 : CollatzResearch.WordTrace tailWord_41797 prefixEnd_41797 21461950916078202745285 := by
  unfold tailWord_41797
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524461829584082204395645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1016307886389388136263763 1524461829584082204395645)
  ·
    refine ⟨571673186094030826648367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1524461829584082204395645 571673186094030826648367)
    ·
      refine ⟨857509779141046239972551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571673186094030826648367 857509779141046239972551)
      ·
        refine ⟨1286264668711569359958827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857509779141046239972551 1286264668711569359958827)
        ·
          refine ⟨1929397003067354039938241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286264668711569359958827 1929397003067354039938241)
          ·
            refine ⟨1447047752300515529953681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1929397003067354039938241 1447047752300515529953681)
            ·
              refine ⟨1085285814225386647465261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447047752300515529953681 1085285814225386647465261)
              ·
                refine ⟨406982180334519992799473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1085285814225386647465261 406982180334519992799473)
                ·
                  refine ⟨305236635250889994599605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406982180334519992799473 305236635250889994599605)
                  ·
                    refine ⟨28615934554770936993713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 305236635250889994599605 28615934554770936993713)
                    ·
                      refine ⟨21461950916078202745285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28615934554770936993713 21461950916078202745285)
                      ·
                        rfl

theorem cell23_41797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_41797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41797 prefixEnd_41797 := by exact prefixLift 41797
  have htrace : WordTrace (prefixWord ++ tailWord_41797) baseStart_41797 baseEnd_41797 := by
    simpa [prefixWord, tailWord_41797, baseEnd_41797] using wordTrace_append hprefix tailTrace_41797
  have hstable : (prefixWord ++ tailWord_41797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41797).length < 2 ^ (prefixWord ++ tailWord_41797).sum := by decide
  have hdescent : baseEnd_41797 < baseStart_41797 := by decide
  rcases family_descends (prefixWord ++ tailWord_41797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41800 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_41800 : Nat := 118140960795 + 41800 * 2 ^ 59
def prefixEnd_41800 : Nat := 4983230072969 + 3 ^ 40 * 41800 * 2
def baseEnd_41800 : Nat := 21463491358041691007771

theorem tailTrace_41800 : CollatzResearch.WordTrace tailWord_41800 prefixEnd_41800 21463491358041691007771 := by
  unfold tailWord_41800
  simp only [CollatzResearch.WordTrace]
  refine ⟨762285624286606858377427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1016380832382142477836569 762285624286606858377427)
  ·
    refine ⟨1143428436429910287566141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 762285624286606858377427 1143428436429910287566141)
    ·
      refine ⟨428785663661216357837303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1143428436429910287566141 428785663661216357837303)
      ·
        refine ⟨643178495491824536755955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428785663661216357837303 643178495491824536755955)
        ·
          refine ⟨964767743237736805133933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643178495491824536755955 964767743237736805133933)
          ·
            refine ⟨361787903714151301925225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 964767743237736805133933 361787903714151301925225)
            ·
              refine ⟨271340927785613476443919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361787903714151301925225 271340927785613476443919)
              ·
                refine ⟨407011391678420214665879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271340927785613476443919 407011391678420214665879)
                ·
                  refine ⟨610517087517630321998819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407011391678420214665879 610517087517630321998819)
                  ·
                    refine ⟨915775631276445482998229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 610517087517630321998819 915775631276445482998229)
                    ·
                      refine ⟨21463491358041691007771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 915775631276445482998229 21463491358041691007771)
                      ·
                        rfl

theorem cell23_41800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_41800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41800 prefixEnd_41800 := by exact prefixLift 41800
  have htrace : WordTrace (prefixWord ++ tailWord_41800) baseStart_41800 baseEnd_41800 := by
    simpa [prefixWord, tailWord_41800, baseEnd_41800] using wordTrace_append hprefix tailTrace_41800
  have hstable : (prefixWord ++ tailWord_41800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41800).length < 2 ^ (prefixWord ++ tailWord_41800).sum := by decide
  have hdescent : baseEnd_41800 < baseStart_41800 := by decide
  rcases family_descends (prefixWord ++ tailWord_41800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41805 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_41805 : Nat := 118140960795 + 41805 * 2 ^ 59
def prefixEnd_41805 : Nat := 4983230072969 + 3 ^ 40 * 41805 * 2
def baseEnd_41805 : Nat := 21466058761314171445249

theorem tailTrace_41805 : CollatzResearch.WordTrace tailWord_41805 prefixEnd_41805 21466058761314171445249 := by
  unfold tailWord_41805
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524753613555099570686869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1016502409036733047124579 1524753613555099570686869)
  ·
    refine ⟨71472825635395292375947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1524753613555099570686869 71472825635395292375947)
    ·
      refine ⟨107209238453092938563921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71472825635395292375947 107209238453092938563921)
      ·
        refine ⟨80406928839819703922941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107209238453092938563921 80406928839819703922941)
        ·
          refine ⟨30152598314932388971103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80406928839819703922941 30152598314932388971103)
          ·
            refine ⟨45228897472398583456655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30152598314932388971103 45228897472398583456655)
            ·
              refine ⟨67843346208597875184983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45228897472398583456655 67843346208597875184983)
              ·
                refine ⟨101765019312896812777475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67843346208597875184983 101765019312896812777475)
                ·
                  refine ⟨152647528969345219166213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101765019312896812777475 152647528969345219166213)
                  ·
                    refine ⟨28621411681752228593665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 152647528969345219166213 28621411681752228593665)
                    ·
                      refine ⟨21466058761314171445249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28621411681752228593665 21466058761314171445249)
                      ·
                        rfl

theorem cell23_41805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_41805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41805 prefixEnd_41805 := by exact prefixLift 41805
  have htrace : WordTrace (prefixWord ++ tailWord_41805) baseStart_41805 baseEnd_41805 := by
    simpa [prefixWord, tailWord_41805, baseEnd_41805] using wordTrace_append hprefix tailTrace_41805
  have hstable : (prefixWord ++ tailWord_41805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41805).length < 2 ^ (prefixWord ++ tailWord_41805).sum := by decide
  have hdescent : baseEnd_41805 < baseStart_41805 := by decide
  rcases family_descends (prefixWord ++ tailWord_41805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41827 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 4]
def baseStart_41827 : Nat := 118140960795 + 41827 * 2 ^ 59
def prefixEnd_41827 : Nat := 4983230072969 + 3 ^ 40 * 41827 * 2
def baseEnd_41827 : Nat := 21477355335713085370147

theorem tailTrace_41827 : CollatzResearch.WordTrace tailWord_41827 prefixEnd_41827 21477355335713085370147 := by
  unfold tailWord_41827
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525556019475397327987735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1017037346316931551991823 1525556019475397327987735)
  ·
    refine ⟨2288334029213095991981603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1525556019475397327987735 2288334029213095991981603)
    ·
      refine ⟨3432501043819643987972405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288334029213095991981603 3432501043819643987972405)
      ·
        refine ⟨321796972858091623872413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3432501043819643987972405 321796972858091623872413)
        ·
          refine ⟨120673864821784358952155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321796972858091623872413 120673864821784358952155)
          ·
            refine ⟨181010797232676538428233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120673864821784358952155 181010797232676538428233)
            ·
              refine ⟨135758097924507403821175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181010797232676538428233 135758097924507403821175)
              ·
                refine ⟨203637146886761105731763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135758097924507403821175 203637146886761105731763)
                ·
                  refine ⟨305455720330141658597645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203637146886761105731763 305455720330141658597645)
                  ·
                    refine ⟨114545895123803121974117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305455720330141658597645 114545895123803121974117)
                    ·
                      refine ⟨21477355335713085370147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 114545895123803121974117 21477355335713085370147)
                      ·
                        rfl

theorem cell23_41827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_41827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41827 prefixEnd_41827 := by exact prefixLift 41827
  have htrace : WordTrace (prefixWord ++ tailWord_41827) baseStart_41827 baseEnd_41827 := by
    simpa [prefixWord, tailWord_41827, baseEnd_41827] using wordTrace_append hprefix tailTrace_41827
  have hstable : (prefixWord ++ tailWord_41827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41827).length < 2 ^ (prefixWord ++ tailWord_41827).sum := by decide
  have hdescent : baseEnd_41827 < baseStart_41827 := by decide
  rcases family_descends (prefixWord ++ tailWord_41827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41840 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_41840 : Nat := 118140960795 + 41840 * 2 ^ 59
def prefixEnd_41840 : Nat := 4983230072969 + 3 ^ 40 * 41840 * 2
def baseEnd_41840 : Nat := 21484030584221534507587

theorem tailTrace_41840 : CollatzResearch.WordTrace tailWord_41840 prefixEnd_41840 21484030584221534507587 := by
  unfold tailWord_41840
  simp only [CollatzResearch.WordTrace]
  refine ⟨763015084214150274105487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1017353445618867032140649 763015084214150274105487)
  ·
    refine ⟨1144522626321225411158231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 763015084214150274105487 1144522626321225411158231)
    ·
      refine ⟨1716783939481838116737347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144522626321225411158231 1716783939481838116737347)
      ·
        refine ⟨2575175909222757175106021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716783939481838116737347 2575175909222757175106021)
        ·
          refine ⟨482845482979266970332379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2575175909222757175106021 482845482979266970332379)
          ·
            refine ⟨724268224468900455498569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482845482979266970332379 724268224468900455498569)
            ·
              refine ⟨543201168351675341623927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724268224468900455498569 543201168351675341623927)
              ·
                refine ⟨814801752527513012435891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543201168351675341623927 814801752527513012435891)
                ·
                  refine ⟨1222202628791269518653837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814801752527513012435891 1222202628791269518653837)
                  ·
                    refine ⟨458325985796726069495189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222202628791269518653837 458325985796726069495189)
                    ·
                      refine ⟨21484030584221534507587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 458325985796726069495189 21484030584221534507587)
                      ·
                        rfl

theorem cell23_41840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_41840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41840 prefixEnd_41840 := by exact prefixLift 41840
  have htrace : WordTrace (prefixWord ++ tailWord_41840) baseStart_41840 baseEnd_41840 := by
    simpa [prefixWord, tailWord_41840, baseEnd_41840] using wordTrace_append hprefix tailTrace_41840
  have hstable : (prefixWord ++ tailWord_41840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41840).length < 2 ^ (prefixWord ++ tailWord_41840).sum := by decide
  have hdescent : baseEnd_41840 < baseStart_41840 := by decide
  rcases family_descends (prefixWord ++ tailWord_41840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41878 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_41878 : Nat := 118140960795 + 41878 * 2 ^ 59
def prefixEnd_41878 : Nat := 4983230072969 + 3 ^ 40 * 41878 * 2
def baseEnd_41878 : Nat := 21503542849092385832413

theorem tailTrace_41878 : CollatzResearch.WordTrace tailWord_41878 prefixEnd_41878 21503542849092385832413 := by
  unfold tailWord_41878
  simp only [CollatzResearch.WordTrace]
  refine ⟨95463508893164564880893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1018277428193755358729525 95463508893164564880893)
  ·
    refine ⟨35798815834936711830335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95463508893164564880893 35798815834936711830335)
    ·
      refine ⟨53698223752405067745503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35798815834936711830335 53698223752405067745503)
      ·
        refine ⟨80547335628607601618255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53698223752405067745503 80547335628607601618255)
        ·
          refine ⟨120821003442911402427383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80547335628607601618255 120821003442911402427383)
          ·
            refine ⟨181231505164367103641075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120821003442911402427383 181231505164367103641075)
            ·
              refine ⟨271847257746550655461613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181231505164367103641075 271847257746550655461613)
              ·
                refine ⟨101942721654956495798105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271847257746550655461613 101942721654956495798105)
                ·
                  refine ⟨76457041241217371848579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101942721654956495798105 76457041241217371848579)
                  ·
                    refine ⟨114685561861826057772869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76457041241217371848579 114685561861826057772869)
                    ·
                      refine ⟨21503542849092385832413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 114685561861826057772869 21503542849092385832413)
                      ·
                        rfl

theorem cell23_41878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_41878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41878 prefixEnd_41878 := by exact prefixLift 41878
  have htrace : WordTrace (prefixWord ++ tailWord_41878) baseStart_41878 baseEnd_41878 := by
    simpa [prefixWord, tailWord_41878, baseEnd_41878] using wordTrace_append hprefix tailTrace_41878
  have hstable : (prefixWord ++ tailWord_41878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41878).length < 2 ^ (prefixWord ++ tailWord_41878).sum := by decide
  have hdescent : baseEnd_41878 < baseStart_41878 := by decide
  rcases family_descends (prefixWord ++ tailWord_41878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41905 : List Nat := [1, 2, 2, 4, 3, 2, 2, 2, 1, 4]
def baseStart_41905 : Nat := 118140960795 + 41905 * 2 ^ 59
def prefixEnd_41905 : Nat := 4983230072969 + 3 ^ 40 * 41905 * 2
def baseEnd_41905 : Nat := 7172468942254593398263

theorem tailTrace_41905 : CollatzResearch.WordTrace tailWord_41905 prefixEnd_41905 7172468942254593398263 := by
  unfold tailWord_41905
  simp only [CollatzResearch.WordTrace]
  refine ⟨1528400913192816649327169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1018933942128544432884779 1528400913192816649327169)
  ·
    refine ⟨1146300684894612486995377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1528400913192816649327169 1146300684894612486995377)
    ·
      refine ⟨859725513670959365246533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1146300684894612486995377 859725513670959365246533)
      ·
        refine ⟨161198533813304880983725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 859725513670959365246533 161198533813304880983725)
        ·
          refine ⟨60449450179989330368897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161198533813304880983725 60449450179989330368897)
          ·
            refine ⟨45337087634991997776673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60449450179989330368897 45337087634991997776673)
            ·
              refine ⟨34002815726243998332505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45337087634991997776673 34002815726243998332505)
              ·
                refine ⟨25502111794682998749379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34002815726243998332505 25502111794682998749379)
                ·
                  refine ⟨38253167692024498124069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25502111794682998749379 38253167692024498124069)
                  ·
                    refine ⟨7172468942254593398263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38253167692024498124069 7172468942254593398263)
                    ·
                      rfl

theorem cell23_41905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_41905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41905 prefixEnd_41905 := by exact prefixLift 41905
  have htrace : WordTrace (prefixWord ++ tailWord_41905) baseStart_41905 baseEnd_41905 := by
    simpa [prefixWord, tailWord_41905, baseEnd_41905] using wordTrace_append hprefix tailTrace_41905
  have hstable : (prefixWord ++ tailWord_41905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41905).length < 2 ^ (prefixWord ++ tailWord_41905).sum := by decide
  have hdescent : baseEnd_41905 < baseStart_41905 := by decide
  rcases family_descends (prefixWord ++ tailWord_41905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41927 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 1, 6]
def baseStart_41927 : Nat := 118140960795 + 41927 * 2 ^ 59
def prefixEnd_41927 : Nat := 4983230072969 + 3 ^ 40 * 41927 * 2
def baseEnd_41927 : Nat := 7176234467054231373229

theorem tailTrace_41927 : CollatzResearch.WordTrace tailWord_41927 prefixEnd_41927 7176234467054231373229 := by
  unfold tailWord_41927
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529203319113114406628035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1019468879408742937752023 1529203319113114406628035)
  ·
    refine ⟨2293804978669671609942053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1529203319113114406628035 2293804978669671609942053)
    ·
      refine ⟨430088433500563426864135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2293804978669671609942053 430088433500563426864135)
      ·
        refine ⟨645132650250845140296203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430088433500563426864135 645132650250845140296203)
        ·
          refine ⟨967698975376267710444305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645132650250845140296203 967698975376267710444305)
          ·
            refine ⟨725774231532200782833229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 967698975376267710444305 725774231532200782833229)
            ·
              refine ⟨272165336824575293562461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725774231532200782833229 272165336824575293562461)
              ·
                refine ⟨102062001309215735085923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272165336824575293562461 102062001309215735085923)
                ·
                  refine ⟨153093001963823602628885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102062001309215735085923 153093001963823602628885)
                  ·
                    refine ⟨7176234467054231373229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 153093001963823602628885 7176234467054231373229)
                    ·
                      rfl

theorem cell23_41927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_41927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41927 prefixEnd_41927 := by exact prefixLift 41927
  have htrace : WordTrace (prefixWord ++ tailWord_41927) baseStart_41927 baseEnd_41927 := by
    simpa [prefixWord, tailWord_41927, baseEnd_41927] using wordTrace_append hprefix tailTrace_41927
  have hstable : (prefixWord ++ tailWord_41927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41927).length < 2 ^ (prefixWord ++ tailWord_41927).sum := by decide
  have hdescent : baseEnd_41927 < baseStart_41927 := by decide
  rcases family_descends (prefixWord ++ tailWord_41927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41934 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_41934 : Nat := 118140960795 + 41934 * 2 ^ 59
def prefixEnd_41934 : Nat := 4983230072969 + 3 ^ 40 * 41934 * 2
def baseEnd_41934 : Nat := 21532297765744166732155

theorem tailTrace_41934 : CollatzResearch.WordTrace tailWord_41934 prefixEnd_41934 21532297765744166732155 := by
  unfold tailWord_41934
  simp only [CollatzResearch.WordTrace]
  refine ⟨191182328760969325266607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1019639086725169734755237 191182328760969325266607)
  ·
    refine ⟨286773493141453987899911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191182328760969325266607 286773493141453987899911)
    ·
      refine ⟨430160239712180981849867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286773493141453987899911 430160239712180981849867)
      ·
        refine ⟨645240359568271472774801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430160239712180981849867 645240359568271472774801)
        ·
          refine ⟨483930269676203604581101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645240359568271472774801 483930269676203604581101)
          ·
            refine ⟨181473851128576351717913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 483930269676203604581101 181473851128576351717913)
            ·
              refine ⟨136105388346432263788435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181473851128576351717913 136105388346432263788435)
              ·
                refine ⟨204158082519648395682653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136105388346432263788435 204158082519648395682653)
                ·
                  refine ⟨76559280944868148380995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204158082519648395682653 76559280944868148380995)
                  ·
                    refine ⟨114838921417302222571493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76559280944868148380995 114838921417302222571493)
                    ·
                      refine ⟨21532297765744166732155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 114838921417302222571493 21532297765744166732155)
                      ·
                        rfl

theorem cell23_41934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_41934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41934 prefixEnd_41934 := by exact prefixLift 41934
  have htrace : WordTrace (prefixWord ++ tailWord_41934) baseStart_41934 baseEnd_41934 := by
    simpa [prefixWord, tailWord_41934, baseEnd_41934] using wordTrace_append hprefix tailTrace_41934
  have hstable : (prefixWord ++ tailWord_41934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41934).length < 2 ^ (prefixWord ++ tailWord_41934).sum := by decide
  have hdescent : baseEnd_41934 < baseStart_41934 := by decide
  rcases family_descends (prefixWord ++ tailWord_41934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41938 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_41938 : Nat := 118140960795 + 41938 * 2 ^ 59
def prefixEnd_41938 : Nat := 4983230072969 + 3 ^ 40 * 41938 * 2
def baseEnd_41938 : Nat := 21534351688362151082137

theorem tailTrace_41938 : CollatzResearch.WordTrace tailWord_41938 prefixEnd_41938 21534351688362151082137 := by
  unfold tailWord_41938
  simp only [CollatzResearch.WordTrace]
  refine ⟨382401130518315821319617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1019736348048842190185645 382401130518315821319617)
  ·
    refine ⟨286800847888736865989713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 382401130518315821319617 286800847888736865989713)
    ·
      refine ⟨215100635916552649492285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286800847888736865989713 215100635916552649492285)
      ·
        refine ⟨80662738468707243559607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215100635916552649492285 80662738468707243559607)
        ·
          refine ⟨120994107703060865339411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80662738468707243559607 120994107703060865339411)
          ·
            refine ⟨181491161554591298009117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120994107703060865339411 181491161554591298009117)
            ·
              refine ⟨68059185582971736753419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181491161554591298009117 68059185582971736753419)
              ·
                refine ⟨102088778374457605130129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68059185582971736753419 102088778374457605130129)
                ·
                  refine ⟨76566583780843203847597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102088778374457605130129 76566583780843203847597)
                  ·
                    refine ⟨28712468917816201442849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76566583780843203847597 28712468917816201442849)
                    ·
                      refine ⟨21534351688362151082137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28712468917816201442849 21534351688362151082137)
                      ·
                        rfl

theorem cell23_41938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_41938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41938 prefixEnd_41938 := by exact prefixLift 41938
  have htrace : WordTrace (prefixWord ++ tailWord_41938) baseStart_41938 baseEnd_41938 := by
    simpa [prefixWord, tailWord_41938, baseEnd_41938] using wordTrace_append hprefix tailTrace_41938
  have hstable : (prefixWord ++ tailWord_41938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41938).length < 2 ^ (prefixWord ++ tailWord_41938).sum := by decide
  have hdescent : baseEnd_41938 < baseStart_41938 := by decide
  rcases family_descends (prefixWord ++ tailWord_41938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41951 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 4]
def baseStart_41951 : Nat := 118140960795 + 41951 * 2 ^ 59
def prefixEnd_41951 : Nat := 4983230072969 + 3 ^ 40 * 41951 * 2
def baseEnd_41951 : Nat := 21541026936870600219577

theorem tailTrace_41951 : CollatzResearch.WordTrace tailWord_41951 prefixEnd_41951 21541026936870600219577 := by
  unfold tailWord_41951
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530078671026166505501707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1020052447350777670334471 1530078671026166505501707)
  ·
    refine ⟨2295118006539249758252561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1530078671026166505501707 2295118006539249758252561)
    ·
      refine ⟨1721338504904437318689421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2295118006539249758252561 1721338504904437318689421)
      ·
        refine ⟨645501939339163994508533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1721338504904437318689421 645501939339163994508533)
        ·
          refine ⟨60515806813046624485175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 645501939339163994508533 60515806813046624485175)
          ·
            refine ⟨90773710219569936727763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60515806813046624485175 90773710219569936727763)
            ·
              refine ⟨136160565329354905091645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90773710219569936727763 136160565329354905091645)
              ·
                refine ⟨51060211998508089409367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136160565329354905091645 51060211998508089409367)
                ·
                  refine ⟨76590317997762134114051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51060211998508089409367 76590317997762134114051)
                  ·
                    refine ⟨114885476996643201171077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76590317997762134114051 114885476996643201171077)
                    ·
                      refine ⟨21541026936870600219577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 114885476996643201171077 21541026936870600219577)
                      ·
                        rfl

theorem cell23_41951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_41951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_41951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_41951 prefixEnd_41951 := by exact prefixLift 41951
  have htrace : WordTrace (prefixWord ++ tailWord_41951) baseStart_41951 baseEnd_41951 := by
    simpa [prefixWord, tailWord_41951, baseEnd_41951] using wordTrace_append hprefix tailTrace_41951
  have hstable : (prefixWord ++ tailWord_41951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41951).length < 2 ^ (prefixWord ++ tailWord_41951).sum := by decide
  have hdescent : baseEnd_41951 < baseStart_41951 := by decide
  rcases family_descends (prefixWord ++ tailWord_41951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42027 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 5]
def baseStart_42027 : Nat := 118140960795 + 42027 * 2 ^ 59
def prefixEnd_42027 : Nat := 4983230072969 + 3 ^ 40 * 42027 * 2
def baseEnd_42027 : Nat := 21580051466612302869227

theorem tailTrace_42027 : CollatzResearch.WordTrace tailWord_42027 prefixEnd_42027 21580051466612302869227 := by
  unfold tailWord_42027
  simp only [CollatzResearch.WordTrace]
  refine ⟨1532850618750831485268335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1021900412500554323512223 1532850618750831485268335)
  ·
    refine ⟨2299275928126247227902503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1532850618750831485268335 2299275928126247227902503)
    ·
      refine ⟨3448913892189370841853755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299275928126247227902503 3448913892189370841853755)
      ·
        refine ⟨5173370838284056262780633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3448913892189370841853755 5173370838284056262780633)
        ·
          refine ⟨3880028128713042197085475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5173370838284056262780633 3880028128713042197085475)
          ·
            refine ⟨5820042193069563295628213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3880028128713042197085475 5820042193069563295628213)
            ·
              refine ⟨545628955600271558965145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5820042193069563295628213 545628955600271558965145)
              ·
                refine ⟨409221716700203669223859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545628955600271558965145 409221716700203669223859)
                ·
                  refine ⟨613832575050305503835789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409221716700203669223859 613832575050305503835789)
                  ·
                    refine ⟨230187215643864563938421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613832575050305503835789 230187215643864563938421)
                    ·
                      refine ⟨21580051466612302869227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 230187215643864563938421 21580051466612302869227)
                      ·
                        rfl

theorem cell23_42027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_42027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42027 prefixEnd_42027 := by exact prefixLift 42027
  have htrace : WordTrace (prefixWord ++ tailWord_42027) baseStart_42027 baseEnd_42027 := by
    simpa [prefixWord, tailWord_42027, baseEnd_42027] using wordTrace_append hprefix tailTrace_42027
  have hstable : (prefixWord ++ tailWord_42027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42027).length < 2 ^ (prefixWord ++ tailWord_42027).sum := by decide
  have hdescent : baseEnd_42027 < baseStart_42027 := by decide
  rcases family_descends (prefixWord ++ tailWord_42027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42044 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_42044 : Nat := 118140960795 + 42044 * 2 ^ 59
def prefixEnd_42044 : Nat := 4983230072969 + 3 ^ 40 * 42044 * 2
def baseEnd_42044 : Nat := 21588780637738736356649

theorem tailTrace_42044 : CollatzResearch.WordTrace tailWord_42044 prefixEnd_42044 21588780637738736356649 := by
  unfold tailWord_42044
  simp only [CollatzResearch.WordTrace]
  refine ⟨766735329844621694318593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1022313773126162259091457 766735329844621694318593)
  ·
    refine ⟨575051497383466270738945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 766735329844621694318593 575051497383466270738945)
    ·
      refine ⟨431288623037599703054209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 575051497383466270738945 431288623037599703054209)
      ·
        refine ⟨323466467278199777290657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431288623037599703054209 323466467278199777290657)
        ·
          refine ⟨242599850458649832967993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323466467278199777290657 242599850458649832967993)
          ·
            refine ⟨181949887843987374725995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242599850458649832967993 181949887843987374725995)
            ·
              refine ⟨272924831765981062088993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181949887843987374725995 272924831765981062088993)
              ·
                refine ⟨204693623824485796566745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272924831765981062088993 204693623824485796566745)
                ·
                  refine ⟨153520217868364347425059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204693623824485796566745 153520217868364347425059)
                  ·
                    refine ⟨230280326802546521137589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153520217868364347425059 230280326802546521137589)
                    ·
                      refine ⟨21588780637738736356649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 230280326802546521137589 21588780637738736356649)
                      ·
                        rfl

theorem cell23_42044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_42044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42044 prefixEnd_42044 := by exact prefixLift 42044
  have htrace : WordTrace (prefixWord ++ tailWord_42044) baseStart_42044 baseEnd_42044 := by
    simpa [prefixWord, tailWord_42044, baseEnd_42044] using wordTrace_append hprefix tailTrace_42044
  have hstable : (prefixWord ++ tailWord_42044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42044).length < 2 ^ (prefixWord ++ tailWord_42044).sum := by decide
  have hdescent : baseEnd_42044 < baseStart_42044 := by decide
  rcases family_descends (prefixWord ++ tailWord_42044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42045 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 1, 3, 2]
def baseStart_42045 : Nat := 118140960795 + 42045 * 2 ^ 59
def prefixEnd_42045 : Nat := 4983230072969 + 3 ^ 40 * 42045 * 2
def baseEnd_42045 : Nat := 21589294118393232444145

theorem tailTrace_42045 : CollatzResearch.WordTrace tailWord_42045 prefixEnd_42045 21589294118393232444145 := by
  unfold tailWord_42045
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533507132685620559423589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1022338088457080372949059 1533507132685620559423589)
  ·
    refine ⟨287532587378553854891923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1533507132685620559423589 287532587378553854891923)
    ·
      refine ⟨431298881067830782337885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287532587378553854891923 431298881067830782337885)
      ·
        refine ⟨161737080400436543376707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 431298881067830782337885 161737080400436543376707)
        ·
          refine ⟨242605620600654815065061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161737080400436543376707 242605620600654815065061)
          ·
            refine ⟨45488553862622777824699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242605620600654815065061 45488553862622777824699)
            ·
              refine ⟨68232830793934166737049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45488553862622777824699 68232830793934166737049)
              ·
                refine ⟨51174623095450625052787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68232830793934166737049 51174623095450625052787)
                ·
                  refine ⟨76761934643175937579181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51174623095450625052787 76761934643175937579181)
                  ·
                    refine ⟨28785725491190976592193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76761934643175937579181 28785725491190976592193)
                    ·
                      refine ⟨21589294118393232444145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28785725491190976592193 21589294118393232444145)
                      ·
                        rfl

theorem cell23_42045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_42045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42045 prefixEnd_42045 := by exact prefixLift 42045
  have htrace : WordTrace (prefixWord ++ tailWord_42045) baseStart_42045 baseEnd_42045 := by
    simpa [prefixWord, tailWord_42045, baseEnd_42045] using wordTrace_append hprefix tailTrace_42045
  have hstable : (prefixWord ++ tailWord_42045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42045).length < 2 ^ (prefixWord ++ tailWord_42045).sum := by decide
  have hdescent : baseEnd_42045 < baseStart_42045 := by decide
  rcases family_descends (prefixWord ++ tailWord_42045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42047 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 9]
def baseStart_42047 : Nat := 118140960795 + 42047 * 2 ^ 59
def prefixEnd_42047 : Nat := 4983230072969 + 3 ^ 40 * 42047 * 2
def baseEnd_42047 : Nat := 2398924564411358291015

theorem tailTrace_42047 : CollatzResearch.WordTrace tailWord_42047 prefixEnd_42047 2398924564411358291015 := by
  unfold tailWord_42047
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533580078678374900996395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1022386719118916600664263 1533580078678374900996395)
  ·
    refine ⟨2300370118017562351494593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1533580078678374900996395 2300370118017562351494593)
    ·
      refine ⟨1725277588513171763620945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2300370118017562351494593 1725277588513171763620945)
      ·
        refine ⟨1293958191384878822715709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1725277588513171763620945 1293958191384878822715709)
        ·
          refine ⟨485234321769329558518391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1293958191384878822715709 485234321769329558518391)
          ·
            refine ⟨727851482653994337777587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485234321769329558518391 727851482653994337777587)
            ·
              refine ⟨1091777223980991506666381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727851482653994337777587 1091777223980991506666381)
              ·
                refine ⟨409416458992871814999893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1091777223980991506666381 409416458992871814999893)
                ·
                  refine ⟨2398924564411358291015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 409416458992871814999893 2398924564411358291015)
                  ·
                    rfl

theorem cell23_42047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 9].length) (baseStart_42047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42047 prefixEnd_42047 := by exact prefixLift 42047
  have htrace : WordTrace (prefixWord ++ tailWord_42047) baseStart_42047 baseEnd_42047 := by
    simpa [prefixWord, tailWord_42047, baseEnd_42047] using wordTrace_append hprefix tailTrace_42047
  have hstable : (prefixWord ++ tailWord_42047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42047).length < 2 ^ (prefixWord ++ tailWord_42047).sum := by decide
  have hdescent : baseEnd_42047 < baseStart_42047 := by decide
  rcases family_descends (prefixWord ++ tailWord_42047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42057 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_42057 : Nat := 118140960795 + 42057 * 2 ^ 59
def prefixEnd_42057 : Nat := 4983230072969 + 3 ^ 40 * 42057 * 2
def baseEnd_42057 : Nat := 21595455886247185494089

theorem tailTrace_42057 : CollatzResearch.WordTrace tailWord_42057 prefixEnd_42057 21595455886247185494089 := by
  unfold tailWord_42057
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533944808642146608860425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1022629872428097739240283 1533944808642146608860425)
  ·
    refine ⟨1150458606481609956645319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1533944808642146608860425 1150458606481609956645319)
    ·
      refine ⟨1725687909722414934967979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1150458606481609956645319 1725687909722414934967979)
      ·
        refine ⟨2588531864583622402451969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725687909722414934967979 2588531864583622402451969)
        ·
          refine ⟨1941398898437716801838977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2588531864583622402451969 1941398898437716801838977)
          ·
            refine ⟨1456049173828287601379233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941398898437716801838977 1456049173828287601379233)
            ·
              refine ⟨1092036880371215701034425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1456049173828287601379233 1092036880371215701034425)
              ·
                refine ⟨819027660278411775775819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092036880371215701034425 819027660278411775775819)
                ·
                  refine ⟨1228541490417617663663729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819027660278411775775819 1228541490417617663663729)
                  ·
                    refine ⟨921406117813213247747797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1228541490417617663663729 921406117813213247747797)
                    ·
                      refine ⟨21595455886247185494089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 921406117813213247747797 21595455886247185494089)
                      ·
                        rfl

theorem cell23_42057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_42057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42057 prefixEnd_42057 := by exact prefixLift 42057
  have htrace : WordTrace (prefixWord ++ tailWord_42057) baseStart_42057 baseEnd_42057 := by
    simpa [prefixWord, tailWord_42057, baseEnd_42057] using wordTrace_append hprefix tailTrace_42057
  have hstable : (prefixWord ++ tailWord_42057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42057).length < 2 ^ (prefixWord ++ tailWord_42057).sum := by decide
  have hdescent : baseEnd_42057 < baseStart_42057 := by decide
  rcases family_descends (prefixWord ++ tailWord_42057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42061 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_42061 : Nat := 118140960795 + 42061 * 2 ^ 59
def prefixEnd_42061 : Nat := 4983230072969 + 3 ^ 40 * 42061 * 2
def baseEnd_42061 : Nat := 21597509808865169844071

theorem tailTrace_42061 : CollatzResearch.WordTrace tailWord_42061 prefixEnd_42061 21597509808865169844071 := by
  unfold tailWord_42061
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534090700627655292006037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1022727133751770194670691 1534090700627655292006037)
  ·
    refine ⟨71910501591921341812783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1534090700627655292006037 71910501591921341812783)
    ·
      refine ⟨107865752387882012719175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71910501591921341812783 107865752387882012719175)
      ·
        refine ⟨161798628581823019078763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107865752387882012719175 161798628581823019078763)
        ·
          refine ⟨242697942872734528618145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161798628581823019078763 242697942872734528618145)
          ·
            refine ⟨182023457154550896463609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242697942872734528618145 182023457154550896463609)
            ·
              refine ⟨136517592865913172347707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182023457154550896463609 136517592865913172347707)
              ·
                refine ⟨204776389298869758521561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136517592865913172347707 204776389298869758521561)
                ·
                  refine ⟨153582291974152318891171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204776389298869758521561 153582291974152318891171)
                  ·
                    refine ⟨230373437961228478336757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153582291974152318891171 230373437961228478336757)
                    ·
                      refine ⟨21597509808865169844071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 230373437961228478336757 21597509808865169844071)
                      ·
                        rfl

theorem cell23_42061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_42061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42061 prefixEnd_42061 := by exact prefixLift 42061
  have htrace : WordTrace (prefixWord ++ tailWord_42061) baseStart_42061 baseEnd_42061 := by
    simpa [prefixWord, tailWord_42061, baseEnd_42061] using wordTrace_append hprefix tailTrace_42061
  have hstable : (prefixWord ++ tailWord_42061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42061).length < 2 ^ (prefixWord ++ tailWord_42061).sum := by decide
  have hdescent : baseEnd_42061 < baseStart_42061 := by decide
  rcases family_descends (prefixWord ++ tailWord_42061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42088 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_42088 : Nat := 118140960795 + 42088 * 2 ^ 59
def prefixEnd_42088 : Nat := 4983230072969 + 3 ^ 40 * 42088 * 2
def baseEnd_42088 : Nat := 21611373786536564206447

theorem tailTrace_42088 : CollatzResearch.WordTrace tailWord_42088 prefixEnd_42088 21611373786536564206447 := by
  unfold tailWord_42088
  simp only [CollatzResearch.WordTrace]
  refine ⟨767537735764919451619459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1023383647686559268825945 767537735764919451619459)
  ·
    refine ⟨1151306603647379177429189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767537735764919451619459 1151306603647379177429189)
    ·
      refine ⟨215869988183883595767973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1151306603647379177429189 215869988183883595767973)
      ·
        refine ⟨40475622784478174206495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215869988183883595767973 40475622784478174206495)
        ·
          refine ⟨60713434176717261309743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40475622784478174206495 60713434176717261309743)
          ·
            refine ⟨91070151265075891964615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60713434176717261309743 91070151265075891964615)
            ·
              refine ⟨136605226897613837946923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91070151265075891964615 136605226897613837946923)
              ·
                refine ⟨204907840346420756920385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136605226897613837946923 204907840346420756920385)
                ·
                  refine ⟨153680880259815567690289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204907840346420756920385 153680880259815567690289)
                  ·
                    refine ⟨115260660194861675767717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153680880259815567690289 115260660194861675767717)
                    ·
                      refine ⟨21611373786536564206447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 115260660194861675767717 21611373786536564206447)
                      ·
                        rfl

theorem cell23_42088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_42088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42088 prefixEnd_42088 := by exact prefixLift 42088
  have htrace : WordTrace (prefixWord ++ tailWord_42088) baseStart_42088 baseEnd_42088 := by
    simpa [prefixWord, tailWord_42088, baseEnd_42088] using wordTrace_append hprefix tailTrace_42088
  have hstable : (prefixWord ++ tailWord_42088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42088).length < 2 ^ (prefixWord ++ tailWord_42088).sum := by decide
  have hdescent : baseEnd_42088 < baseStart_42088 := by decide
  rcases family_descends (prefixWord ++ tailWord_42088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42131 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 2, 4, 2]
def baseStart_42131 : Nat := 118140960795 + 42131 * 2 ^ 59
def prefixEnd_42131 : Nat := 4983230072969 + 3 ^ 40 * 42131 * 2
def baseEnd_42131 : Nat := 21633453454679895968749

theorem tailTrace_42131 : CollatzResearch.WordTrace tailWord_42131 prefixEnd_42131 21633453454679895968749 := by
  unfold tailWord_42131
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536643810374057247054247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1024429206916038164702831 1536643810374057247054247)
  ·
    refine ⟨2304965715561085870581371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1536643810374057247054247 2304965715561085870581371)
    ·
      refine ⟨3457448573341628805872057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304965715561085870581371 3457448573341628805872057)
      ·
        refine ⟨2593086430006221604404043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3457448573341628805872057 2593086430006221604404043)
        ·
          refine ⟨3889629645009332406606065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2593086430006221604404043 3889629645009332406606065)
          ·
            refine ⟨2917222233756999304954549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3889629645009332406606065 2917222233756999304954549)
            ·
              refine ⟨273489584414718684839489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2917222233756999304954549 273489584414718684839489)
              ·
                refine ⟨205117188311039013629617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273489584414718684839489 205117188311039013629617)
                ·
                  refine ⟨153837891233279260222213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205117188311039013629617 153837891233279260222213)
                  ·
                    refine ⟨28844604606239861291665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153837891233279260222213 28844604606239861291665)
                    ·
                      refine ⟨21633453454679895968749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28844604606239861291665 21633453454679895968749)
                      ·
                        rfl

theorem cell23_42131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 4, 2].length) (baseStart_42131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42131 prefixEnd_42131 := by exact prefixLift 42131
  have htrace : WordTrace (prefixWord ++ tailWord_42131) baseStart_42131 baseEnd_42131 := by
    simpa [prefixWord, tailWord_42131, baseEnd_42131] using wordTrace_append hprefix tailTrace_42131
  have hstable : (prefixWord ++ tailWord_42131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42131).length < 2 ^ (prefixWord ++ tailWord_42131).sum := by decide
  have hdescent : baseEnd_42131 < baseStart_42131 := by decide
  rcases family_descends (prefixWord ++ tailWord_42131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42144 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_42144 : Nat := 118140960795 + 42144 * 2 ^ 59
def prefixEnd_42144 : Nat := 4983230072969 + 3 ^ 40 * 42144 * 2
def baseEnd_42144 : Nat := 21640128703188345106189

theorem tailTrace_42144 : CollatzResearch.WordTrace tailWord_42144 prefixEnd_42144 21640128703188345106189 := by
  unfold tailWord_42144
  simp only [CollatzResearch.WordTrace]
  refine ⟨768558979663480233638743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1024745306217973644851657 768558979663480233638743)
  ·
    refine ⟨1152838469495220350458115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 768558979663480233638743 1152838469495220350458115)
    ·
      refine ⟨1729257704242830525687173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152838469495220350458115 1729257704242830525687173)
      ·
        refine ⟨324235819545530723566345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1729257704242830525687173 324235819545530723566345)
        ·
          refine ⟨243176864659148042674759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324235819545530723566345 243176864659148042674759)
          ·
            refine ⟨364765296988722064012139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243176864659148042674759 364765296988722064012139)
            ·
              refine ⟨547147945483083096018209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364765296988722064012139 547147945483083096018209)
              ·
                refine ⟨410360959112312322013657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547147945483083096018209 410360959112312322013657)
                ·
                  refine ⟨307770719334234241510243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410360959112312322013657 307770719334234241510243)
                  ·
                    refine ⟨461656079001351362265365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 307770719334234241510243 461656079001351362265365)
                    ·
                      refine ⟨21640128703188345106189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 461656079001351362265365 21640128703188345106189)
                      ·
                        rfl

theorem cell23_42144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_42144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42144 prefixEnd_42144 := by exact prefixLift 42144
  have htrace : WordTrace (prefixWord ++ tailWord_42144) baseStart_42144 baseEnd_42144 := by
    simpa [prefixWord, tailWord_42144, baseEnd_42144] using wordTrace_append hprefix tailTrace_42144
  have hstable : (prefixWord ++ tailWord_42144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42144).length < 2 ^ (prefixWord ++ tailWord_42144).sum := by decide
  have hdescent : baseEnd_42144 < baseStart_42144 := by decide
  rcases family_descends (prefixWord ++ tailWord_42144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42148 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 2, 4, 2]
def baseStart_42148 : Nat := 118140960795 + 42148 * 2 ^ 59
def prefixEnd_42148 : Nat := 4983230072969 + 3 ^ 40 * 42148 * 2
def baseEnd_42148 : Nat := 21642182625806329456171

theorem tailTrace_42148 : CollatzResearch.WordTrace tailWord_42148 prefixEnd_42148 21642182625806329456171 := by
  unfold tailWord_42148
  simp only [CollatzResearch.WordTrace]
  refine ⟨768631925656234575211549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1024842567541646100282065 768631925656234575211549)
  ·
    refine ⟨288236972121087965704331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 768631925656234575211549 288236972121087965704331)
    ·
      refine ⟨432355458181631948556497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288236972121087965704331 432355458181631948556497)
      ·
        refine ⟨324266593636223961417373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432355458181631948556497 324266593636223961417373)
        ·
          refine ⟨121599972613583985531515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324266593636223961417373 121599972613583985531515)
          ·
            refine ⟨182399958920375978297273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121599972613583985531515 182399958920375978297273)
            ·
              refine ⟨136799969190281983722955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182399958920375978297273 136799969190281983722955)
              ·
                refine ⟨205199953785422975584433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136799969190281983722955 205199953785422975584433)
                ·
                  refine ⟨153899965339067231688325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205199953785422975584433 153899965339067231688325)
                  ·
                    refine ⟨28856243501075105941561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153899965339067231688325 28856243501075105941561)
                    ·
                      refine ⟨21642182625806329456171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28856243501075105941561 21642182625806329456171)
                      ·
                        rfl

theorem cell23_42148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_42148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42148 prefixEnd_42148 := by exact prefixLift 42148
  have htrace : WordTrace (prefixWord ++ tailWord_42148) baseStart_42148 baseEnd_42148 := by
    simpa [prefixWord, tailWord_42148, baseEnd_42148] using wordTrace_append hprefix tailTrace_42148
  have hstable : (prefixWord ++ tailWord_42148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42148).length < 2 ^ (prefixWord ++ tailWord_42148).sum := by decide
  have hdescent : baseEnd_42148 < baseStart_42148 := by decide
  rcases family_descends (prefixWord ++ tailWord_42148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42191 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 3, 5, 2]
def baseStart_42191 : Nat := 118140960795 + 42191 * 2 ^ 59
def prefixEnd_42191 : Nat := 4983230072969 + 3 ^ 40 * 42191 * 2
def baseEnd_42191 : Nat := 21664262293949661218473

theorem tailTrace_42191 : CollatzResearch.WordTrace tailWord_42191 prefixEnd_42191 21664262293949661218473 := by
  unfold tailWord_42191
  simp only [CollatzResearch.WordTrace]
  refine ⟨1538832190156687494238427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1025888126771124996158951 1538832190156687494238427)
  ·
    refine ⟨2308248285235031241357641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1538832190156687494238427 2308248285235031241357641)
    ·
      refine ⟨1731186213926273431018231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2308248285235031241357641 1731186213926273431018231)
      ·
        refine ⟨2596779320889410146527347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1731186213926273431018231 2596779320889410146527347)
        ·
          refine ⟨3895168981334115219791021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596779320889410146527347 3895168981334115219791021)
          ·
            refine ⟨1460688368000293207421633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3895168981334115219791021 1460688368000293207421633)
            ·
              refine ⟨1095516276000219905566225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1460688368000293207421633 1095516276000219905566225)
              ·
                refine ⟨821637207000164929174669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095516276000219905566225 821637207000164929174669)
                ·
                  refine ⟨308113952625061848440501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821637207000164929174669 308113952625061848440501)
                  ·
                    refine ⟨28885683058599548291297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 308113952625061848440501 28885683058599548291297)
                    ·
                      refine ⟨21664262293949661218473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28885683058599548291297 21664262293949661218473)
                      ·
                        rfl

theorem cell23_42191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 5, 2].length) (baseStart_42191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42191 prefixEnd_42191 := by exact prefixLift 42191
  have htrace : WordTrace (prefixWord ++ tailWord_42191) baseStart_42191 baseEnd_42191 := by
    simpa [prefixWord, tailWord_42191, baseEnd_42191] using wordTrace_append hprefix tailTrace_42191
  have hstable : (prefixWord ++ tailWord_42191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42191).length < 2 ^ (prefixWord ++ tailWord_42191).sum := by decide
  have hdescent : baseEnd_42191 < baseStart_42191 := by decide
  rcases family_descends (prefixWord ++ tailWord_42191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42218 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_42218 : Nat := 118140960795 + 42218 * 2 ^ 59
def prefixEnd_42218 : Nat := 4983230072969 + 3 ^ 40 * 42218 * 2
def baseEnd_42218 : Nat := 7226042090540351860283

theorem tailTrace_42218 : CollatzResearch.WordTrace tailWord_42218 prefixEnd_42218 7226042090540351860283 := by
  unfold tailWord_42218
  simp only [CollatzResearch.WordTrace]
  refine ⟨384954240264717776367827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1026544640705914070314205 384954240264717776367827)
  ·
    refine ⟨577431360397076664551741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384954240264717776367827 577431360397076664551741)
    ·
      refine ⟨216536760148903749206903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 577431360397076664551741 216536760148903749206903)
      ·
        refine ⟨324805140223355623810355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216536760148903749206903 324805140223355623810355)
        ·
          refine ⟨487207710335033435715533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324805140223355623810355 487207710335033435715533)
          ·
            refine ⟨182702891375637538393325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487207710335033435715533 182702891375637538393325)
            ·
              refine ⟨68513584265864076897497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182702891375637538393325 68513584265864076897497)
              ·
                refine ⟨51385188199398057673123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68513584265864076897497 51385188199398057673123)
                ·
                  refine ⟨77077782299097086509685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51385188199398057673123 77077782299097086509685)
                  ·
                    refine ⟨7226042090540351860283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77077782299097086509685 7226042090540351860283)
                    ·
                      rfl

theorem cell23_42218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_42218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42218 prefixEnd_42218 := by exact prefixLift 42218
  have htrace : WordTrace (prefixWord ++ tailWord_42218) baseStart_42218 baseEnd_42218 := by
    simpa [prefixWord, tailWord_42218, baseEnd_42218] using wordTrace_append hprefix tailTrace_42218
  have hstable : (prefixWord ++ tailWord_42218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42218).length < 2 ^ (prefixWord ++ tailWord_42218).sum := by decide
  have hdescent : baseEnd_42218 < baseStart_42218 := by decide
  rcases family_descends (prefixWord ++ tailWord_42218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42224 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_42224 : Nat := 118140960795 + 42224 * 2 ^ 59
def prefixEnd_42224 : Nat := 4983230072969 + 3 ^ 40 * 42224 * 2
def baseEnd_42224 : Nat := 21681207155548032105821

theorem tailTrace_42224 : CollatzResearch.WordTrace tailWord_42224 prefixEnd_42224 21681207155548032105821 := by
  unfold tailWord_42224
  simp only [CollatzResearch.WordTrace]
  refine ⟨770017899518567065094863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1026690532691422753459817 770017899518567065094863)
  ·
    refine ⟨1155026849277850597642295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770017899518567065094863 1155026849277850597642295)
    ·
      refine ⟨1732540273916775896463443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155026849277850597642295 1732540273916775896463443)
      ·
        refine ⟨2598810410875163844695165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732540273916775896463443 2598810410875163844695165)
        ·
          refine ⟨974553904078186441760687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2598810410875163844695165 974553904078186441760687)
          ·
            refine ⟨1461830856117279662641031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974553904078186441760687 1461830856117279662641031)
            ·
              refine ⟨2192746284175919493961547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461830856117279662641031 2192746284175919493961547)
              ·
                refine ⟨3289119426263879240942321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192746284175919493961547 3289119426263879240942321)
                ·
                  refine ⟨2466839569697909430706741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3289119426263879240942321 2466839569697909430706741)
                  ·
                    refine ⟨231266209659179009128757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2466839569697909430706741 231266209659179009128757)
                    ·
                      refine ⟨21681207155548032105821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 231266209659179009128757 21681207155548032105821)
                      ·
                        rfl

theorem cell23_42224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_42224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42224 prefixEnd_42224 := by exact prefixLift 42224
  have htrace : WordTrace (prefixWord ++ tailWord_42224) baseStart_42224 baseEnd_42224 := by
    simpa [prefixWord, tailWord_42224, baseEnd_42224] using wordTrace_append hprefix tailTrace_42224
  have hstable : (prefixWord ++ tailWord_42224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42224).length < 2 ^ (prefixWord ++ tailWord_42224).sum := by decide
  have hdescent : baseEnd_42224 < baseStart_42224 := by decide
  rcases family_descends (prefixWord ++ tailWord_42224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42272 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 3, 2, 2]
def baseStart_42272 : Nat := 118140960795 + 42272 * 2 ^ 59
def prefixEnd_42272 : Nat := 4983230072969 + 3 ^ 40 * 42272 * 2
def baseEnd_42272 : Nat := 21705854226963844305601

theorem tailTrace_42272 : CollatzResearch.WordTrace tailWord_42272 prefixEnd_42272 21705854226963844305601 := by
  unfold tailWord_42272
  simp only [CollatzResearch.WordTrace]
  refine ⟨770893251431619163968535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1027857668575492218624713 770893251431619163968535)
  ·
    refine ⟨1156339877147428745952803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770893251431619163968535 1156339877147428745952803)
    ·
      refine ⟨1734509815721143118929205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1156339877147428745952803 1734509815721143118929205)
      ·
        refine ⟨162610295223857167399613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1734509815721143118929205 162610295223857167399613)
        ·
          refine ⟨60978860708946437774855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162610295223857167399613 60978860708946437774855)
          ·
            refine ⟨91468291063419656662283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60978860708946437774855 91468291063419656662283)
            ·
              refine ⟨137202436595129484993425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91468291063419656662283 137202436595129484993425)
              ·
                refine ⟨102901827446347113745069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137202436595129484993425 102901827446347113745069)
                ·
                  refine ⟨38588185292380167654401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102901827446347113745069 38588185292380167654401)
                  ·
                    refine ⟨28941138969285125740801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38588185292380167654401 28941138969285125740801)
                    ·
                      refine ⟨21705854226963844305601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28941138969285125740801 21705854226963844305601)
                      ·
                        rfl

theorem cell23_42272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_42272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42272 prefixEnd_42272 := by exact prefixLift 42272
  have htrace : WordTrace (prefixWord ++ tailWord_42272) baseStart_42272 baseEnd_42272 := by
    simpa [prefixWord, tailWord_42272, baseEnd_42272] using wordTrace_append hprefix tailTrace_42272
  have hstable : (prefixWord ++ tailWord_42272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42272).length < 2 ^ (prefixWord ++ tailWord_42272).sum := by decide
  have hdescent : baseEnd_42272 < baseStart_42272 := by decide
  rcases family_descends (prefixWord ++ tailWord_42272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42285 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_42285 : Nat := 118140960795 + 42285 * 2 ^ 59
def prefixEnd_42285 : Nat := 4983230072969 + 3 ^ 40 * 42285 * 2
def baseEnd_42285 : Nat := 21712529475472293443041

theorem tailTrace_42285 : CollatzResearch.WordTrace tailWord_42285 prefixEnd_42285 21712529475472293443041 := by
  unfold tailWord_42285
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542260651816141548160309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1028173767877427698773539 1542260651816141548160309)
  ·
    refine ⟨144586936107763270140029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1542260651816141548160309 144586936107763270140029)
    ·
      refine ⟨54220101040411226302511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144586936107763270140029 54220101040411226302511)
      ·
        refine ⟨81330151560616839453767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54220101040411226302511 81330151560616839453767)
        ·
          refine ⟨121995227340925259180651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81330151560616839453767 121995227340925259180651)
          ·
            refine ⟨182992841011387888770977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121995227340925259180651 182992841011387888770977)
            ·
              refine ⟨137244630758540916578233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182992841011387888770977 137244630758540916578233)
              ·
                refine ⟨102933473068905687433675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137244630758540916578233 102933473068905687433675)
                ·
                  refine ⟨154400209603358531150513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102933473068905687433675 154400209603358531150513)
                  ·
                    refine ⟨115800157202518898362885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154400209603358531150513 115800157202518898362885)
                    ·
                      refine ⟨21712529475472293443041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 115800157202518898362885 21712529475472293443041)
                      ·
                        rfl

theorem cell23_42285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_42285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42285 prefixEnd_42285 := by exact prefixLift 42285
  have htrace : WordTrace (prefixWord ++ tailWord_42285) baseStart_42285 baseEnd_42285 := by
    simpa [prefixWord, tailWord_42285, baseEnd_42285] using wordTrace_append hprefix tailTrace_42285
  have hstable : (prefixWord ++ tailWord_42285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42285).length < 2 ^ (prefixWord ++ tailWord_42285).sum := by decide
  have hdescent : baseEnd_42285 < baseStart_42285 := by decide
  rcases family_descends (prefixWord ++ tailWord_42285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42288 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 4, 1, 3]
def baseStart_42288 : Nat := 118140960795 + 42288 * 2 ^ 59
def prefixEnd_42288 : Nat := 4983230072969 + 3 ^ 40 * 42288 * 2
def baseEnd_42288 : Nat := 21714069917435781705527

theorem tailTrace_42288 : CollatzResearch.WordTrace tailWord_42288 prefixEnd_42288 21714069917435781705527 := by
  unfold tailWord_42288
  simp only [CollatzResearch.WordTrace]
  refine ⟨771185035402636530259759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1028246713870182040346345 771185035402636530259759)
  ·
    refine ⟨1156777553103954795389639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 771185035402636530259759 1156777553103954795389639)
    ·
      refine ⟨1735166329655932193084459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1156777553103954795389639 1735166329655932193084459)
      ·
        refine ⟨2602749494483898289626689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735166329655932193084459 2602749494483898289626689)
        ·
          refine ⟨1952062120862923717220017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2602749494483898289626689 1952062120862923717220017)
          ·
            refine ⟨1464046590647192787915013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1952062120862923717220017 1464046590647192787915013)
            ·
              refine ⟨274508735746348647734065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1464046590647192787915013 274508735746348647734065)
              ·
                refine ⟨205881551809761485800549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274508735746348647734065 205881551809761485800549)
                ·
                  refine ⟨38602790964330278587603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205881551809761485800549 38602790964330278587603)
                  ·
                    refine ⟨57904186446495417881405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38602790964330278587603 57904186446495417881405)
                    ·
                      refine ⟨21714069917435781705527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 57904186446495417881405 21714069917435781705527)
                      ·
                        rfl

theorem cell23_42288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4, 1, 3].length) (baseStart_42288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42288 prefixEnd_42288 := by exact prefixLift 42288
  have htrace : WordTrace (prefixWord ++ tailWord_42288) baseStart_42288 baseEnd_42288 := by
    simpa [prefixWord, tailWord_42288, baseEnd_42288] using wordTrace_append hprefix tailTrace_42288
  have hstable : (prefixWord ++ tailWord_42288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42288).length < 2 ^ (prefixWord ++ tailWord_42288).sum := by decide
  have hdescent : baseEnd_42288 < baseStart_42288 := by decide
  rcases family_descends (prefixWord ++ tailWord_42288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42289 : List Nat := [1, 2, 2, 3, 3, 2, 2, 3, 1, 2, 2]
def baseStart_42289 : Nat := 118140960795 + 42289 * 2 ^ 59
def prefixEnd_42289 : Nat := 4983230072969 + 3 ^ 40 * 42289 * 2
def baseEnd_42289 : Nat := 21714583398090277793023

theorem tailTrace_42289 : CollatzResearch.WordTrace tailWord_42289 prefixEnd_42289 21714583398090277793023 := by
  unfold tailWord_42289
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542406543801650231305921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1028271029201100154203947 1542406543801650231305921)
  ·
    refine ⟨1156804907851237673479441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1542406543801650231305921 1156804907851237673479441)
    ·
      refine ⟨867603680888428255109581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1156804907851237673479441 867603680888428255109581)
      ·
        refine ⟨325351380333160595666093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 867603680888428255109581 325351380333160595666093)
        ·
          refine ⟨122006767624935223374785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325351380333160595666093 122006767624935223374785)
          ·
            refine ⟨91505075718701417531089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122006767624935223374785 91505075718701417531089)
            ·
              refine ⟨68628806789026063148317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91505075718701417531089 68628806789026063148317)
              ·
                refine ⟨25735802545884773680619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68628806789026063148317 25735802545884773680619)
                ·
                  refine ⟨38603703818827160520929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25735802545884773680619 38603703818827160520929)
                  ·
                    refine ⟨28952777864120370390697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38603703818827160520929 28952777864120370390697)
                    ·
                      refine ⟨21714583398090277793023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 28952777864120370390697 21714583398090277793023)
                      ·
                        rfl

theorem cell23_42289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_42289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42289 prefixEnd_42289 := by exact prefixLift 42289
  have htrace : WordTrace (prefixWord ++ tailWord_42289) baseStart_42289 baseEnd_42289 := by
    simpa [prefixWord, tailWord_42289, baseEnd_42289] using wordTrace_append hprefix tailTrace_42289
  have hstable : (prefixWord ++ tailWord_42289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42289).length < 2 ^ (prefixWord ++ tailWord_42289).sum := by decide
  have hdescent : baseEnd_42289 < baseStart_42289 := by decide
  rcases family_descends (prefixWord ++ tailWord_42289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42321 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 2, 6]
def baseStart_42321 : Nat := 118140960795 + 42321 * 2 ^ 59
def prefixEnd_42321 : Nat := 4983230072969 + 3 ^ 40 * 42321 * 2
def baseEnd_42321 : Nat := 7243671593011384197625

theorem tailTrace_42321 : CollatzResearch.WordTrace tailWord_42321 prefixEnd_42321 7243671593011384197625 := by
  unfold tailWord_42321
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543573679685719696470817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1029049119790479797647211 1543573679685719696470817)
  ·
    refine ⟨1157680259764289772353113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1543573679685719696470817 1157680259764289772353113)
    ·
      refine ⟨868260194823217329264835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1157680259764289772353113 868260194823217329264835)
      ·
        refine ⟨1302390292234825993897253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868260194823217329264835 1302390292234825993897253)
        ·
          refine ⟨244198179794029873855735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1302390292234825993897253 244198179794029873855735)
          ·
            refine ⟨366297269691044810783603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244198179794029873855735 366297269691044810783603)
            ·
              refine ⟨549445904536567216175405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366297269691044810783603 549445904536567216175405)
              ·
                refine ⟨206042214201212706065777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 549445904536567216175405 206042214201212706065777)
                ·
                  refine ⟨154531660650909529549333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206042214201212706065777 154531660650909529549333)
                  ·
                    refine ⟨7243671593011384197625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 154531660650909529549333 7243671593011384197625)
                    ·
                      rfl

theorem cell23_42321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_42321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42321 prefixEnd_42321 := by exact prefixLift 42321
  have htrace : WordTrace (prefixWord ++ tailWord_42321) baseStart_42321 baseEnd_42321 := by
    simpa [prefixWord, tailWord_42321, baseEnd_42321] using wordTrace_append hprefix tailTrace_42321
  have hstable : (prefixWord ++ tailWord_42321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42321).length < 2 ^ (prefixWord ++ tailWord_42321).sum := by decide
  have hdescent : baseEnd_42321 < baseStart_42321 := by decide
  rcases family_descends (prefixWord ++ tailWord_42321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42348 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_42348 : Nat := 118140960795 + 42348 * 2 ^ 59
def prefixEnd_42348 : Nat := 4983230072969 + 3 ^ 40 * 42348 * 2
def baseEnd_42348 : Nat := 21744878756705546955251

theorem tailTrace_42348 : CollatzResearch.WordTrace tailWord_42348 prefixEnd_42348 21744878756705546955251 := by
  unfold tailWord_42348
  simp only [CollatzResearch.WordTrace]
  refine ⟨772279225293951653851849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1029705633725268871802465 772279225293951653851849)
  ·
    refine ⟨579209418970463740388887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 772279225293951653851849 579209418970463740388887)
    ·
      refine ⟨868814128455695610583331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 579209418970463740388887 868814128455695610583331)
      ·
        refine ⟨1303221192683543415874997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868814128455695610583331 1303221192683543415874997)
        ·
          refine ⟨122176986814082195238281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1303221192683543415874997 122176986814082195238281)
          ·
            refine ⟨91632740110561646428711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122176986814082195238281 91632740110561646428711)
            ·
              refine ⟨137449110165842469643067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91632740110561646428711 137449110165842469643067)
              ·
                refine ⟨206173665248763704464601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137449110165842469643067 206173665248763704464601)
                ·
                  refine ⟨154630248936572778348451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206173665248763704464601 154630248936572778348451)
                  ·
                    refine ⟨231945373404859167522677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154630248936572778348451 231945373404859167522677)
                    ·
                      refine ⟨21744878756705546955251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 231945373404859167522677 21744878756705546955251)
                      ·
                        rfl

theorem cell23_42348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_42348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42348 prefixEnd_42348 := by exact prefixLift 42348
  have htrace : WordTrace (prefixWord ++ tailWord_42348) baseStart_42348 baseEnd_42348 := by
    simpa [prefixWord, tailWord_42348, baseEnd_42348] using wordTrace_append hprefix tailTrace_42348
  have hstable : (prefixWord ++ tailWord_42348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42348).length < 2 ^ (prefixWord ++ tailWord_42348).sum := by decide
  have hdescent : baseEnd_42348 < baseStart_42348 := by decide
  rcases family_descends (prefixWord ++ tailWord_42348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42368 : List Nat := [2, 1, 1, 2, 1, 2, 1, 8, 5]
def baseStart_42368 : Nat := 118140960795 + 42368 * 2 ^ 59
def prefixEnd_42368 : Nat := 4983230072969 + 3 ^ 40 * 42368 * 2
def baseEnd_42368 : Nat := 2417238707755052078351

theorem tailTrace_42368 : CollatzResearch.WordTrace tailWord_42368 prefixEnd_42368 2417238707755052078351 := by
  unfold tailWord_42368
  simp only [CollatzResearch.WordTrace]
  refine ⟨772643955257723361715879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1030191940343631148954505 772643955257723361715879)
  ·
    refine ⟨1158965932886585042573819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 772643955257723361715879 1158965932886585042573819)
    ·
      refine ⟨1738448899329877563860729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158965932886585042573819 1738448899329877563860729)
      ·
        refine ⟨1303836674497408172895547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1738448899329877563860729 1303836674497408172895547)
        ·
          refine ⟨1955755011746112259343321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303836674497408172895547 1955755011746112259343321)
          ·
            refine ⟨1466816258809584194507491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1955755011746112259343321 1466816258809584194507491)
            ·
              refine ⟨2200224388214376291761237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466816258809584194507491 2200224388214376291761237)
              ·
                refine ⟨25783879549387222169077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2200224388214376291761237 25783879549387222169077)
                ·
                  refine ⟨2417238707755052078351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25783879549387222169077 2417238707755052078351)
                  ·
                    rfl

theorem cell23_42368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 5].length) (baseStart_42368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42368 prefixEnd_42368 := by exact prefixLift 42368
  have htrace : WordTrace (prefixWord ++ tailWord_42368) baseStart_42368 baseEnd_42368 := by
    simpa [prefixWord, tailWord_42368, baseEnd_42368] using wordTrace_append hprefix tailTrace_42368
  have hstable : (prefixWord ++ tailWord_42368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42368).length < 2 ^ (prefixWord ++ tailWord_42368).sum := by decide
  have hdescent : baseEnd_42368 < baseStart_42368 := by decide
  rcases family_descends (prefixWord ++ tailWord_42368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42391 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_42391 : Nat := 118140960795 + 42391 * 2 ^ 59
def prefixEnd_42391 : Nat := 4983230072969 + 3 ^ 40 * 42391 * 2
def baseEnd_42391 : Nat := 21766958424848878717553

theorem tailTrace_42391 : CollatzResearch.WordTrace tailWord_42391 prefixEnd_42391 21766958424848878717553 := by
  unfold tailWord_42391
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546126789432121651519027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1030751192954747767679351 1546126789432121651519027)
  ·
    refine ⟨2319190184148182477278541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1546126789432121651519027 2319190184148182477278541)
    ·
      refine ⟨869696319055568428979453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2319190184148182477278541 869696319055568428979453)
      ·
        refine ⟨326136119645838160867295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 869696319055568428979453 326136119645838160867295)
        ·
          refine ⟨489204179468757241300943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326136119645838160867295 489204179468757241300943)
          ·
            refine ⟨733806269203135861951415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489204179468757241300943 733806269203135861951415)
            ·
              refine ⟨1100709403804703792927123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733806269203135861951415 1100709403804703792927123)
              ·
                refine ⟨1651064105707055689390685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100709403804703792927123 1651064105707055689390685)
                ·
                  refine ⟨619149039640145883521507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1651064105707055689390685 619149039640145883521507)
                  ·
                    refine ⟨928723559460218825282261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 619149039640145883521507 928723559460218825282261)
                    ·
                      refine ⟨21766958424848878717553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 928723559460218825282261 21766958424848878717553)
                      ·
                        rfl

theorem cell23_42391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_42391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42391 prefixEnd_42391 := by exact prefixLift 42391
  have htrace : WordTrace (prefixWord ++ tailWord_42391) baseStart_42391 baseEnd_42391 := by
    simpa [prefixWord, tailWord_42391, baseEnd_42391] using wordTrace_append hprefix tailTrace_42391
  have hstable : (prefixWord ++ tailWord_42391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42391).length < 2 ^ (prefixWord ++ tailWord_42391).sum := by decide
  have hdescent : baseEnd_42391 < baseStart_42391 := by decide
  rcases family_descends (prefixWord ++ tailWord_42391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42418 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_42418 : Nat := 118140960795 + 42418 * 2 ^ 59
def prefixEnd_42418 : Nat := 4983230072969 + 3 ^ 40 * 42418 * 2
def baseEnd_42418 : Nat := 21780822402520273079929

theorem tailTrace_42418 : CollatzResearch.WordTrace tailWord_42418 prefixEnd_42418 21780822402520273079929 := by
  unfold tailWord_42418
  simp only [CollatzResearch.WordTrace]
  refine ⟨386777890083576315687977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1031407706889536841834605 386777890083576315687977)
  ·
    refine ⟨290083417562682236765983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 386777890083576315687977 290083417562682236765983)
    ·
      refine ⟨435125126344023355148975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290083417562682236765983 435125126344023355148975)
      ·
        refine ⟨652687689516035032723463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435125126344023355148975 652687689516035032723463)
        ·
          refine ⟨979031534274052549085195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652687689516035032723463 979031534274052549085195)
          ·
            refine ⟨1468547301411078823627793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979031534274052549085195 1468547301411078823627793)
            ·
              refine ⟨1101410476058309117720845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1468547301411078823627793 1101410476058309117720845)
              ·
                refine ⟨413028928521865919145317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1101410476058309117720845 413028928521865919145317)
                ·
                  refine ⟨77442924097849859839747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 413028928521865919145317 77442924097849859839747)
                  ·
                    refine ⟨116164386146774789759621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77442924097849859839747 116164386146774789759621)
                    ·
                      refine ⟨21780822402520273079929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 116164386146774789759621 21780822402520273079929)
                      ·
                        rfl

theorem cell23_42418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_42418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42418 prefixEnd_42418 := by exact prefixLift 42418
  have htrace : WordTrace (prefixWord ++ tailWord_42418) baseStart_42418 baseEnd_42418 := by
    simpa [prefixWord, tailWord_42418, baseEnd_42418] using wordTrace_append hprefix tailTrace_42418
  have hstable : (prefixWord ++ tailWord_42418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42418).length < 2 ^ (prefixWord ++ tailWord_42418).sum := by decide
  have hdescent : baseEnd_42418 < baseStart_42418 := by decide
  rcases family_descends (prefixWord ++ tailWord_42418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42441 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 10]
def baseStart_42441 : Nat := 118140960795 + 42441 * 2 ^ 59
def prefixEnd_42441 : Nat := 4983230072969 + 3 ^ 40 * 42441 * 2
def baseEnd_42441 : Nat := 2421403606397075899147

theorem tailTrace_42441 : CollatzResearch.WordTrace tailWord_42441 prefixEnd_42441 2421403606397075899147 := by
  unfold tailWord_42441
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547950439250980190839177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1031966959500653460559451 1547950439250980190839177)
  ·
    refine ⟨1160962829438235143129383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1547950439250980190839177 1160962829438235143129383)
    ·
      refine ⟨1741444244157352714694075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1160962829438235143129383 1741444244157352714694075)
      ·
        refine ⟨2612166366236029072041113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1741444244157352714694075 2612166366236029072041113)
        ·
          refine ⟨1959124774677021804030835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2612166366236029072041113 1959124774677021804030835)
          ·
            refine ⟨2938687162015532706046253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959124774677021804030835 2938687162015532706046253)
            ·
              refine ⟨1102007685755824764767345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2938687162015532706046253 1102007685755824764767345)
              ·
                refine ⟨826505764316868573575509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102007685755824764767345 826505764316868573575509)
                ·
                  refine ⟨2421403606397075899147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 826505764316868573575509 2421403606397075899147)
                  ·
                    rfl

theorem cell23_42441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 10].length) (baseStart_42441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42441 prefixEnd_42441 := by exact prefixLift 42441
  have htrace : WordTrace (prefixWord ++ tailWord_42441) baseStart_42441 baseEnd_42441 := by
    simpa [prefixWord, tailWord_42441, baseEnd_42441] using wordTrace_append hprefix tailTrace_42441
  have hstable : (prefixWord ++ tailWord_42441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42441).length < 2 ^ (prefixWord ++ tailWord_42441).sum := by decide
  have hdescent : baseEnd_42441 < baseStart_42441 := by decide
  rcases family_descends (prefixWord ++ tailWord_42441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42468 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_42468 : Nat := 118140960795 + 42468 * 2 ^ 59
def prefixEnd_42468 : Nat := 4983230072969 + 3 ^ 40 * 42468 * 2
def baseEnd_42468 : Nat := 21806496435245077454699

theorem tailTrace_42468 : CollatzResearch.WordTrace tailWord_42468 prefixEnd_42468 21806496435245077454699 := by
  unfold tailWord_42468
  simp only [CollatzResearch.WordTrace]
  refine ⟨774467605076581901036029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1032623473435442534714705 774467605076581901036029)
  ·
    refine ⟨290425351903718212888511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 774467605076581901036029 290425351903718212888511)
    ·
      refine ⟨435638027855577319332767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290425351903718212888511 435638027855577319332767)
      ·
        refine ⟨653457041783365978999151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435638027855577319332767 653457041783365978999151)
        ·
          refine ⟨980185562675048968498727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653457041783365978999151 980185562675048968498727)
          ·
            refine ⟨1470278344012573452748091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980185562675048968498727 1470278344012573452748091)
            ·
              refine ⟨2205417516018860179122137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470278344012573452748091 2205417516018860179122137)
              ·
                refine ⟨1654063137014145134341603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2205417516018860179122137 1654063137014145134341603)
                ·
                  refine ⟨2481094705521217701512405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1654063137014145134341603 2481094705521217701512405)
                  ·
                    refine ⟨58150657160653539879197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2481094705521217701512405 58150657160653539879197)
                    ·
                      refine ⟨21806496435245077454699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 58150657160653539879197 21806496435245077454699)
                      ·
                        rfl

theorem cell23_42468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_42468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42468 prefixEnd_42468 := by exact prefixLift 42468
  have htrace : WordTrace (prefixWord ++ tailWord_42468) baseStart_42468 baseEnd_42468 := by
    simpa [prefixWord, tailWord_42468, baseEnd_42468] using wordTrace_append hprefix tailTrace_42468
  have hstable : (prefixWord ++ tailWord_42468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42468).length < 2 ^ (prefixWord ++ tailWord_42468).sum := by decide
  have hdescent : baseEnd_42468 < baseStart_42468 := by decide
  rcases family_descends (prefixWord ++ tailWord_42468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42478 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_42478 : Nat := 118140960795 + 42478 * 2 ^ 59
def prefixEnd_42478 : Nat := 4983230072969 + 3 ^ 40 * 42478 * 2
def baseEnd_42478 : Nat := 21811631241790038329653

theorem tailTrace_42478 : CollatzResearch.WordTrace tailWord_42478 prefixEnd_42478 21811631241790038329653 := by
  unfold tailWord_42478
  simp only [CollatzResearch.WordTrace]
  refine ⟨193662492514616938742011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1032866626744623673290725 193662492514616938742011)
  ·
    refine ⟨290493738771925408113017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193662492514616938742011 290493738771925408113017)
    ·
      refine ⟨217870304078944056084763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290493738771925408113017 217870304078944056084763)
      ·
        refine ⟨326805456118416084127145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217870304078944056084763 326805456118416084127145)
        ·
          refine ⟨245104092088812063095359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326805456118416084127145 245104092088812063095359)
          ·
            refine ⟨367656138133218094643039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245104092088812063095359 367656138133218094643039)
            ·
              refine ⟨551484207199827141964559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367656138133218094643039 551484207199827141964559)
              ·
                refine ⟨827226310799740712946839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551484207199827141964559 827226310799740712946839)
                ·
                  refine ⟨1240839466199611069420259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827226310799740712946839 1240839466199611069420259)
                  ·
                    refine ⟨1861259199299416604130389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1240839466199611069420259 1861259199299416604130389)
                    ·
                      refine ⟨21811631241790038329653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 1861259199299416604130389 21811631241790038329653)
                      ·
                        rfl

theorem cell23_42478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_42478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42478 prefixEnd_42478 := by exact prefixLift 42478
  have htrace : WordTrace (prefixWord ++ tailWord_42478) baseStart_42478 baseEnd_42478 := by
    simpa [prefixWord, tailWord_42478, baseEnd_42478] using wordTrace_append hprefix tailTrace_42478
  have hstable : (prefixWord ++ tailWord_42478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42478).length < 2 ^ (prefixWord ++ tailWord_42478).sum := by decide
  have hdescent : baseEnd_42478 < baseStart_42478 := by decide
  rcases family_descends (prefixWord ++ tailWord_42478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42495 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 6, 3, 2]
def baseStart_42495 : Nat := 118140960795 + 42495 * 2 ^ 59
def prefixEnd_42495 : Nat := 4983230072969 + 3 ^ 40 * 42495 * 2
def baseEnd_42495 : Nat := 21820360412916471817075

theorem tailTrace_42495 : CollatzResearch.WordTrace tailWord_42495 prefixEnd_42495 21820360412916471817075 := by
  unfold tailWord_42495
  simp only [CollatzResearch.WordTrace]
  refine ⟨1549919981055347413304939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1033279987370231608869959 1549919981055347413304939)
  ·
    refine ⟨2324879971583021119957409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1549919981055347413304939 2324879971583021119957409)
    ·
      refine ⟨1743659978687265839968057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2324879971583021119957409 1743659978687265839968057)
      ·
        refine ⟨1307744984015449379976043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1743659978687265839968057 1307744984015449379976043)
        ·
          refine ⟨1961617476023174069964065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307744984015449379976043 1961617476023174069964065)
          ·
            refine ⟨1471213107017380552473049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1961617476023174069964065 1471213107017380552473049)
            ·
              refine ⟨1103409830263035414354787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1471213107017380552473049 1103409830263035414354787)
              ·
                refine ⟨1655114745394553121532181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103409830263035414354787 1655114745394553121532181)
                ·
                  refine ⟨77583503690369677571821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1655114745394553121532181 77583503690369677571821)
                  ·
                    refine ⟨29093813883888629089433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77583503690369677571821 29093813883888629089433)
                    ·
                      refine ⟨21820360412916471817075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 29093813883888629089433 21820360412916471817075)
                      ·
                        rfl

theorem cell23_42495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_42495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42495 prefixEnd_42495 := by exact prefixLift 42495
  have htrace : WordTrace (prefixWord ++ tailWord_42495) baseStart_42495 baseEnd_42495 := by
    simpa [prefixWord, tailWord_42495, baseEnd_42495] using wordTrace_append hprefix tailTrace_42495
  have hstable : (prefixWord ++ tailWord_42495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42495).length < 2 ^ (prefixWord ++ tailWord_42495).sum := by decide
  have hdescent : baseEnd_42495 < baseStart_42495 := by decide
  rcases family_descends (prefixWord ++ tailWord_42495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42505 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 1, 5]
def baseStart_42505 : Nat := 118140960795 + 42505 * 2 ^ 59
def prefixEnd_42505 : Nat := 4983230072969 + 3 ^ 40 * 42505 * 2
def baseEnd_42505 : Nat := 7275165073153810897343

theorem tailTrace_42505 : CollatzResearch.WordTrace tailWord_42505 prefixEnd_42505 7275165073153810897343 := by
  unfold tailWord_42505
  simp only [CollatzResearch.WordTrace]
  refine ⟨1550284711019119121168969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1033523140679412747445979 1550284711019119121168969)
  ·
    refine ⟨1162713533264339340876727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1550284711019119121168969 1162713533264339340876727)
    ·
      refine ⟨1744070299896509011315091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162713533264339340876727 1744070299896509011315091)
      ·
        refine ⟨2616105449844763516972637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744070299896509011315091 2616105449844763516972637)
        ·
          refine ⟨981039543691786318864739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2616105449844763516972637 981039543691786318864739)
          ·
            refine ⟨1471559315537679478297109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981039543691786318864739 1471559315537679478297109)
            ·
              refine ⟨68979342915828725545177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1471559315537679478297109 68979342915828725545177)
              ·
                refine ⟨51734507186871544158883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68979342915828725545177 51734507186871544158883)
                ·
                  refine ⟨77601760780307316238325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51734507186871544158883 77601760780307316238325)
                  ·
                    refine ⟨7275165073153810897343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77601760780307316238325 7275165073153810897343)
                    ·
                      rfl

theorem cell23_42505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 5].length) (baseStart_42505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42505 prefixEnd_42505 := by exact prefixLift 42505
  have htrace : WordTrace (prefixWord ++ tailWord_42505) baseStart_42505 baseEnd_42505 := by
    simpa [prefixWord, tailWord_42505, baseEnd_42505] using wordTrace_append hprefix tailTrace_42505
  have hstable : (prefixWord ++ tailWord_42505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42505).length < 2 ^ (prefixWord ++ tailWord_42505).sum := by decide
  have hdescent : baseEnd_42505 < baseStart_42505 := by decide
  rcases family_descends (prefixWord ++ tailWord_42505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42536 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_42536 : Nat := 118140960795 + 42536 * 2 ^ 59
def prefixEnd_42536 : Nat := 4983230072969 + 3 ^ 40 * 42536 * 2
def baseEnd_42536 : Nat := 21841413119750811404387

theorem tailTrace_42536 : CollatzResearch.WordTrace tailWord_42536 prefixEnd_42536 21841413119750811404387 := by
  unfold tailWord_42536
  simp only [CollatzResearch.WordTrace]
  refine ⟨775707686953405707773731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1034276915937874277031641 775707686953405707773731)
  ·
    refine ⟨1163561530430108561660597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 775707686953405707773731 1163561530430108561660597)
    ·
      refine ⟨109083893477822677655681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1163561530430108561660597 109083893477822677655681)
      ·
        refine ⟨81812920108367008241761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109083893477822677655681 81812920108367008241761)
        ·
          refine ⟨61359690081275256181321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81812920108367008241761 61359690081275256181321)
          ·
            refine ⟨46019767560956442135991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61359690081275256181321 46019767560956442135991)
            ·
              refine ⟨69029651341434663203987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46019767560956442135991 69029651341434663203987)
              ·
                refine ⟨103544477012151994805981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69029651341434663203987 103544477012151994805981)
                ·
                  refine ⟨38829178879556998052243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103544477012151994805981 38829178879556998052243)
                  ·
                    refine ⟨58243768319335497078365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38829178879556998052243 58243768319335497078365)
                    ·
                      refine ⟨21841413119750811404387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 58243768319335497078365 21841413119750811404387)
                      ·
                        rfl

theorem cell23_42536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_42536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42536 prefixEnd_42536 := by exact prefixLift 42536
  have htrace : WordTrace (prefixWord ++ tailWord_42536) baseStart_42536 baseEnd_42536 := by
    simpa [prefixWord, tailWord_42536, baseEnd_42536] using wordTrace_append hprefix tailTrace_42536
  have hstable : (prefixWord ++ tailWord_42536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42536).length < 2 ^ (prefixWord ++ tailWord_42536).sum := by decide
  have hdescent : baseEnd_42536 < baseStart_42536 := by decide
  rcases family_descends (prefixWord ++ tailWord_42536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42545 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 3, 2, 3]
def baseStart_42545 : Nat := 118140960795 + 42545 * 2 ^ 59
def prefixEnd_42545 : Nat := 4983230072969 + 3 ^ 40 * 42545 * 2
def baseEnd_42545 : Nat := 21846034445641276191845

theorem tailTrace_42545 : CollatzResearch.WordTrace tailWord_42545 prefixEnd_42545 21846034445641276191845 := by
  unfold tailWord_42545
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551743630874205952625089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1034495753916137301750059 1551743630874205952625089)
  ·
    refine ⟨1163807723155654464468817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1551743630874205952625089 1163807723155654464468817)
    ·
      refine ⟨872855792366740848351613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1163807723155654464468817 872855792366740848351613)
      ·
        refine ⟨327320922137527818131855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 872855792366740848351613 327320922137527818131855)
        ·
          refine ⟨490981383206291727197783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327320922137527818131855 490981383206291727197783)
          ·
            refine ⟨736472074809437590796675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490981383206291727197783 736472074809437590796675)
            ·
              refine ⟨1104708112214156386195013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736472074809437590796675 1104708112214156386195013)
              ·
                refine ⟨207132771040154322411565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1104708112214156386195013 207132771040154322411565)
                ·
                  refine ⟨77674789140057870904337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207132771040154322411565 77674789140057870904337)
                  ·
                    refine ⟨58256091855043403178253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77674789140057870904337 58256091855043403178253)
                    ·
                      refine ⟨21846034445641276191845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 58256091855043403178253 21846034445641276191845)
                      ·
                        rfl

theorem cell23_42545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_42545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42545 prefixEnd_42545 := by exact prefixLift 42545
  have htrace : WordTrace (prefixWord ++ tailWord_42545) baseStart_42545 baseEnd_42545 := by
    simpa [prefixWord, tailWord_42545, baseEnd_42545] using wordTrace_append hprefix tailTrace_42545
  have hstable : (prefixWord ++ tailWord_42545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42545).length < 2 ^ (prefixWord ++ tailWord_42545).sum := by decide
  have hdescent : baseEnd_42545 < baseStart_42545 := by decide
  rcases family_descends (prefixWord ++ tailWord_42545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42552 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 2, 4]
def baseStart_42552 : Nat := 118140960795 + 42552 * 2 ^ 59
def prefixEnd_42552 : Nat := 4983230072969 + 3 ^ 40 * 42552 * 2
def baseEnd_42552 : Nat := 7283209603407582934771

theorem tailTrace_42552 : CollatzResearch.WordTrace tailWord_42552 prefixEnd_42552 7283209603407582934771 := by
  unfold tailWord_42552
  simp only [CollatzResearch.WordTrace]
  refine ⟨775999470924423074064955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1034665961232564098753273 775999470924423074064955)
  ·
    refine ⟨1163999206386634611097433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 775999470924423074064955 1163999206386634611097433)
    ·
      refine ⟨872999404789975958323075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1163999206386634611097433 872999404789975958323075)
      ·
        refine ⟨1309499107184963937484613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872999404789975958323075 1309499107184963937484613)
        ·
          refine ⟨245531082597180738278365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1309499107184963937484613 245531082597180738278365)
          ·
            refine ⟨92074155973942776854387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245531082597180738278365 92074155973942776854387)
            ·
              refine ⟨138111233960914165281581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92074155973942776854387 138111233960914165281581)
              ·
                refine ⟨51791712735342811980593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138111233960914165281581 51791712735342811980593)
                ·
                  refine ⟨38843784551507108985445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51791712735342811980593 38843784551507108985445)
                  ·
                    refine ⟨7283209603407582934771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38843784551507108985445 7283209603407582934771)
                    ·
                      rfl

theorem cell23_42552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_42552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42552 prefixEnd_42552 := by exact prefixLift 42552
  have htrace : WordTrace (prefixWord ++ tailWord_42552) baseStart_42552 baseEnd_42552 := by
    simpa [prefixWord, tailWord_42552, baseEnd_42552] using wordTrace_append hprefix tailTrace_42552
  have hstable : (prefixWord ++ tailWord_42552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42552).length < 2 ^ (prefixWord ++ tailWord_42552).sum := by decide
  have hdescent : baseEnd_42552 < baseStart_42552 := by decide
  rcases family_descends (prefixWord ++ tailWord_42552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42582 : List Nat := [5, 2, 2, 2, 12]
def baseStart_42582 : Nat := 118140960795 + 42582 * 2 ^ 59
def prefixEnd_42582 : Nat := 4983230072969 + 3 ^ 40 * 42582 * 2
def baseEnd_42582 : Nat := 29993186872232690575

theorem tailTrace_42582 : CollatzResearch.WordTrace tailWord_42582 prefixEnd_42582 29993186872232690575 := by
  unfold tailWord_42582
  simp only [CollatzResearch.WordTrace]
  refine ⟨97068320733760079482625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1035395421160107514481333 97068320733760079482625)
  ·
    refine ⟨72801240550320059611969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97068320733760079482625 72801240550320059611969)
    ·
      refine ⟨54600930412740044708977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72801240550320059611969 54600930412740044708977)
      ·
        refine ⟨40950697809555033531733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54600930412740044708977 40950697809555033531733)
        ·
          refine ⟨29993186872232690575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 40950697809555033531733 29993186872232690575)
          ·
            rfl

theorem cell23_42582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 12].length) (baseStart_42582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42582 prefixEnd_42582 := by exact prefixLift 42582
  have htrace : WordTrace (prefixWord ++ tailWord_42582) baseStart_42582 baseEnd_42582 := by
    simpa [prefixWord, tailWord_42582, baseEnd_42582] using wordTrace_append hprefix tailTrace_42582
  have hstable : (prefixWord ++ tailWord_42582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42582).length < 2 ^ (prefixWord ++ tailWord_42582).sum := by decide
  have hdescent : baseEnd_42582 < baseStart_42582 := by decide
  rcases family_descends (prefixWord ++ tailWord_42582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42649 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 2, 2, 2]
def baseStart_42649 : Nat := 118140960795 + 42649 * 2 ^ 59
def prefixEnd_42649 : Nat := 4983230072969 + 3 ^ 40 * 42649 * 2
def baseEnd_42649 : Nat := 21899436433708869291367

theorem tailTrace_42649 : CollatzResearch.WordTrace tailWord_42649 prefixEnd_42649 21899436433708869291367 := by
  unfold tailWord_42649
  simp only [CollatzResearch.WordTrace]
  refine ⟨1555536822497431714411001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1037024548331621142940667 1555536822497431714411001)
  ·
    refine ⟨1166652616873073785808251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1555536822497431714411001 1166652616873073785808251)
    ·
      refine ⟨1749978925309610678712377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166652616873073785808251 1749978925309610678712377)
      ·
        refine ⟨1312484193982208009034283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1749978925309610678712377 1312484193982208009034283)
        ·
          refine ⟨1968726290973312013551425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312484193982208009034283 1968726290973312013551425)
          ·
            refine ⟨1476544718229984010163569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1968726290973312013551425 1476544718229984010163569)
            ·
              refine ⟨1107408538672488007622677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476544718229984010163569 1107408538672488007622677)
              ·
                refine ⟨51909775250272875357313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1107408538672488007622677 51909775250272875357313)
                ·
                  refine ⟨38932331437704656517985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51909775250272875357313 38932331437704656517985)
                  ·
                    refine ⟨29199248578278492388489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38932331437704656517985 29199248578278492388489)
                    ·
                      refine ⟨21899436433708869291367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 29199248578278492388489 21899436433708869291367)
                      ·
                        rfl

theorem cell23_42649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_42649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42649 prefixEnd_42649 := by exact prefixLift 42649
  have htrace : WordTrace (prefixWord ++ tailWord_42649) baseStart_42649 baseEnd_42649 := by
    simpa [prefixWord, tailWord_42649, baseEnd_42649] using wordTrace_append hprefix tailTrace_42649
  have hstable : (prefixWord ++ tailWord_42649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42649).length < 2 ^ (prefixWord ++ tailWord_42649).sum := by decide
  have hdescent : baseEnd_42649 < baseStart_42649 := by decide
  rcases family_descends (prefixWord ++ tailWord_42649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42665 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 6, 3, 3]
def baseStart_42665 : Nat := 118140960795 + 42665 * 2 ^ 59
def prefixEnd_42665 : Nat := 4983230072969 + 3 ^ 40 * 42665 * 2
def baseEnd_42665 : Nat := 21907652124180806691293

theorem tailTrace_42665 : CollatzResearch.WordTrace tailWord_42665 prefixEnd_42665 21907652124180806691293 := by
  unfold tailWord_42665
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556120390439466446993449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1037413593626310964662299 1556120390439466446993449)
  ·
    refine ⟨1167090292829599835245087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1556120390439466446993449 1167090292829599835245087)
    ·
      refine ⟨1750635439244399752867631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1167090292829599835245087 1750635439244399752867631)
      ·
        refine ⟨2625953158866599629301447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750635439244399752867631 2625953158866599629301447)
        ·
          refine ⟨3938929738299899443952171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625953158866599629301447 3938929738299899443952171)
          ·
            refine ⟨5908394607449849165928257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938929738299899443952171 5908394607449849165928257)
            ·
              refine ⟨4431295955587386874446193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5908394607449849165928257 4431295955587386874446193)
              ·
                refine ⟨3323471966690540155834645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4431295955587386874446193 3323471966690540155834645)
                ·
                  refine ⟨155787748438619069804749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3323471966690540155834645 155787748438619069804749)
                  ·
                    refine ⟨58420405664482151176781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155787748438619069804749 58420405664482151176781)
                    ·
                      refine ⟨21907652124180806691293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 58420405664482151176781 21907652124180806691293)
                      ·
                        rfl

theorem cell23_42665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3, 3].length) (baseStart_42665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42665 prefixEnd_42665 := by exact prefixLift 42665
  have htrace : WordTrace (prefixWord ++ tailWord_42665) baseStart_42665 baseEnd_42665 := by
    simpa [prefixWord, tailWord_42665, baseEnd_42665] using wordTrace_append hprefix tailTrace_42665
  have hstable : (prefixWord ++ tailWord_42665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42665).length < 2 ^ (prefixWord ++ tailWord_42665).sum := by decide
  have hdescent : baseEnd_42665 < baseStart_42665 := by decide
  rcases family_descends (prefixWord ++ tailWord_42665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42685 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_42685 : Nat := 118140960795 + 42685 * 2 ^ 59
def prefixEnd_42685 : Nat := 4983230072969 + 3 ^ 40 * 42685 * 2
def baseEnd_42685 : Nat := 7305973912423576147067

theorem tailTrace_42685 : CollatzResearch.WordTrace tailWord_42685 prefixEnd_42685 7305973912423576147067 := by
  unfold tailWord_42685
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556849850367009862721509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1037899900244673241814339 1556849850367009862721509)
  ·
    refine ⟨291909346943814349260283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1556849850367009862721509 291909346943814349260283)
    ·
      refine ⟨437864020415721523890425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291909346943814349260283 437864020415721523890425)
      ·
        refine ⟨328398015311791142917819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437864020415721523890425 328398015311791142917819)
        ·
          refine ⟨492597022967686714376729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328398015311791142917819 492597022967686714376729)
          ·
            refine ⟨369447767225765035782547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492597022967686714376729 369447767225765035782547)
            ·
              refine ⟨554171650838647553673821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369447767225765035782547 554171650838647553673821)
              ·
                refine ⟨207814369064492832627683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 554171650838647553673821 207814369064492832627683)
                ·
                  refine ⟨311721553596739248941525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207814369064492832627683 311721553596739248941525)
                  ·
                    refine ⟨7305973912423576147067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 311721553596739248941525 7305973912423576147067)
                    ·
                      rfl

theorem cell23_42685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_42685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42685 prefixEnd_42685 := by exact prefixLift 42685
  have htrace : WordTrace (prefixWord ++ tailWord_42685) baseStart_42685 baseEnd_42685 := by
    simpa [prefixWord, tailWord_42685, baseEnd_42685] using wordTrace_append hprefix tailTrace_42685
  have hstable : (prefixWord ++ tailWord_42685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42685).length < 2 ^ (prefixWord ++ tailWord_42685).sum := by decide
  have hdescent : baseEnd_42685 < baseStart_42685 := by decide
  rcases family_descends (prefixWord ++ tailWord_42685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42695 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_42695 : Nat := 118140960795 + 42695 * 2 ^ 59
def prefixEnd_42695 : Nat := 4983230072969 + 3 ^ 40 * 42695 * 2
def baseEnd_42695 : Nat := 21923056543815689316155

theorem tailTrace_42695 : CollatzResearch.WordTrace tailWord_42695 prefixEnd_42695 21923056543815689316155 := by
  unfold tailWord_42695
  simp only [CollatzResearch.WordTrace]
  refine ⟨1557214580330781570585539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1038143053553854380390359 1557214580330781570585539)
  ·
    refine ⟨2335821870496172355878309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1557214580330781570585539 2335821870496172355878309)
    ·
      refine ⟨437966600718032316727183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2335821870496172355878309 437966600718032316727183)
      ·
        refine ⟨656949901077048475090775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437966600718032316727183 656949901077048475090775)
        ·
          refine ⟨985424851615572712636163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656949901077048475090775 985424851615572712636163)
          ·
            refine ⟨1478137277423359068954245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985424851615572712636163 1478137277423359068954245)
            ·
              refine ⟨277150739516879825428921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1478137277423359068954245 277150739516879825428921)
              ·
                refine ⟨207863054637659869071691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277150739516879825428921 207863054637659869071691)
                ·
                  refine ⟨311794581956489803607537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207863054637659869071691 311794581956489803607537)
                  ·
                    refine ⟨233845936467367352705653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 311794581956489803607537 233845936467367352705653)
                    ·
                      refine ⟨21923056543815689316155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 233845936467367352705653 21923056543815689316155)
                      ·
                        rfl

theorem cell23_42695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_42695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42695 prefixEnd_42695 := by exact prefixLift 42695
  have htrace : WordTrace (prefixWord ++ tailWord_42695) baseStart_42695 baseEnd_42695 := by
    simpa [prefixWord, tailWord_42695, baseEnd_42695] using wordTrace_append hprefix tailTrace_42695
  have hstable : (prefixWord ++ tailWord_42695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42695).length < 2 ^ (prefixWord ++ tailWord_42695).sum := by decide
  have hdescent : baseEnd_42695 < baseStart_42695 := by decide
  rcases family_descends (prefixWord ++ tailWord_42695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42702 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_42702 : Nat := 118140960795 + 42702 * 2 ^ 59
def prefixEnd_42702 : Nat := 4983230072969 + 3 ^ 40 * 42702 * 2
def baseEnd_42702 : Nat := 7308883636132387309541

theorem tailTrace_42702 : CollatzResearch.WordTrace tailWord_42702 prefixEnd_42702 7308883636132387309541 := by
  unfold tailWord_42702
  simp only [CollatzResearch.WordTrace]
  refine ⟨194683736413177720761295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1038313260870281177393573 194683736413177720761295)
  ·
    refine ⟨292025604619766581141943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194683736413177720761295 292025604619766581141943)
    ·
      refine ⟨438038406929649871712915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292025604619766581141943 438038406929649871712915)
      ·
        refine ⟨657057610394474807569373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438038406929649871712915 657057610394474807569373)
        ·
          refine ⟨246396603897928052838515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 657057610394474807569373 246396603897928052838515)
          ·
            refine ⟨369594905846892079257773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246396603897928052838515 369594905846892079257773)
            ·
              refine ⟨138598089692584529721665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369594905846892079257773 138598089692584529721665)
              ·
                refine ⟨103948567269438397291249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138598089692584529721665 103948567269438397291249)
                ·
                  refine ⟨77961425452078797968437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103948567269438397291249 77961425452078797968437)
                  ·
                    refine ⟨7308883636132387309541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77961425452078797968437 7308883636132387309541)
                    ·
                      rfl

theorem cell23_42702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_42702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42702 prefixEnd_42702 := by exact prefixLift 42702
  have htrace : WordTrace (prefixWord ++ tailWord_42702) baseStart_42702 baseEnd_42702 := by
    simpa [prefixWord, tailWord_42702, baseEnd_42702] using wordTrace_append hprefix tailTrace_42702
  have hstable : (prefixWord ++ tailWord_42702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42702).length < 2 ^ (prefixWord ++ tailWord_42702).sum := by decide
  have hdescent : baseEnd_42702 < baseStart_42702 := by decide
  rcases family_descends (prefixWord ++ tailWord_42702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42706 : List Nat := [3, 2, 2, 2, 2, 2, 3, 2, 5]
def baseStart_42706 : Nat := 118140960795 + 42706 * 2 ^ 59
def prefixEnd_42706 : Nat := 4983230072969 + 3 ^ 40 * 42706 * 2
def baseEnd_42706 : Nat := 2436522759001682919845

theorem tailTrace_42706 : CollatzResearch.WordTrace tailWord_42706 prefixEnd_42706 2436522759001682919845 := by
  unfold tailWord_42706
  simp only [CollatzResearch.WordTrace]
  refine ⟨389403945822732612308993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1038410522193953632823981 389403945822732612308993)
  ·
    refine ⟨292052959367049459231745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 389403945822732612308993 292052959367049459231745)
    ·
      refine ⟨219039719525287094423809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292052959367049459231745 219039719525287094423809)
      ·
        refine ⟨164279789643965320817857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219039719525287094423809 164279789643965320817857)
        ·
          refine ⟨123209842232973990613393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164279789643965320817857 123209842232973990613393)
          ·
            refine ⟨92407381674730492960045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123209842232973990613393 92407381674730492960045)
            ·
              refine ⟨34652768128023934860017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92407381674730492960045 34652768128023934860017)
              ·
                refine ⟨25989576096017951145013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34652768128023934860017 25989576096017951145013)
                ·
                  refine ⟨2436522759001682919845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25989576096017951145013 2436522759001682919845)
                  ·
                    rfl

theorem cell23_42706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_42706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42706 prefixEnd_42706 := by exact prefixLift 42706
  have htrace : WordTrace (prefixWord ++ tailWord_42706) baseStart_42706 baseEnd_42706 := by
    simpa [prefixWord, tailWord_42706, baseEnd_42706] using wordTrace_append hprefix tailTrace_42706
  have hstable : (prefixWord ++ tailWord_42706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42706).length < 2 ^ (prefixWord ++ tailWord_42706).sum := by decide
  have hdescent : baseEnd_42706 < baseStart_42706 := by decide
  rcases family_descends (prefixWord ++ tailWord_42706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42717 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_42717 : Nat := 118140960795 + 42717 * 2 ^ 59
def prefixEnd_42717 : Nat := 4983230072969 + 3 ^ 40 * 42717 * 2
def baseEnd_42717 : Nat := 21934353118214603241055

theorem tailTrace_42717 : CollatzResearch.WordTrace tailWord_42717 prefixEnd_42717 21934353118214603241055 := by
  unfold tailWord_42717
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558016986251079327886405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1038677990834052885257603 1558016986251079327886405)
  ·
    refine ⟨292128184922077373978701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1558016986251079327886405 292128184922077373978701)
    ·
      refine ⟨109548069345779015242013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292128184922077373978701 109548069345779015242013)
      ·
        refine ⟨41080526004667130715755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109548069345779015242013 41080526004667130715755)
        ·
          refine ⟨61620789007000696073633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41080526004667130715755 61620789007000696073633)
          ·
            refine ⟨46215591755250522055225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61620789007000696073633 46215591755250522055225)
            ·
              refine ⟨34661693816437891541419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46215591755250522055225 34661693816437891541419)
              ·
                refine ⟨51992540724656837312129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34661693816437891541419 51992540724656837312129)
                ·
                  refine ⟨38994405543492627984097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51992540724656837312129 38994405543492627984097)
                  ·
                    refine ⟨29245804157619470988073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38994405543492627984097 29245804157619470988073)
                    ·
                      refine ⟨21934353118214603241055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 29245804157619470988073 21934353118214603241055)
                      ·
                        rfl

theorem cell23_42717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_42717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42717 prefixEnd_42717 := by exact prefixLift 42717
  have htrace : WordTrace (prefixWord ++ tailWord_42717) baseStart_42717 baseEnd_42717 := by
    simpa [prefixWord, tailWord_42717, baseEnd_42717] using wordTrace_append hprefix tailTrace_42717
  have hstable : (prefixWord ++ tailWord_42717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42717).length < 2 ^ (prefixWord ++ tailWord_42717).sum := by decide
  have hdescent : baseEnd_42717 < baseStart_42717 := by decide
  rcases family_descends (prefixWord ++ tailWord_42717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42732 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_42732 : Nat := 118140960795 + 42732 * 2 ^ 59
def prefixEnd_42732 : Nat := 4983230072969 + 3 ^ 40 * 42732 * 2
def baseEnd_42732 : Nat := 7314018442677348184495

theorem tailTrace_42732 : CollatzResearch.WordTrace tailWord_42732 prefixEnd_42732 7314018442677348184495 := by
  unfold tailWord_42732
  simp only [CollatzResearch.WordTrace]
  refine ⟨779282040598368444841225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1039042720797824593121633 779282040598368444841225)
  ·
    refine ⟨584461530448776333630919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 779282040598368444841225 584461530448776333630919)
    ·
      refine ⟨876692295673164500446379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 584461530448776333630919 876692295673164500446379)
      ·
        refine ⟨1315038443509746750669569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876692295673164500446379 1315038443509746750669569)
        ·
          refine ⟨986278832632310063002177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1315038443509746750669569 986278832632310063002177)
          ·
            refine ⟨739709124474232547251633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 986278832632310063002177 739709124474232547251633)
            ·
              refine ⟨554781843355674410438725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739709124474232547251633 554781843355674410438725)
              ·
                refine ⟨104021595629188951957261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554781843355674410438725 104021595629188951957261)
                ·
                  refine ⟨39008098360945856983973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104021595629188951957261 39008098360945856983973)
                  ·
                    refine ⟨7314018442677348184495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39008098360945856983973 7314018442677348184495)
                    ·
                      rfl

theorem cell23_42732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_42732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42732 prefixEnd_42732 := by exact prefixLift 42732
  have htrace : WordTrace (prefixWord ++ tailWord_42732) baseStart_42732 baseEnd_42732 := by
    simpa [prefixWord, tailWord_42732, baseEnd_42732] using wordTrace_append hprefix tailTrace_42732
  have hstable : (prefixWord ++ tailWord_42732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42732).length < 2 ^ (prefixWord ++ tailWord_42732).sum := by decide
  have hdescent : baseEnd_42732 < baseStart_42732 := by decide
  rcases family_descends (prefixWord ++ tailWord_42732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42762 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 6]
def baseStart_42762 : Nat := 118140960795 + 42762 * 2 ^ 59
def prefixEnd_42762 : Nat := 4983230072969 + 3 ^ 40 * 42762 * 2
def baseEnd_42762 : Nat := 2439717749740769686483

theorem tailTrace_42762 : CollatzResearch.WordTrace tailWord_42762 prefixEnd_42762 2439717749740769686483 := by
  unfold tailWord_42762
  simp only [CollatzResearch.WordTrace]
  refine ⟨389914567772013003318635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1039772180725368008849693 389914567772013003318635)
  ·
    refine ⟨584871851658019504977953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 389914567772013003318635 584871851658019504977953)
    ·
      refine ⟨438653888743514628733465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 584871851658019504977953 438653888743514628733465)
      ·
        refine ⟨328990416557635971550099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438653888743514628733465 328990416557635971550099)
        ·
          refine ⟨493485624836453957325149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328990416557635971550099 493485624836453957325149)
          ·
            refine ⟨185057109313670233996931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 493485624836453957325149 185057109313670233996931)
            ·
              refine ⟨277585663970505350995397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185057109313670233996931 277585663970505350995397)
              ·
                refine ⟨52047311994469753311637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277585663970505350995397 52047311994469753311637)
                ·
                  refine ⟨2439717749740769686483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52047311994469753311637 2439717749740769686483)
                  ·
                    rfl

theorem cell23_42762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_42762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42762 prefixEnd_42762 := by exact prefixLift 42762
  have htrace : WordTrace (prefixWord ++ tailWord_42762) baseStart_42762 baseEnd_42762 := by
    simpa [prefixWord, tailWord_42762, baseEnd_42762] using wordTrace_append hprefix tailTrace_42762
  have hstable : (prefixWord ++ tailWord_42762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42762).length < 2 ^ (prefixWord ++ tailWord_42762).sum := by decide
  have hdescent : baseEnd_42762 < baseStart_42762 := by decide
  rcases family_descends (prefixWord ++ tailWord_42762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42789 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 5, 1, 3]
def baseStart_42789 : Nat := 118140960795 + 42789 * 2 ^ 59
def prefixEnd_42789 : Nat := 4983230072969 + 3 ^ 40 * 42789 * 2
def baseEnd_42789 : Nat := 21971323725338321540723

theorem tailTrace_42789 : CollatzResearch.WordTrace tailWord_42789 prefixEnd_42789 21971323725338321540723 := by
  unfold tailWord_42789
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560643041990235624507421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1040428694660157083004947 1560643041990235624507421)
  ·
    refine ⟨585241140746338359190283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1560643041990235624507421 585241140746338359190283)
    ·
      refine ⟨877861711119507538785425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 585241140746338359190283 877861711119507538785425)
      ·
        refine ⟨658396283339630654089069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 877861711119507538785425 658396283339630654089069)
        ·
          refine ⟨246898606252361495283401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 658396283339630654089069 246898606252361495283401)
          ·
            refine ⟨185173954689271121462551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246898606252361495283401 185173954689271121462551)
            ·
              refine ⟨277760932033906682193827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185173954689271121462551 277760932033906682193827)
              ·
                refine ⟨416641398050860023290741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277760932033906682193827 416641398050860023290741)
                ·
                  refine ⟨39060131067268127183507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 416641398050860023290741 39060131067268127183507)
                  ·
                    refine ⟨58590196600902190775261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39060131067268127183507 58590196600902190775261)
                    ·
                      refine ⟨21971323725338321540723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 58590196600902190775261 21971323725338321540723)
                      ·
                        rfl

theorem cell23_42789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_42789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42789 prefixEnd_42789 := by exact prefixLift 42789
  have htrace : WordTrace (prefixWord ++ tailWord_42789) baseStart_42789 baseEnd_42789 := by
    simpa [prefixWord, tailWord_42789, baseEnd_42789] using wordTrace_append hprefix tailTrace_42789
  have hstable : (prefixWord ++ tailWord_42789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42789).length < 2 ^ (prefixWord ++ tailWord_42789).sum := by decide
  have hdescent : baseEnd_42789 < baseStart_42789 := by decide
  rcases family_descends (prefixWord ++ tailWord_42789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42842 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_42842 : Nat := 118140960795 + 42842 * 2 ^ 59
def prefixEnd_42842 : Nat := 4983230072969 + 3 ^ 40 * 42842 * 2
def baseEnd_42842 : Nat := 21998538200026614177979

theorem tailTrace_42842 : CollatzResearch.WordTrace tailWord_42842 prefixEnd_42842 21998538200026614177979 := by
  unfold tailWord_42842
  simp only [CollatzResearch.WordTrace]
  refine ⟨390644027699556419046695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1041717407198817117457853 390644027699556419046695)
  ·
    refine ⟨585966041549334628570043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 390644027699556419046695 585966041549334628570043)
    ·
      refine ⟨878949062324001942855065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 585966041549334628570043 878949062324001942855065)
      ·
        refine ⟨659211796743001457141299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 878949062324001942855065 659211796743001457141299)
        ·
          refine ⟨988817695114502185711949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659211796743001457141299 988817695114502185711949)
          ·
            refine ⟨370806635667938319641981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 988817695114502185711949 370806635667938319641981)
            ·
              refine ⟨139052488375476869865743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 370806635667938319641981 139052488375476869865743)
              ·
                refine ⟨208578732563215304798615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139052488375476869865743 208578732563215304798615)
                ·
                  refine ⟨312868098844822957197923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208578732563215304798615 312868098844822957197923)
                  ·
                    refine ⟨469302148267234435796885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 312868098844822957197923 469302148267234435796885)
                    ·
                      refine ⟨21998538200026614177979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 469302148267234435796885 21998538200026614177979)
                      ·
                        rfl

theorem cell23_42842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_42842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42842 prefixEnd_42842 := by exact prefixLift 42842
  have htrace : WordTrace (prefixWord ++ tailWord_42842) baseStart_42842 baseEnd_42842 := by
    simpa [prefixWord, tailWord_42842, baseEnd_42842] using wordTrace_append hprefix tailTrace_42842
  have hstable : (prefixWord ++ tailWord_42842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42842).length < 2 ^ (prefixWord ++ tailWord_42842).sum := by decide
  have hdescent : baseEnd_42842 < baseStart_42842 := by decide
  rcases family_descends (prefixWord ++ tailWord_42842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42880 : List Nat := [2, 1, 1, 2, 1, 2, 7, 2, 1, 2, 2]
def baseStart_42880 : Nat := 118140960795 + 42880 * 2 ^ 59
def prefixEnd_42880 : Nat := 4983230072969 + 3 ^ 40 * 42880 * 2
def baseEnd_42880 : Nat := 22018050464897465502805

theorem tailTrace_42880 : CollatzResearch.WordTrace tailWord_42880 prefixEnd_42880 22018050464897465502805 := by
  unfold tailWord_42880
  simp only [CollatzResearch.WordTrace]
  refine ⟨781981042330279083035047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1042641389773705444046729 781981042330279083035047)
  ·
    refine ⟨1172971563495418624552571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 781981042330279083035047 1172971563495418624552571)
    ·
      refine ⟨1759457345243127936828857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172971563495418624552571 1759457345243127936828857)
      ·
        refine ⟨1319593008932345952621643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1759457345243127936828857 1319593008932345952621643)
        ·
          refine ⟨1979389513398518928932465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319593008932345952621643 1979389513398518928932465)
          ·
            refine ⟨1484542135048889196699349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1979389513398518928932465 1484542135048889196699349)
            ·
              refine ⟨34793956290208340547641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1484542135048889196699349 34793956290208340547641)
              ·
                refine ⟨26095467217656255410731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34793956290208340547641 26095467217656255410731)
                ·
                  refine ⟨39143200826484383116097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26095467217656255410731 39143200826484383116097)
                  ·
                    refine ⟨29357400619863287337073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39143200826484383116097 29357400619863287337073)
                    ·
                      refine ⟨22018050464897465502805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 29357400619863287337073 22018050464897465502805)
                      ·
                        rfl

theorem cell23_42880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 1, 2, 2].length) (baseStart_42880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42880 prefixEnd_42880 := by exact prefixLift 42880
  have htrace : WordTrace (prefixWord ++ tailWord_42880) baseStart_42880 baseEnd_42880 := by
    simpa [prefixWord, tailWord_42880, baseEnd_42880] using wordTrace_append hprefix tailTrace_42880
  have hstable : (prefixWord ++ tailWord_42880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42880).length < 2 ^ (prefixWord ++ tailWord_42880).sum := by decide
  have hdescent : baseEnd_42880 < baseStart_42880 := by decide
  rcases family_descends (prefixWord ++ tailWord_42880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42890 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 2, 4]
def baseStart_42890 : Nat := 118140960795 + 42890 * 2 ^ 59
def prefixEnd_42890 : Nat := 4983230072969 + 3 ^ 40 * 42890 * 2
def baseEnd_42890 : Nat := 7341061757147475459253

theorem tailTrace_42890 : CollatzResearch.WordTrace tailWord_42890 prefixEnd_42890 7341061757147475459253 := by
  unfold tailWord_42890
  simp only [CollatzResearch.WordTrace]
  refine ⟨391081703656082468483531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1042884543082886582622749 391081703656082468483531)
  ·
    refine ⟨586622555484123702725297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 391081703656082468483531 586622555484123702725297)
    ·
      refine ⟨439966916613092777043973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 586622555484123702725297 439966916613092777043973)
      ·
        refine ⟨82493796864954895695745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 439966916613092777043973 82493796864954895695745)
        ·
          refine ⟨61870347648716171771809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82493796864954895695745 61870347648716171771809)
          ·
            refine ⟨46402760736537128828857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61870347648716171771809 46402760736537128828857)
            ·
              refine ⟨34802070552402846621643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46402760736537128828857 34802070552402846621643)
              ·
                refine ⟨52203105828604269932465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34802070552402846621643 52203105828604269932465)
                ·
                  refine ⟨39152329371453202449349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52203105828604269932465 39152329371453202449349)
                  ·
                    refine ⟨7341061757147475459253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39152329371453202449349 7341061757147475459253)
                    ·
                      rfl

theorem cell23_42890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_42890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42890 prefixEnd_42890 := by exact prefixLift 42890
  have htrace : WordTrace (prefixWord ++ tailWord_42890) baseStart_42890 baseEnd_42890 := by
    simpa [prefixWord, tailWord_42890, baseEnd_42890] using wordTrace_append hprefix tailTrace_42890
  have hstable : (prefixWord ++ tailWord_42890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42890).length < 2 ^ (prefixWord ++ tailWord_42890).sum := by decide
  have hdescent : baseEnd_42890 < baseStart_42890 := by decide
  rcases family_descends (prefixWord ++ tailWord_42890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42912 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 4, 6]
def baseStart_42912 : Nat := 118140960795 + 42912 * 2 ^ 59
def prefixEnd_42912 : Nat := 4983230072969 + 3 ^ 40 * 42912 * 2
def baseEnd_42912 : Nat := 7344827281947113434219

theorem tailTrace_42912 : CollatzResearch.WordTrace tailWord_42912 prefixEnd_42912 7344827281947113434219 := by
  unfold tailWord_42912
  simp only [CollatzResearch.WordTrace]
  refine ⟨782564610272313815617495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1043419480363085087489993 782564610272313815617495)
  ·
    refine ⟨1173846915408470723426243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 782564610272313815617495 1173846915408470723426243)
    ·
      refine ⟨1760770373112706085139365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1173846915408470723426243 1760770373112706085139365)
      ·
        refine ⟨330144444958632390963631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1760770373112706085139365 330144444958632390963631)
        ·
          refine ⟨495216667437948586445447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330144444958632390963631 495216667437948586445447)
          ·
            refine ⟨742825001156922879668171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495216667437948586445447 742825001156922879668171)
            ·
              refine ⟨1114237501735384319502257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742825001156922879668171 1114237501735384319502257)
              ·
                refine ⟨835678126301538239626693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114237501735384319502257 835678126301538239626693)
                ·
                  refine ⟨156689648681538419930005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835678126301538239626693 156689648681538419930005)
                  ·
                    refine ⟨7344827281947113434219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 156689648681538419930005 7344827281947113434219)
                    ·
                      rfl

theorem cell23_42912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_42912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_42912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_42912 prefixEnd_42912 := by exact prefixLift 42912
  have htrace : WordTrace (prefixWord ++ tailWord_42912) baseStart_42912 baseEnd_42912 := by
    simpa [prefixWord, tailWord_42912, baseEnd_42912] using wordTrace_append hprefix tailTrace_42912
  have hstable : (prefixWord ++ tailWord_42912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42912).length < 2 ^ (prefixWord ++ tailWord_42912).sum := by decide
  have hdescent : baseEnd_42912 < baseStart_42912 := by decide
  rcases family_descends (prefixWord ++ tailWord_42912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43006 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_43006 : Nat := 118140960795 + 43006 * 2 ^ 59
def prefixEnd_43006 : Nat := 4983230072969 + 3 ^ 40 * 43006 * 2
def baseEnd_43006 : Nat := 7360916342454657509075

theorem tailTrace_43006 : CollatzResearch.WordTrace tailWord_43006 prefixEnd_43006 7360916342454657509075 := by
  unfold tailWord_43006
  simp only [CollatzResearch.WordTrace]
  refine ⟨196069710275510210644609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1045705121469387790104581 196069710275510210644609)
  ·
    refine ⟨147052282706632657983457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196069710275510210644609 147052282706632657983457)
    ·
      refine ⟨110289212029974493487593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147052282706632657983457 110289212029974493487593)
      ·
        refine ⟨82716909022480870115695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110289212029974493487593 82716909022480870115695)
        ·
          refine ⟨124075363533721305173543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82716909022480870115695 124075363533721305173543)
          ·
            refine ⟨186113045300581957760315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124075363533721305173543 186113045300581957760315)
            ·
              refine ⟨279169567950872936640473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186113045300581957760315 279169567950872936640473)
              ·
                refine ⟨209377175963154702480355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279169567950872936640473 209377175963154702480355)
                ·
                  refine ⟨314065763944732053720533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209377175963154702480355 314065763944732053720533)
                  ·
                    refine ⟨7360916342454657509075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 314065763944732053720533 7360916342454657509075)
                    ·
                      rfl

theorem cell23_43006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_43006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43006 prefixEnd_43006 := by exact prefixLift 43006
  have htrace : WordTrace (prefixWord ++ tailWord_43006) baseStart_43006 baseEnd_43006 := by
    simpa [prefixWord, tailWord_43006, baseEnd_43006] using wordTrace_append hprefix tailTrace_43006
  have hstable : (prefixWord ++ tailWord_43006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43006).length < 2 ^ (prefixWord ++ tailWord_43006).sum := by decide
  have hdescent : baseEnd_43006 < baseStart_43006 := by decide
  rcases family_descends (prefixWord ++ tailWord_43006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43009 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_43009 : Nat := 118140960795 + 43009 * 2 ^ 59
def prefixEnd_43009 : Nat := 4983230072969 + 3 ^ 40 * 43009 * 2
def baseEnd_43009 : Nat := 22084289469327460789711

theorem tailTrace_43009 : CollatzResearch.WordTrace tailWord_43009 prefixEnd_43009 22084289469327460789711 := by
  unfold tailWord_43009
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568667101193213197516081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1045778067462142131677387 1568667101193213197516081)
  ·
    refine ⟨1176500325894909898137061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1568667101193213197516081 1176500325894909898137061)
    ·
      refine ⟨220593811105295605900699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1176500325894909898137061 220593811105295605900699)
      ·
        refine ⟨330890716657943408851049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220593811105295605900699 330890716657943408851049)
        ·
          refine ⟨248168037493457556638287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330890716657943408851049 248168037493457556638287)
          ·
            refine ⟨372252056240186334957431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248168037493457556638287 372252056240186334957431)
            ·
              refine ⟨558378084360279502436147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372252056240186334957431 558378084360279502436147)
              ·
                refine ⟨837567126540419253654221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558378084360279502436147 837567126540419253654221)
                ·
                  refine ⟨314087672452657220120333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837567126540419253654221 314087672452657220120333)
                  ·
                    refine ⟨117782877169746457545125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 314087672452657220120333 117782877169746457545125)
                    ·
                      refine ⟨22084289469327460789711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 117782877169746457545125 22084289469327460789711)
                      ·
                        rfl

theorem cell23_43009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_43009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43009 prefixEnd_43009 := by exact prefixLift 43009
  have htrace : WordTrace (prefixWord ++ tailWord_43009) baseStart_43009 baseEnd_43009 := by
    simpa [prefixWord, tailWord_43009, baseEnd_43009] using wordTrace_append hprefix tailTrace_43009
  have hstable : (prefixWord ++ tailWord_43009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43009).length < 2 ^ (prefixWord ++ tailWord_43009).sum := by decide
  have hdescent : baseEnd_43009 < baseStart_43009 := by decide
  rcases family_descends (prefixWord ++ tailWord_43009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43116 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_43116 : Nat := 118140960795 + 43116 * 2 ^ 59
def prefixEnd_43116 : Nat := 4983230072969 + 3 ^ 40 * 43116 * 2
def baseEnd_43116 : Nat := 22139231899358542151719

theorem tailTrace_43116 : CollatzResearch.WordTrace tailWord_43116 prefixEnd_43116 22139231899358542151719 := by
  unfold tailWord_43116
  simp only [CollatzResearch.WordTrace]
  refine ⟨786284855902785235830601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1048379807870380314440801 786284855902785235830601)
  ·
    refine ⟨589713641927088926872951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 786284855902785235830601 589713641927088926872951)
    ·
      refine ⟨884570462890633390309427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 589713641927088926872951 884570462890633390309427)
      ·
        refine ⟨1326855694335950085464141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884570462890633390309427 1326855694335950085464141)
        ·
          refine ⟨497570885375981282049053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1326855694335950085464141 497570885375981282049053)
          ·
            refine ⟨186589082015992980768395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 497570885375981282049053 186589082015992980768395)
            ·
              refine ⟨279883623023989471152593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186589082015992980768395 279883623023989471152593)
              ·
                refine ⟨209912717267992103364445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279883623023989471152593 209912717267992103364445)
                ·
                  refine ⟨78717268975497038761667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209912717267992103364445 78717268975497038761667)
                  ·
                    refine ⟨118075903463245558142501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78717268975497038761667 118075903463245558142501)
                    ·
                      refine ⟨22139231899358542151719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 118075903463245558142501 22139231899358542151719)
                      ·
                        rfl

theorem cell23_43116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_43116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43116 prefixEnd_43116 := by exact prefixLift 43116
  have htrace : WordTrace (prefixWord ++ tailWord_43116) baseStart_43116 baseEnd_43116 := by
    simpa [prefixWord, tailWord_43116, baseEnd_43116] using wordTrace_append hprefix tailTrace_43116
  have hstable : (prefixWord ++ tailWord_43116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43116).length < 2 ^ (prefixWord ++ tailWord_43116).sum := by decide
  have hdescent : baseEnd_43116 < baseStart_43116 := by decide
  rcases family_descends (prefixWord ++ tailWord_43116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43137 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_43137 : Nat := 118140960795 + 43137 * 2 ^ 59
def prefixEnd_43137 : Nat := 4983230072969 + 3 ^ 40 * 43137 * 2
def baseEnd_43137 : Nat := 22150014993102959989123

theorem tailTrace_43137 : CollatzResearch.WordTrace tailWord_43137 prefixEnd_43137 22150014993102959989123 := by
  unfold tailWord_43137
  simp only [CollatzResearch.WordTrace]
  refine ⟨1573335644729491058175665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1048890429819660705450443 1573335644729491058175665)
  ·
    refine ⟨1180001733547118293631749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1573335644729491058175665 1180001733547118293631749)
    ·
      refine ⟨221250325040084680055953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1180001733547118293631749 221250325040084680055953)
      ·
        refine ⟨165937743780063510041965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221250325040084680055953 165937743780063510041965)
        ·
          refine ⟨62226653917523816265737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165937743780063510041965 62226653917523816265737)
          ·
            refine ⟨46669990438142862199303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62226653917523816265737 46669990438142862199303)
            ·
              refine ⟨70004985657214293298955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46669990438142862199303 70004985657214293298955)
              ·
                refine ⟨105007478485821439948433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70004985657214293298955 105007478485821439948433)
                ·
                  refine ⟨78755608864366079961325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105007478485821439948433 78755608864366079961325)
                  ·
                    refine ⟨29533353324137279985497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78755608864366079961325 29533353324137279985497)
                    ·
                      refine ⟨22150014993102959989123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 29533353324137279985497 22150014993102959989123)
                      ·
                        rfl

theorem cell23_43137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_43137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43137 prefixEnd_43137 := by exact prefixLift 43137
  have htrace : WordTrace (prefixWord ++ tailWord_43137) baseStart_43137 baseEnd_43137 := by
    simpa [prefixWord, tailWord_43137, baseEnd_43137] using wordTrace_append hprefix tailTrace_43137
  have hstable : (prefixWord ++ tailWord_43137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43137).length < 2 ^ (prefixWord ++ tailWord_43137).sum := by decide
  have hdescent : baseEnd_43137 < baseStart_43137 := by decide
  rcases family_descends (prefixWord ++ tailWord_43137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43150 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_43150 : Nat := 118140960795 + 43150 * 2 ^ 59
def prefixEnd_43150 : Nat := 4983230072969 + 3 ^ 40 * 43150 * 2
def baseEnd_43150 : Nat := 22156690241611409126563

theorem tailTrace_43150 : CollatzResearch.WordTrace tailWord_43150 prefixEnd_43150 22156690241611409126563 := by
  unfold tailWord_43150
  simp only [CollatzResearch.WordTrace]
  refine ⟨196726224210299284799863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1049206529121596185599269 196726224210299284799863)
  ·
    refine ⟨295089336315448927199795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196726224210299284799863 295089336315448927199795)
    ·
      refine ⟨442634004473173390799693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295089336315448927199795 442634004473173390799693)
      ·
        refine ⟨165987751677440021549885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442634004473173390799693 165987751677440021549885)
        ·
          refine ⟨62245406879040008081207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165987751677440021549885 62245406879040008081207)
          ·
            refine ⟨93368110318560012121811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62245406879040008081207 93368110318560012121811)
            ·
              refine ⟨140052165477840018182717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93368110318560012121811 140052165477840018182717)
              ·
                refine ⟨52519562054190006818519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140052165477840018182717 52519562054190006818519)
                ·
                  refine ⟨78779343081285010227779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52519562054190006818519 78779343081285010227779)
                  ·
                    refine ⟨118169014621927515341669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78779343081285010227779 118169014621927515341669)
                    ·
                      refine ⟨22156690241611409126563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 118169014621927515341669 22156690241611409126563)
                      ·
                        rfl

theorem cell23_43150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_43150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43150 prefixEnd_43150 := by exact prefixLift 43150
  have htrace : WordTrace (prefixWord ++ tailWord_43150) baseStart_43150 baseEnd_43150 := by
    simpa [prefixWord, tailWord_43150, baseEnd_43150] using wordTrace_append hprefix tailTrace_43150
  have hstable : (prefixWord ++ tailWord_43150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43150).length < 2 ^ (prefixWord ++ tailWord_43150).sum := by decide
  have hdescent : baseEnd_43150 < baseStart_43150 := by decide
  rcases family_descends (prefixWord ++ tailWord_43150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43167 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 3, 2, 2]
def baseStart_43167 : Nat := 118140960795 + 43167 * 2 ^ 59
def prefixEnd_43167 : Nat := 4983230072969 + 3 ^ 40 * 43167 * 2
def baseEnd_43167 : Nat := 22165419412737842613985

theorem tailTrace_43167 : CollatzResearch.WordTrace tailWord_43167 prefixEnd_43167 22165419412737842613985 := by
  unfold tailWord_43167
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574429834620806181767755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1049619889747204121178503 1574429834620806181767755)
  ·
    refine ⟨2361644751931209272651633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1574429834620806181767755 2361644751931209272651633)
    ·
      refine ⟨1771233563948406954488725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2361644751931209272651633 1771233563948406954488725)
      ·
        refine ⟨83026573310081575991659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1771233563948406954488725 83026573310081575991659)
        ·
          refine ⟨124539859965122363987489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83026573310081575991659 124539859965122363987489)
          ·
            refine ⟨93404894973841772990617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124539859965122363987489 93404894973841772990617)
            ·
              refine ⟨70053671230381329742963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93404894973841772990617 70053671230381329742963)
              ·
                refine ⟨105080506845571994614445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70053671230381329742963 105080506845571994614445)
                ·
                  refine ⟨39405190067089497980417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105080506845571994614445 39405190067089497980417)
                  ·
                    refine ⟨29553892550317123485313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39405190067089497980417 29553892550317123485313)
                    ·
                      refine ⟨22165419412737842613985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 29553892550317123485313 22165419412737842613985)
                      ·
                        rfl

theorem cell23_43167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_43167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43167 prefixEnd_43167 := by exact prefixLift 43167
  have htrace : WordTrace (prefixWord ++ tailWord_43167) baseStart_43167 baseEnd_43167 := by
    simpa [prefixWord, tailWord_43167, baseEnd_43167] using wordTrace_append hprefix tailTrace_43167
  have hstable : (prefixWord ++ tailWord_43167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43167).length < 2 ^ (prefixWord ++ tailWord_43167).sum := by decide
  have hdescent : baseEnd_43167 < baseStart_43167 := by decide
  rcases family_descends (prefixWord ++ tailWord_43167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43210 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2]
def baseStart_43210 : Nat := 118140960795 + 43210 * 2 ^ 59
def prefixEnd_43210 : Nat := 4983230072969 + 3 ^ 40 * 43210 * 2
def baseEnd_43210 : Nat := 22187499080881174376287

theorem tailTrace_43210 : CollatzResearch.WordTrace tailWord_43210 prefixEnd_43210 22187499080881174376287 := by
  unfold tailWord_43210
  simp only [CollatzResearch.WordTrace]
  refine ⟨393999543366256131395771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1050665448976683017055389 393999543366256131395771)
  ·
    refine ⟨590999315049384197093657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393999543366256131395771 590999315049384197093657)
    ·
      refine ⟨443249486287038147820243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 590999315049384197093657 443249486287038147820243)
      ·
        refine ⟨664874229430557221730365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443249486287038147820243 664874229430557221730365)
        ·
          refine ⟨249327836036458958148887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 664874229430557221730365 249327836036458958148887)
          ·
            refine ⟨373991754054688437223331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249327836036458958148887 373991754054688437223331)
            ·
              refine ⟨560987631082032655834997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373991754054688437223331 560987631082032655834997)
              ·
                refine ⟨52592590413940561484531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 560987631082032655834997 52592590413940561484531)
                ·
                  refine ⟨78888885620910842226797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52592590413940561484531 78888885620910842226797)
                  ·
                    refine ⟨29583332107841565835049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78888885620910842226797 29583332107841565835049)
                    ·
                      refine ⟨22187499080881174376287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 29583332107841565835049 22187499080881174376287)
                      ·
                        rfl

theorem cell23_43210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_43210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43210 prefixEnd_43210 := by exact prefixLift 43210
  have htrace : WordTrace (prefixWord ++ tailWord_43210) baseStart_43210 baseEnd_43210 := by
    simpa [prefixWord, tailWord_43210, baseEnd_43210] using wordTrace_append hprefix tailTrace_43210
  have hstable : (prefixWord ++ tailWord_43210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43210).length < 2 ^ (prefixWord ++ tailWord_43210).sum := by decide
  have hdescent : baseEnd_43210 < baseStart_43210 := by decide
  rcases family_descends (prefixWord ++ tailWord_43210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43236 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_43236 : Nat := 118140960795 + 43236 * 2 ^ 59
def prefixEnd_43236 : Nat := 4983230072969 + 3 ^ 40 * 43236 * 2
def baseEnd_43236 : Nat := 22200849577898072651167

theorem tailTrace_43236 : CollatzResearch.WordTrace tailWord_43236 prefixEnd_43236 22200849577898072651167 := by
  unfold tailWord_43236
  simp only [CollatzResearch.WordTrace]
  refine ⟨788473235685415483014781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1051297647580553977353041 788473235685415483014781)
  ·
    refine ⟨295677463382030806130543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 788473235685415483014781 295677463382030806130543)
    ·
      refine ⟨443516195073046209195815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295677463382030806130543 443516195073046209195815)
      ·
        refine ⟨665274292609569313793723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443516195073046209195815 665274292609569313793723)
        ·
          refine ⟨997911438914353970690585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665274292609569313793723 997911438914353970690585)
          ·
            refine ⟨748433579185765478017939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 997911438914353970690585 748433579185765478017939)
            ·
              refine ⟨1122650368778648217026909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748433579185765478017939 1122650368778648217026909)
              ·
                refine ⟨420993888291993081385091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1122650368778648217026909 420993888291993081385091)
                ·
                  refine ⟨631490832437989622077637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420993888291993081385091 631490832437989622077637)
                  ·
                    refine ⟨118404531082123054139557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 631490832437989622077637 118404531082123054139557)
                    ·
                      refine ⟨22200849577898072651167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 118404531082123054139557 22200849577898072651167)
                      ·
                        rfl

theorem cell23_43236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_43236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43236 prefixEnd_43236 := by exact prefixLift 43236
  have htrace : WordTrace (prefixWord ++ tailWord_43236) baseStart_43236 baseEnd_43236 := by
    simpa [prefixWord, tailWord_43236, baseEnd_43236] using wordTrace_append hprefix tailTrace_43236
  have hstable : (prefixWord ++ tailWord_43236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43236).length < 2 ^ (prefixWord ++ tailWord_43236).sum := by decide
  have hdescent : baseEnd_43236 < baseStart_43236 := by decide
  rcases family_descends (prefixWord ++ tailWord_43236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43246 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_43246 : Nat := 118140960795 + 43246 * 2 ^ 59
def prefixEnd_43246 : Nat := 4983230072969 + 3 ^ 40 * 43246 * 2
def baseEnd_43246 : Nat := 2467331598271448169569

theorem tailTrace_43246 : CollatzResearch.WordTrace tailWord_43246 prefixEnd_43246 2467331598271448169569 := by
  unfold tailWord_43246
  simp only [CollatzResearch.WordTrace]
  refine ⟨197163900166825334236699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1051540800889735115929061 197163900166825334236699)
  ·
    refine ⟨295745850250238001355049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197163900166825334236699 295745850250238001355049)
    ·
      refine ⟨221809387687678501016287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295745850250238001355049 221809387687678501016287)
      ·
        refine ⟨332714081531517751524431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221809387687678501016287 332714081531517751524431)
        ·
          refine ⟨499071122297276627286647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332714081531517751524431 499071122297276627286647)
          ·
            refine ⟨748606683445914940929971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499071122297276627286647 748606683445914940929971)
            ·
              refine ⟨1122910025168872411394957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748606683445914940929971 1122910025168872411394957)
              ·
                refine ⟨421091259438327154273109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1122910025168872411394957 421091259438327154273109)
                ·
                  refine ⟨2467331598271448169569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 421091259438327154273109 2467331598271448169569)
                  ·
                    rfl

theorem cell23_43246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_43246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43246 prefixEnd_43246 := by exact prefixLift 43246
  have htrace : WordTrace (prefixWord ++ tailWord_43246) baseStart_43246 baseEnd_43246 := by
    simpa [prefixWord, tailWord_43246, baseEnd_43246] using wordTrace_append hprefix tailTrace_43246
  have hstable : (prefixWord ++ tailWord_43246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43246).length < 2 ^ (prefixWord ++ tailWord_43246).sum := by decide
  have hdescent : baseEnd_43246 < baseStart_43246 := by decide
  rcases family_descends (prefixWord ++ tailWord_43246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43263 : List Nat := [1, 1, 2, 2, 1, 4, 2, 5, 5]
def baseStart_43263 : Nat := 118140960795 + 43263 * 2 ^ 59
def prefixEnd_43263 : Nat := 4983230072969 + 3 ^ 40 * 43263 * 2
def baseEnd_43263 : Nat := 2468301506174385223727

theorem tailTrace_43263 : CollatzResearch.WordTrace tailWord_43263 prefixEnd_43263 2468301506174385223727 := by
  unfold tailWord_43263
  simp only [CollatzResearch.WordTrace]
  refine ⟨1577931242273014577262443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1051954161515343051508295 1577931242273014577262443)
  ·
    refine ⟨2366896863409521865893665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1577931242273014577262443 2366896863409521865893665)
    ·
      refine ⟨1775172647557141399420249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2366896863409521865893665 1775172647557141399420249)
      ·
        refine ⟨1331379485667856049565187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1775172647557141399420249 1331379485667856049565187)
        ·
          refine ⟨1997069228501784074347781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1331379485667856049565187 1997069228501784074347781)
          ·
            refine ⟨374450480344084513940209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1997069228501784074347781 374450480344084513940209)
            ·
              refine ⟨280837860258063385455157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374450480344084513940209 280837860258063385455157)
              ·
                refine ⟨26328549399193442386421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 280837860258063385455157 26328549399193442386421)
                ·
                  refine ⟨2468301506174385223727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26328549399193442386421 2468301506174385223727)
                  ·
                    rfl

theorem cell23_43263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 5].length) (baseStart_43263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43263 prefixEnd_43263 := by exact prefixLift 43263
  have htrace : WordTrace (prefixWord ++ tailWord_43263) baseStart_43263 baseEnd_43263 := by
    simpa [prefixWord, tailWord_43263, baseEnd_43263] using wordTrace_append hprefix tailTrace_43263
  have hstable : (prefixWord ++ tailWord_43263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43263).length < 2 ^ (prefixWord ++ tailWord_43263).sum := by decide
  have hdescent : baseEnd_43263 < baseStart_43263 := by decide
  rcases family_descends (prefixWord ++ tailWord_43263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43290 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3]
def baseStart_43290 : Nat := 118140960795 + 43290 * 2 ^ 59
def prefixEnd_43290 : Nat := 4983230072969 + 3 ^ 40 * 43290 * 2
def baseEnd_43290 : Nat := 22228577533240861375919

theorem tailTrace_43290 : CollatzResearch.WordTrace tailWord_43290 prefixEnd_43290 22228577533240861375919 := by
  unfold tailWord_43290
  simp only [CollatzResearch.WordTrace]
  refine ⟨394729003293799547123831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1052610675450132125663549 394729003293799547123831)
  ·
    refine ⟨592093504940699320685747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 394729003293799547123831 592093504940699320685747)
    ·
      refine ⟨888140257411048981028621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592093504940699320685747 888140257411048981028621)
      ·
        refine ⟨333052596529143367885733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 888140257411048981028621 333052596529143367885733)
        ·
          refine ⟨62447361849214381478575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333052596529143367885733 62447361849214381478575)
          ·
            refine ⟨93671042773821572217863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62447361849214381478575 93671042773821572217863)
            ·
              refine ⟨140506564160732358326795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93671042773821572217863 140506564160732358326795)
              ·
                refine ⟨210759846241098537490193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140506564160732358326795 210759846241098537490193)
                ·
                  refine ⟨158069884680823903117645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210759846241098537490193 158069884680823903117645)
                  ·
                    refine ⟨59276206755308963669117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158069884680823903117645 59276206755308963669117)
                    ·
                      refine ⟨22228577533240861375919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 59276206755308963669117 22228577533240861375919)
                      ·
                        rfl

theorem cell23_43290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_43290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43290 prefixEnd_43290 := by exact prefixLift 43290
  have htrace : WordTrace (prefixWord ++ tailWord_43290) baseStart_43290 baseEnd_43290 := by
    simpa [prefixWord, tailWord_43290, baseEnd_43290] using wordTrace_append hprefix tailTrace_43290
  have hstable : (prefixWord ++ tailWord_43290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43290).length < 2 ^ (prefixWord ++ tailWord_43290).sum := by decide
  have hdescent : baseEnd_43290 < baseStart_43290 := by decide
  rcases family_descends (prefixWord ++ tailWord_43290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43340 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_43340 : Nat := 118140960795 + 43340 * 2 ^ 59
def prefixEnd_43340 : Nat := 4983230072969 + 3 ^ 40 * 43340 * 2
def baseEnd_43340 : Nat := 7418083855321888583563

theorem tailTrace_43340 : CollatzResearch.WordTrace tailWord_43340 prefixEnd_43340 7418083855321888583563 := by
  unfold tailWord_43340
  simp only [CollatzResearch.WordTrace]
  refine ⟨790369831497028363907737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1053826441996037818543649 790369831497028363907737)
  ·
    refine ⟨592777373622771272930803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 790369831497028363907737 592777373622771272930803)
    ·
      refine ⟨889166060434156909396205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592777373622771272930803 889166060434156909396205)
      ·
        refine ⟨333437272662808841023577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 889166060434156909396205 333437272662808841023577)
        ·
          refine ⟨250077954497106630767683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333437272662808841023577 250077954497106630767683)
          ·
            refine ⟨375116931745659946151525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250077954497106630767683 375116931745659946151525)
            ·
              refine ⟨70334424702311239903411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 375116931745659946151525 70334424702311239903411)
              ·
                refine ⟨105501637053466859855117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70334424702311239903411 105501637053466859855117)
                ·
                  refine ⟨39563113895050072445669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105501637053466859855117 39563113895050072445669)
                  ·
                    refine ⟨7418083855321888583563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39563113895050072445669 7418083855321888583563)
                    ·
                      rfl

theorem cell23_43340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_43340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43340 prefixEnd_43340 := by exact prefixLift 43340
  have htrace : WordTrace (prefixWord ++ tailWord_43340) baseStart_43340 baseEnd_43340 := by
    simpa [prefixWord, tailWord_43340, baseEnd_43340] using wordTrace_append hprefix tailTrace_43340
  have hstable : (prefixWord ++ tailWord_43340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43340).length < 2 ^ (prefixWord ++ tailWord_43340).sum := by decide
  have hdescent : baseEnd_43340 < baseStart_43340 := by decide
  rcases family_descends (prefixWord ++ tailWord_43340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43363 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 3]
def baseStart_43363 : Nat := 118140960795 + 43363 * 2 ^ 59
def prefixEnd_43363 : Nat := 4983230072969 + 3 ^ 40 * 43363 * 2
def baseEnd_43363 : Nat := 22266061621019075763083

theorem tailTrace_43363 : CollatzResearch.WordTrace tailWord_43363 prefixEnd_43363 22266061621019075763083 := by
  unfold tailWord_43363
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581578541910731655902743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1054385694607154437268495 1581578541910731655902743)
  ·
    refine ⟨2372367812866097483854115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1581578541910731655902743 2372367812866097483854115)
    ·
      refine ⟨3558551719299146225781173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2372367812866097483854115 3558551719299146225781173)
      ·
        refine ⟨333614223684294958666985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3558551719299146225781173 333614223684294958666985)
        ·
          refine ⟨250210667763221219000239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333614223684294958666985 250210667763221219000239)
          ·
            refine ⟨375316001644831828500359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250210667763221219000239 375316001644831828500359)
            ·
              refine ⟨562974002467247742750539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375316001644831828500359 562974002467247742750539)
              ·
                refine ⟨844461003700871614125809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562974002467247742750539 844461003700871614125809)
                ·
                  refine ⟨633345752775653710594357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 844461003700871614125809 633345752775653710594357)
                  ·
                    refine ⟨59376164322717535368221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 633345752775653710594357 59376164322717535368221)
                    ·
                      refine ⟨22266061621019075763083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 59376164322717535368221 22266061621019075763083)
                      ·
                        rfl

theorem cell23_43363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_43363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43363 prefixEnd_43363 := by exact prefixLift 43363
  have htrace : WordTrace (prefixWord ++ tailWord_43363) baseStart_43363 baseEnd_43363 := by
    simpa [prefixWord, tailWord_43363, baseEnd_43363] using wordTrace_append hprefix tailTrace_43363
  have hstable : (prefixWord ++ tailWord_43363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43363).length < 2 ^ (prefixWord ++ tailWord_43363).sum := by decide
  have hdescent : baseEnd_43363 < baseStart_43363 := by decide
  rcases family_descends (prefixWord ++ tailWord_43363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43413 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_43413 : Nat := 118140960795 + 43413 * 2 ^ 59
def prefixEnd_43413 : Nat := 4983230072969 + 3 ^ 40 * 43413 * 2
def baseEnd_43413 : Nat := 7430578551247960045951

theorem tailTrace_43413 : CollatzResearch.WordTrace tailWord_43413 prefixEnd_43413 7430578551247960045951 := by
  unfold tailWord_43413
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583402191729590195222893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1055601461153060130148595 1583402191729590195222893)
  ·
    refine ⟨593775821898596323208585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1583402191729590195222893 593775821898596323208585)
    ·
      refine ⟨445331866423947242406439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 593775821898596323208585 445331866423947242406439)
      ·
        refine ⟨667997799635920863609659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445331866423947242406439 667997799635920863609659)
        ·
          refine ⟨1001996699453881295414489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667997799635920863609659 1001996699453881295414489)
          ·
            refine ⟨751497524590410971560867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001996699453881295414489 751497524590410971560867)
            ·
              refine ⟨1127246286885616457341301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751497524590410971560867 1127246286885616457341301)
              ·
                refine ⟨105679339395526542875747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1127246286885616457341301 105679339395526542875747)
                ·
                  refine ⟨158519009093289814313621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105679339395526542875747 158519009093289814313621)
                  ·
                    refine ⟨7430578551247960045951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 158519009093289814313621 7430578551247960045951)
                    ·
                      rfl

theorem cell23_43413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_43413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43413 prefixEnd_43413 := by exact prefixLift 43413
  have htrace : WordTrace (prefixWord ++ tailWord_43413) baseStart_43413 baseEnd_43413 := by
    simpa [prefixWord, tailWord_43413, baseEnd_43413] using wordTrace_append hprefix tailTrace_43413
  have hstable : (prefixWord ++ tailWord_43413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43413).length < 2 ^ (prefixWord ++ tailWord_43413).sum := by decide
  have hdescent : baseEnd_43413 < baseStart_43413 := by decide
  rcases family_descends (prefixWord ++ tailWord_43413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43447 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 2, 4]
def baseStart_43447 : Nat := 118140960795 + 43447 * 2 ^ 59
def prefixEnd_43447 : Nat := 4983230072969 + 3 ^ 40 * 43447 * 2
def baseEnd_43447 : Nat := 7436397998665582370899

theorem tailTrace_43447 : CollatzResearch.WordTrace tailWord_43447 prefixEnd_43447 7436397998665582370899 := by
  unfold tailWord_43447
  simp only [CollatzResearch.WordTrace]
  refine ⟨1584642273606414001960595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1056428182404276001307063 1584642273606414001960595)
  ·
    refine ⟨2376963410409621002940893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1584642273606414001960595 2376963410409621002940893)
    ·
      refine ⟨891361278903607876102835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2376963410409621002940893 891361278903607876102835)
      ·
        refine ⟨1337041918355411814154253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891361278903607876102835 1337041918355411814154253)
        ·
          refine ⟨501390719383279430307845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1337041918355411814154253 501390719383279430307845)
          ·
            refine ⟨94010759884364893182721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 501390719383279430307845 94010759884364893182721)
            ·
              refine ⟨70508069913273669887041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94010759884364893182721 70508069913273669887041)
              ·
                refine ⟨52881052434955252415281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70508069913273669887041 52881052434955252415281)
                ·
                  refine ⟨39660789326216439311461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52881052434955252415281 39660789326216439311461)
                  ·
                    refine ⟨7436397998665582370899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39660789326216439311461 7436397998665582370899)
                    ·
                      rfl

theorem cell23_43447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_43447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43447 prefixEnd_43447 := by exact prefixLift 43447
  have htrace : WordTrace (prefixWord ++ tailWord_43447) baseStart_43447 baseEnd_43447 := by
    simpa [prefixWord, tailWord_43447, baseEnd_43447] using wordTrace_append hprefix tailTrace_43447
  have hstable : (prefixWord ++ tailWord_43447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43447).length < 2 ^ (prefixWord ++ tailWord_43447).sum := by decide
  have hdescent : baseEnd_43447 < baseStart_43447 := by decide
  rcases family_descends (prefixWord ++ tailWord_43447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43491 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 1, 2, 3]
def baseStart_43491 : Nat := 118140960795 + 43491 * 2 ^ 59
def prefixEnd_43491 : Nat := 4983230072969 + 3 ^ 40 * 43491 * 2
def baseEnd_43491 : Nat := 22331787144794574962495

theorem tailTrace_43491 : CollatzResearch.WordTrace tailWord_43491 prefixEnd_43491 22331787144794574962495 := by
  unfold tailWord_43491
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586247085447009516562327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1057498056964673011041551 1586247085447009516562327)
  ·
    refine ⟨2379370628170514274843491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1586247085447009516562327 2379370628170514274843491)
    ·
      refine ⟨3569055942255771412265237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2379370628170514274843491 3569055942255771412265237)
      ·
        refine ⟨167299497293239284949933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3569055942255771412265237 167299497293239284949933)
        ·
          refine ⟨62737311484964731856225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167299497293239284949933 62737311484964731856225)
          ·
            refine ⟨47052983613723548892169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62737311484964731856225 47052983613723548892169)
            ·
              refine ⟨35289737710292661669127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47052983613723548892169 35289737710292661669127)
              ·
                refine ⟨52934606565438992503691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35289737710292661669127 52934606565438992503691)
                ·
                  refine ⟨79401909848158488755537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52934606565438992503691 79401909848158488755537)
                  ·
                    refine ⟨59551432386118866566653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79401909848158488755537 59551432386118866566653)
                    ·
                      refine ⟨22331787144794574962495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 59551432386118866566653 22331787144794574962495)
                      ·
                        rfl

theorem cell23_43491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_43491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43491 prefixEnd_43491 := by exact prefixLift 43491
  have htrace : WordTrace (prefixWord ++ tailWord_43491) baseStart_43491 baseEnd_43491 := by
    simpa [prefixWord, tailWord_43491, baseEnd_43491] using wordTrace_append hprefix tailTrace_43491
  have hstable : (prefixWord ++ tailWord_43491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43491).length < 2 ^ (prefixWord ++ tailWord_43491).sum := by decide
  have hdescent : baseEnd_43491 < baseStart_43491 := by decide
  rcases family_descends (prefixWord ++ tailWord_43491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43521 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_43521 : Nat := 118140960795 + 43521 * 2 ^ 59
def prefixEnd_43521 : Nat := 4983230072969 + 3 ^ 40 * 43521 * 2
def baseEnd_43521 : Nat := 22347191564429457587357

theorem tailTrace_43521 : CollatzResearch.WordTrace tailWord_43521 prefixEnd_43521 22347191564429457587357 := by
  unfold tailWord_43521
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587341275338324640154417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1058227516892216426769611 1587341275338324640154417)
  ·
    refine ⟨1190505956503743480115813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1587341275338324640154417 1190505956503743480115813)
    ·
      refine ⟨223219866844451902521715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1190505956503743480115813 223219866844451902521715)
      ·
        refine ⟨334829800266677853782573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223219866844451902521715 334829800266677853782573)
        ·
          refine ⟨125561175100004195168465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334829800266677853782573 125561175100004195168465)
          ·
            refine ⟨94170881325003146376349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125561175100004195168465 94170881325003146376349)
            ·
              refine ⟨35314080496876179891131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94170881325003146376349 35314080496876179891131)
              ·
                refine ⟨52971120745314269836697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35314080496876179891131 52971120745314269836697)
                ·
                  refine ⟨39728340558985702377523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52971120745314269836697 39728340558985702377523)
                  ·
                    refine ⟨59592510838478553566285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39728340558985702377523 59592510838478553566285)
                    ·
                      refine ⟨22347191564429457587357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 59592510838478553566285 22347191564429457587357)
                      ·
                        rfl

theorem cell23_43521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_43521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43521 prefixEnd_43521 := by exact prefixLift 43521
  have htrace : WordTrace (prefixWord ++ tailWord_43521) baseStart_43521 baseEnd_43521 := by
    simpa [prefixWord, tailWord_43521, baseEnd_43521] using wordTrace_append hprefix tailTrace_43521
  have hstable : (prefixWord ++ tailWord_43521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43521).length < 2 ^ (prefixWord ++ tailWord_43521).sum := by decide
  have hdescent : baseEnd_43521 < baseStart_43521 := by decide
  rcases family_descends (prefixWord ++ tailWord_43521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43530 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_43530 : Nat := 118140960795 + 43530 * 2 ^ 59
def prefixEnd_43530 : Nat := 4983230072969 + 3 ^ 40 * 43530 * 2
def baseEnd_43530 : Nat := 22351812890319922374815

theorem tailTrace_43530 : CollatzResearch.WordTrace tailWord_43530 prefixEnd_43530 22351812890319922374815 := by
  unfold tailWord_43530
  simp only [CollatzResearch.WordTrace]
  refine ⟨396917383076429794308011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1058446354870479451488029 396917383076429794308011)
  ·
    refine ⟨595376074614644691462017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 396917383076429794308011 595376074614644691462017)
    ·
      refine ⟨446532055960983518596513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 595376074614644691462017 446532055960983518596513)
      ·
        refine ⟨334899041970737638947385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446532055960983518596513 334899041970737638947385)
        ·
          refine ⟨251174281478053229210539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334899041970737638947385 251174281478053229210539)
          ·
            refine ⟨376761422217079843815809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251174281478053229210539 376761422217079843815809)
            ·
              refine ⟨282571066662809882861857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376761422217079843815809 282571066662809882861857)
              ·
                refine ⟨211928299997107412146393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282571066662809882861857 211928299997107412146393)
                ·
                  refine ⟨158946224997830559109795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211928299997107412146393 158946224997830559109795)
                  ·
                    refine ⟨238419337496745838664693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158946224997830559109795 238419337496745838664693)
                    ·
                      refine ⟨22351812890319922374815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 238419337496745838664693 22351812890319922374815)
                      ·
                        rfl

theorem cell23_43530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_43530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43530 prefixEnd_43530 := by exact prefixLift 43530
  have htrace : WordTrace (prefixWord ++ tailWord_43530) baseStart_43530 baseEnd_43530 := by
    simpa [prefixWord, tailWord_43530, baseEnd_43530] using wordTrace_append hprefix tailTrace_43530
  have hstable : (prefixWord ++ tailWord_43530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43530).length < 2 ^ (prefixWord ++ tailWord_43530).sum := by decide
  have hdescent : baseEnd_43530 < baseStart_43530 := by decide
  rcases family_descends (prefixWord ++ tailWord_43530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43544 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 4, 2, 2]
def baseStart_43544 : Nat := 118140960795 + 43544 * 2 ^ 59
def prefixEnd_43544 : Nat := 4983230072969 + 3 ^ 40 * 43544 * 2
def baseEnd_43544 : Nat := 22359001619482867599751

theorem tailTrace_43544 : CollatzResearch.WordTrace tailWord_43544 prefixEnd_43544 22359001619482867599751 := by
  unfold tailWord_43544
  simp only [CollatzResearch.WordTrace]
  refine ⟨794090077127499784120843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1058786769503333045494457 794090077127499784120843)
  ·
    refine ⟨1191135115691249676181265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 794090077127499784120843 1191135115691249676181265)
    ·
      refine ⟨893351336768437257135949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1191135115691249676181265 893351336768437257135949)
      ·
        refine ⟨335006751288163971425981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 893351336768437257135949 335006751288163971425981)
        ·
          refine ⟨125627531733061489284743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335006751288163971425981 125627531733061489284743)
          ·
            refine ⟨188441297599592233927115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125627531733061489284743 188441297599592233927115)
            ·
              refine ⟨282661946399388350890673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188441297599592233927115 282661946399388350890673)
              ·
                refine ⟨211996459799541263168005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282661946399388350890673 211996459799541263168005)
                ·
                  refine ⟨39749336212413986844001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211996459799541263168005 39749336212413986844001)
                  ·
                    refine ⟨29812002159310490133001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39749336212413986844001 29812002159310490133001)
                    ·
                      refine ⟨22359001619482867599751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 29812002159310490133001 22359001619482867599751)
                      ·
                        rfl

theorem cell23_43544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_43544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43544 prefixEnd_43544 := by exact prefixLift 43544
  have htrace : WordTrace (prefixWord ++ tailWord_43544) baseStart_43544 baseEnd_43544 := by
    simpa [prefixWord, tailWord_43544, baseEnd_43544] using wordTrace_append hprefix tailTrace_43544
  have hstable : (prefixWord ++ tailWord_43544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43544).length < 2 ^ (prefixWord ++ tailWord_43544).sum := by decide
  have hdescent : baseEnd_43544 < baseStart_43544 := by decide
  rcases family_descends (prefixWord ++ tailWord_43544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43572 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_43572 : Nat := 118140960795 + 43572 * 2 ^ 59
def prefixEnd_43572 : Nat := 4983230072969 + 3 ^ 40 * 43572 * 2
def baseEnd_43572 : Nat := 22373379077808758049623

theorem tailTrace_43572 : CollatzResearch.WordTrace tailWord_43572 prefixEnd_43572 22373379077808758049623 := by
  unfold tailWord_43572
  simp only [CollatzResearch.WordTrace]
  refine ⟨794600699076780175130485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1059467598769040233507313 794600699076780175130485)
  ·
    refine ⟨74493815538448141418483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 794600699076780175130485 74493815538448141418483)
    ·
      refine ⟨111740723307672212127725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74493815538448141418483 111740723307672212127725)
      ·
        refine ⟨41902771240377079547897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111740723307672212127725 41902771240377079547897)
        ·
          refine ⟨31427078430282809660923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41902771240377079547897 31427078430282809660923)
          ·
            refine ⟨47140617645424214491385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31427078430282809660923 47140617645424214491385)
            ·
              refine ⟨35355463234068160868539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47140617645424214491385 35355463234068160868539)
              ·
                refine ⟨53033194851102241302809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35355463234068160868539 53033194851102241302809)
                ·
                  refine ⟨39774896138326680977107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53033194851102241302809 39774896138326680977107)
                  ·
                    refine ⟨59662344207490021465661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39774896138326680977107 59662344207490021465661)
                    ·
                      refine ⟨22373379077808758049623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 59662344207490021465661 22373379077808758049623)
                      ·
                        rfl

theorem cell23_43572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_43572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43572 prefixEnd_43572 := by exact prefixLift 43572
  have htrace : WordTrace (prefixWord ++ tailWord_43572) baseStart_43572 baseEnd_43572 := by
    simpa [prefixWord, tailWord_43572, baseEnd_43572] using wordTrace_append hprefix tailTrace_43572
  have hstable : (prefixWord ++ tailWord_43572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43572).length < 2 ^ (prefixWord ++ tailWord_43572).sum := by decide
  have hdescent : baseEnd_43572 < baseStart_43572 := by decide
  rcases family_descends (prefixWord ++ tailWord_43572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43578 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2]
def baseStart_43578 : Nat := 118140960795 + 43578 * 2 ^ 59
def prefixEnd_43578 : Nat := 4983230072969 + 3 ^ 40 * 43578 * 2
def baseEnd_43578 : Nat := 22376459961735734574595

theorem tailTrace_43578 : CollatzResearch.WordTrace tailWord_43578 prefixEnd_43578 22376459961735734574595 := by
  unfold tailWord_43578
  simp only [CollatzResearch.WordTrace]
  refine ⟨397355059032955843744847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1059613490754548916652925 397355059032955843744847)
  ·
    refine ⟨596032588549433765617271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 397355059032955843744847 596032588549433765617271)
    ·
      refine ⟨894048882824150648425907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 596032588549433765617271 894048882824150648425907)
      ·
        refine ⟨1341073324236225972638861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894048882824150648425907 1341073324236225972638861)
        ·
          refine ⟨502902496588584739739573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1341073324236225972638861 502902496588584739739573)
          ·
            refine ⟨47147109055179819350585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 502902496588584739739573 47147109055179819350585)
            ·
              refine ⟨35360331791384864512939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47147109055179819350585 35360331791384864512939)
              ·
                refine ⟨53040497687077296769409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35360331791384864512939 53040497687077296769409)
                ·
                  refine ⟨39780373265307972577057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53040497687077296769409 39780373265307972577057)
                  ·
                    refine ⟨29835279948980979432793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39780373265307972577057 29835279948980979432793)
                    ·
                      refine ⟨22376459961735734574595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 29835279948980979432793 22376459961735734574595)
                      ·
                        rfl

theorem cell23_43578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_43578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43578 prefixEnd_43578 := by exact prefixLift 43578
  have htrace : WordTrace (prefixWord ++ tailWord_43578) baseStart_43578 baseEnd_43578 := by
    simpa [prefixWord, tailWord_43578, baseEnd_43578] using wordTrace_append hprefix tailTrace_43578
  have hstable : (prefixWord ++ tailWord_43578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43578).length < 2 ^ (prefixWord ++ tailWord_43578).sum := by decide
  have hdescent : baseEnd_43578 < baseStart_43578 := by decide
  rcases family_descends (prefixWord ++ tailWord_43578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43617 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_43617 : Nat := 118140960795 + 43617 * 2 ^ 59
def prefixEnd_43617 : Nat := 4983230072969 + 3 ^ 40 * 43617 * 2
def baseEnd_43617 : Nat := 22396485707261081986915

theorem tailTrace_43617 : CollatzResearch.WordTrace tailWord_43617 prefixEnd_43617 22396485707261081986915 := by
  unfold tailWord_43617
  simp only [CollatzResearch.WordTrace]
  refine ⟨1590842682990533035649105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1060561788660355357099403 1590842682990533035649105)
  ·
    refine ⟨1193132012242899776736829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1590842682990533035649105 1193132012242899776736829)
    ·
      refine ⟨447424504591087416276311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1193132012242899776736829 447424504591087416276311)
      ·
        refine ⟨671136756886631124414467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447424504591087416276311 671136756886631124414467)
        ·
          refine ⟨1006705135329946686621701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671136756886631124414467 1006705135329946686621701)
          ·
            refine ⟨188757212874365003741569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1006705135329946686621701 188757212874365003741569)
            ·
              refine ⟨141567909655773752806177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188757212874365003741569 141567909655773752806177)
              ·
                refine ⟨106175932241830314604633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141567909655773752806177 106175932241830314604633)
                ·
                  refine ⟨79631949181372735953475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106175932241830314604633 79631949181372735953475)
                  ·
                    refine ⟨119447923772059103930213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79631949181372735953475 119447923772059103930213)
                    ·
                      refine ⟨22396485707261081986915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 119447923772059103930213 22396485707261081986915)
                      ·
                        rfl

theorem cell23_43617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_43617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43617 prefixEnd_43617 := by exact prefixLift 43617
  have htrace : WordTrace (prefixWord ++ tailWord_43617) baseStart_43617 baseEnd_43617 := by
    simpa [prefixWord, tailWord_43617, baseEnd_43617] using wordTrace_append hprefix tailTrace_43617
  have hstable : (prefixWord ++ tailWord_43617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43617).length < 2 ^ (prefixWord ++ tailWord_43617).sum := by decide
  have hdescent : baseEnd_43617 < baseStart_43617 := by decide
  rcases family_descends (prefixWord ++ tailWord_43617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43620 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_43620 : Nat := 118140960795 + 43620 * 2 ^ 59
def prefixEnd_43620 : Nat := 4983230072969 + 3 ^ 40 * 43620 * 2
def baseEnd_43620 : Nat := 22398026149224570249401

theorem tailTrace_43620 : CollatzResearch.WordTrace tailWord_43620 prefixEnd_43620 22398026149224570249401 := by
  unfold tailWord_43620
  simp only [CollatzResearch.WordTrace]
  refine ⟨795476050989832274004157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1060634734653109698672209 795476050989832274004157)
  ·
    refine ⟨298303519121187102751559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 795476050989832274004157 298303519121187102751559)
    ·
      refine ⟨447455278681780654127339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298303519121187102751559 447455278681780654127339)
      ·
        refine ⟨671182918022670981191009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447455278681780654127339 671182918022670981191009)
        ·
          refine ⟨503387188517003235893257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671182918022670981191009 503387188517003235893257)
          ·
            refine ⟨377540391387752426919943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503387188517003235893257 377540391387752426919943)
            ·
              refine ⟨566310587081628640379915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377540391387752426919943 566310587081628640379915)
              ·
                refine ⟨849465880622442960569873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566310587081628640379915 849465880622442960569873)
                ·
                  refine ⟨637099410466832220427405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 849465880622442960569873 637099410466832220427405)
                  ·
                    refine ⟨238912278925062082660277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637099410466832220427405 238912278925062082660277)
                    ·
                      refine ⟨22398026149224570249401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 238912278925062082660277 22398026149224570249401)
                      ·
                        rfl

theorem cell23_43620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_43620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43620 prefixEnd_43620 := by exact prefixLift 43620
  have htrace : WordTrace (prefixWord ++ tailWord_43620) baseStart_43620 baseEnd_43620 := by
    simpa [prefixWord, tailWord_43620, baseEnd_43620] using wordTrace_append hprefix tailTrace_43620
  have hstable : (prefixWord ++ tailWord_43620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43620).length < 2 ^ (prefixWord ++ tailWord_43620).sum := by decide
  have hdescent : baseEnd_43620 < baseStart_43620 := by decide
  rcases family_descends (prefixWord ++ tailWord_43620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43674 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 8]
def baseStart_43674 : Nat := 118140960795 + 43674 * 2 ^ 59
def prefixEnd_43674 : Nat := 4983230072969 + 3 ^ 40 * 43674 * 2
def baseEnd_43674 : Nat := 2491750456063039886017

theorem tailTrace_43674 : CollatzResearch.WordTrace tailWord_43674 prefixEnd_43674 2491750456063039886017 := by
  unfold tailWord_43674
  simp only [CollatzResearch.WordTrace]
  refine ⟨398230410946007942618519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1061947762522687846982717 398230410946007942618519)
  ·
    refine ⟨597345616419011913927779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 398230410946007942618519 597345616419011913927779)
    ·
      refine ⟨896018424628517870891669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597345616419011913927779 896018424628517870891669)
      ·
        refine ⟨42000863654461775198047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 896018424628517870891669 42000863654461775198047)
        ·
          refine ⟨63001295481692662797071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42000863654461775198047 63001295481692662797071)
          ·
            refine ⟨94501943222538994195607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63001295481692662797071 94501943222538994195607)
            ·
              refine ⟨141752914833808491293411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94501943222538994195607 141752914833808491293411)
              ·
                refine ⟨212629372250712736940117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141752914833808491293411 212629372250712736940117)
                ·
                  refine ⟨2491750456063039886017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 212629372250712736940117 2491750456063039886017)
                  ·
                    rfl

theorem cell23_43674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_43674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43674 prefixEnd_43674 := by exact prefixLift 43674
  have htrace : WordTrace (prefixWord ++ tailWord_43674) baseStart_43674 baseEnd_43674 := by
    simpa [prefixWord, tailWord_43674, baseEnd_43674] using wordTrace_append hprefix tailTrace_43674
  have hstable : (prefixWord ++ tailWord_43674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43674).length < 2 ^ (prefixWord ++ tailWord_43674).sum := by decide
  have hdescent : baseEnd_43674 < baseStart_43674 := by decide
  rcases family_descends (prefixWord ++ tailWord_43674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43701 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_43701 : Nat := 118140960795 + 43701 * 2 ^ 59
def prefixEnd_43701 : Nat := 4983230072969 + 3 ^ 40 * 43701 * 2
def baseEnd_43701 : Nat := 22439618082238753336529

theorem tailTrace_43701 : CollatzResearch.WordTrace tailWord_43701 prefixEnd_43701 22439618082238753336529 := by
  unfold tailWord_43701
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593906414686215381706957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1062604276457476921137971 1593906414686215381706957)
  ·
    refine ⟨597714905507330768140109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1593906414686215381706957 597714905507330768140109)
    ·
      refine ⟨224143089565249038052541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 597714905507330768140109 224143089565249038052541)
      ·
        refine ⟨84053658586968389269703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224143089565249038052541 84053658586968389269703)
        ·
          refine ⟨126080487880452583904555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84053658586968389269703 126080487880452583904555)
          ·
            refine ⟨189120731820678875856833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126080487880452583904555 189120731820678875856833)
            ·
              refine ⟨141840548865509156892625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189120731820678875856833 141840548865509156892625)
              ·
                refine ⟨106380411649131867669469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141840548865509156892625 106380411649131867669469)
                ·
                  refine ⟨39892654368424450376051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106380411649131867669469 39892654368424450376051)
                  ·
                    refine ⟨59838981552636675564077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39892654368424450376051 59838981552636675564077)
                    ·
                      refine ⟨22439618082238753336529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 59838981552636675564077 22439618082238753336529)
                      ·
                        rfl

theorem cell23_43701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_43701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43701 prefixEnd_43701 := by exact prefixLift 43701
  have htrace : WordTrace (prefixWord ++ tailWord_43701) baseStart_43701 baseEnd_43701 := by
    simpa [prefixWord, tailWord_43701, baseEnd_43701] using wordTrace_append hprefix tailTrace_43701
  have hstable : (prefixWord ++ tailWord_43701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43701).length < 2 ^ (prefixWord ++ tailWord_43701).sum := by decide
  have hdescent : baseEnd_43701 < baseStart_43701 := by decide
  rcases family_descends (prefixWord ++ tailWord_43701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43727 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 3]
def baseStart_43727 : Nat := 118140960795 + 43727 * 2 ^ 59
def prefixEnd_43727 : Nat := 4983230072969 + 3 ^ 40 * 43727 * 2
def baseEnd_43727 : Nat := 22452968579255651611409

theorem tailTrace_43727 : CollatzResearch.WordTrace tailWord_43727 prefixEnd_43727 22452968579255651611409 := by
  unfold tailWord_43727
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594854712592021822153435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1063236475061347881435623 1594854712592021822153435)
  ·
    refine ⟨2392282068888032733230153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1594854712592021822153435 2392282068888032733230153)
    ·
      refine ⟨1794211551666024549922615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2392282068888032733230153 1794211551666024549922615)
      ·
        refine ⟨2691317327499036824883923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794211551666024549922615 2691317327499036824883923)
        ·
          refine ⟨4036975991248555237325885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2691317327499036824883923 4036975991248555237325885)
          ·
            refine ⟨1513865996718208213997207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4036975991248555237325885 1513865996718208213997207)
            ·
              refine ⟨2270798995077312320995811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513865996718208213997207 2270798995077312320995811)
              ·
                refine ⟨3406198492615968481493717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2270798995077312320995811 3406198492615968481493717)
                ·
                  refine ⟨79832777170686761285009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3406198492615968481493717 79832777170686761285009)
                  ·
                    refine ⟨59874582878015070963757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79832777170686761285009 59874582878015070963757)
                    ·
                      refine ⟨22452968579255651611409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 59874582878015070963757 22452968579255651611409)
                      ·
                        rfl

theorem cell23_43727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 3].length) (baseStart_43727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43727 prefixEnd_43727 := by exact prefixLift 43727
  have htrace : WordTrace (prefixWord ++ tailWord_43727) baseStart_43727 baseEnd_43727 := by
    simpa [prefixWord, tailWord_43727, baseEnd_43727] using wordTrace_append hprefix tailTrace_43727
  have hstable : (prefixWord ++ tailWord_43727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43727).length < 2 ^ (prefixWord ++ tailWord_43727).sum := by decide
  have hdescent : baseEnd_43727 < baseStart_43727 := by decide
  rcases family_descends (prefixWord ++ tailWord_43727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43747 : List Nat := [1, 1, 1, 7, 1, 1, 1, 10]
def baseStart_43747 : Nat := 118140960795 + 43747 * 2 ^ 59
def prefixEnd_43747 : Nat := 4983230072969 + 3 ^ 40 * 43747 * 2
def baseEnd_43747 : Nat := 831971784901687902271

theorem tailTrace_43747 : CollatzResearch.WordTrace tailWord_43747 prefixEnd_43747 831971784901687902271 := by
  unfold tailWord_43747
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595584172519565237881495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1063722781679710158587663 1595584172519565237881495)
  ·
    refine ⟨2393376258779347856822243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1595584172519565237881495 2393376258779347856822243)
    ·
      refine ⟨3590064388169021785233365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2393376258779347856822243 3590064388169021785233365)
      ·
        refine ⟨84142134097711448091407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3590064388169021785233365 84142134097711448091407)
        ·
          refine ⟨126213201146567172137111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84142134097711448091407 126213201146567172137111)
          ·
            refine ⟨189319801719850758205667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126213201146567172137111 189319801719850758205667)
            ·
              refine ⟨283979702579776137308501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189319801719850758205667 283979702579776137308501)
              ·
                refine ⟨831971784901687902271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 283979702579776137308501 831971784901687902271)
                ·
                  rfl

theorem cell23_43747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 10].length) (baseStart_43747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43747 prefixEnd_43747 := by exact prefixLift 43747
  have htrace : WordTrace (prefixWord ++ tailWord_43747) baseStart_43747 baseEnd_43747 := by
    simpa [prefixWord, tailWord_43747, baseEnd_43747] using wordTrace_append hprefix tailTrace_43747
  have hstable : (prefixWord ++ tailWord_43747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43747).length < 2 ^ (prefixWord ++ tailWord_43747).sum := by decide
  have hdescent : baseEnd_43747 < baseStart_43747 := by decide
  rcases family_descends (prefixWord ++ tailWord_43747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43791 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 2, 1, 3]
def baseStart_43791 : Nat := 118140960795 + 43791 * 2 ^ 59
def prefixEnd_43791 : Nat := 4983230072969 + 3 ^ 40 * 43791 * 2
def baseEnd_43791 : Nat := 22485831341143401211115

theorem tailTrace_43791 : CollatzResearch.WordTrace tailWord_43791 prefixEnd_43791 22485831341143401211115 := by
  unfold tailWord_43791
  simp only [CollatzResearch.WordTrace]
  refine ⟨1597188984360160752483227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1064792656240107168322151 1597188984360160752483227)
  ·
    refine ⟨2395783476540241128724841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1597188984360160752483227 2395783476540241128724841)
    ·
      refine ⟨1796837607405180846543631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2395783476540241128724841 1796837607405180846543631)
      ·
        refine ⟨2695256411107771269815447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796837607405180846543631 2695256411107771269815447)
        ·
          refine ⟨4042884616661656904723171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695256411107771269815447 4042884616661656904723171)
          ·
            refine ⟨6064326924992485357084757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4042884616661656904723171 6064326924992485357084757)
            ·
              refine ⟨71066331152255687778337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 6064326924992485357084757 71066331152255687778337)
              ·
                refine ⟨53299748364191765833753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71066331152255687778337 53299748364191765833753)
                ·
                  refine ⟨39974811273143824375315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53299748364191765833753 39974811273143824375315)
                  ·
                    refine ⟨59962216909715736562973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39974811273143824375315 59962216909715736562973)
                    ·
                      refine ⟨22485831341143401211115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 59962216909715736562973 22485831341143401211115)
                      ·
                        rfl

theorem cell23_43791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 1, 3].length) (baseStart_43791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43791 prefixEnd_43791 := by exact prefixLift 43791
  have htrace : WordTrace (prefixWord ++ tailWord_43791) baseStart_43791 baseEnd_43791 := by
    simpa [prefixWord, tailWord_43791, baseEnd_43791] using wordTrace_append hprefix tailTrace_43791
  have hstable : (prefixWord ++ tailWord_43791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43791).length < 2 ^ (prefixWord ++ tailWord_43791).sum := by decide
  have hdescent : baseEnd_43791 < baseStart_43791 := by decide
  rcases family_descends (prefixWord ++ tailWord_43791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43797 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_43797 : Nat := 118140960795 + 43797 * 2 ^ 59
def prefixEnd_43797 : Nat := 4983230072969 + 3 ^ 40 * 43797 * 2
def baseEnd_43797 : Nat := 22488912225070377736087

theorem tailTrace_43797 : CollatzResearch.WordTrace tailWord_43797 prefixEnd_43797 22488912225070377736087 := by
  unfold tailWord_43797
  simp only [CollatzResearch.WordTrace]
  refine ⟨1597407822338423777201645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1064938548225615851467763 1597407822338423777201645)
  ·
    refine ⟨599027933376908916450617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1597407822338423777201645 599027933376908916450617)
    ·
      refine ⟨449270950032681687337963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 599027933376908916450617 449270950032681687337963)
      ·
        refine ⟨673906425049022531006945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449270950032681687337963 673906425049022531006945)
        ·
          refine ⟨505429818786766898255209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673906425049022531006945 505429818786766898255209)
          ·
            refine ⟨379072364090075173691407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505429818786766898255209 379072364090075173691407)
            ·
              refine ⟨568608546135112760537111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379072364090075173691407 568608546135112760537111)
              ·
                refine ⟨852912819202669140805667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568608546135112760537111 852912819202669140805667)
                ·
                  refine ⟨1279369228804003711208501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852912819202669140805667 1279369228804003711208501)
                  ·
                    refine ⟨119940865200375347925797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1279369228804003711208501 119940865200375347925797)
                    ·
                      refine ⟨22488912225070377736087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 119940865200375347925797 22488912225070377736087)
                      ·
                        rfl

theorem cell23_43797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_43797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43797 prefixEnd_43797 := by exact prefixLift 43797
  have htrace : WordTrace (prefixWord ++ tailWord_43797) baseStart_43797 baseEnd_43797 := by
    simpa [prefixWord, tailWord_43797, baseEnd_43797] using wordTrace_append hprefix tailTrace_43797
  have hstable : (prefixWord ++ tailWord_43797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43797).length < 2 ^ (prefixWord ++ tailWord_43797).sum := by decide
  have hdescent : baseEnd_43797 < baseStart_43797 := by decide
  rcases family_descends (prefixWord ++ tailWord_43797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43807 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 1, 8]
def baseStart_43807 : Nat := 118140960795 + 43807 * 2 ^ 59
def prefixEnd_43807 : Nat := 4983230072969 + 3 ^ 40 * 43807 * 2
def baseEnd_43807 : Nat := 7498015677205112870347

theorem tailTrace_43807 : CollatzResearch.WordTrace tailWord_43807 prefixEnd_43807 7498015677205112870347 := by
  unfold tailWord_43807
  simp only [CollatzResearch.WordTrace]
  refine ⟨1597772552302195485065675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1065181701534796990043783 1597772552302195485065675)
  ·
    refine ⟨2396658828453293227598513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1597772552302195485065675 2396658828453293227598513)
    ·
      refine ⟨1797494121339969920698885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2396658828453293227598513 1797494121339969920698885)
      ·
        refine ⟨337030147751244360131041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1797494121339969920698885 337030147751244360131041)
        ·
          refine ⟨252772610813433270098281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337030147751244360131041 252772610813433270098281)
          ·
            refine ⟨189579458110074952573711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252772610813433270098281 189579458110074952573711)
            ·
              refine ⟨284369187165112428860567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189579458110074952573711 284369187165112428860567)
              ·
                refine ⟨426553780747668643290851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284369187165112428860567 426553780747668643290851)
                ·
                  refine ⟨639830671121502964936277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426553780747668643290851 639830671121502964936277)
                  ·
                    refine ⟨7498015677205112870347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 639830671121502964936277 7498015677205112870347)
                    ·
                      rfl

theorem cell23_43807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_43807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43807 prefixEnd_43807 := by exact prefixLift 43807
  have htrace : WordTrace (prefixWord ++ tailWord_43807) baseStart_43807 baseEnd_43807 := by
    simpa [prefixWord, tailWord_43807, baseEnd_43807] using wordTrace_append hprefix tailTrace_43807
  have hstable : (prefixWord ++ tailWord_43807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43807).length < 2 ^ (prefixWord ++ tailWord_43807).sum := by decide
  have hdescent : baseEnd_43807 < baseStart_43807 := by decide
  rcases family_descends (prefixWord ++ tailWord_43807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43831 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 4, 2, 2]
def baseStart_43831 : Nat := 118140960795 + 43831 * 2 ^ 59
def prefixEnd_43831 : Nat := 4983230072969 + 3 ^ 40 * 43831 * 2
def baseEnd_43831 : Nat := 22506370567323244710931

theorem tailTrace_43831 : CollatzResearch.WordTrace tailWord_43831 prefixEnd_43831 22506370567323244710931 := by
  unfold tailWord_43831
  simp only [CollatzResearch.WordTrace]
  refine ⟨1598647904215247583939347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1065765269476831722626231 1598647904215247583939347)
  ·
    refine ⟨2397971856322871375909021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1598647904215247583939347 2397971856322871375909021)
    ·
      refine ⟨899239446121076765965883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2397971856322871375909021 899239446121076765965883)
      ·
        refine ⟨1348859169181615148948825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899239446121076765965883 1348859169181615148948825)
        ·
          refine ⟨1011644376886211361711619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1348859169181615148948825 1011644376886211361711619)
          ·
            refine ⟨1517466565329317042567429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011644376886211361711619 1517466565329317042567429)
            ·
              refine ⟨284524980999246945481393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1517466565329317042567429 284524980999246945481393)
              ·
                refine ⟨213393735749435209111045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284524980999246945481393 213393735749435209111045)
                ·
                  refine ⟨40011325453019101708321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213393735749435209111045 40011325453019101708321)
                  ·
                    refine ⟨30008494089764326281241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40011325453019101708321 30008494089764326281241)
                    ·
                      refine ⟨22506370567323244710931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 30008494089764326281241 22506370567323244710931)
                      ·
                        rfl

theorem cell23_43831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_43831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43831 prefixEnd_43831 := by exact prefixLift 43831
  have htrace : WordTrace (prefixWord ++ tailWord_43831) baseStart_43831 baseEnd_43831 := by
    simpa [prefixWord, tailWord_43831, baseEnd_43831] using wordTrace_append hprefix tailTrace_43831
  have hstable : (prefixWord ++ tailWord_43831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43831).length < 2 ^ (prefixWord ++ tailWord_43831).sum := by decide
  have hdescent : baseEnd_43831 < baseStart_43831 := by decide
  rcases family_descends (prefixWord ++ tailWord_43831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43865 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 2, 2, 2]
def baseStart_43865 : Nat := 118140960795 + 43865 * 2 ^ 59
def prefixEnd_43865 : Nat := 4983230072969 + 3 ^ 40 * 43865 * 2
def baseEnd_43865 : Nat := 22523828909576111685775

theorem tailTrace_43865 : CollatzResearch.WordTrace tailWord_43865 prefixEnd_43865 22523828909576111685775 := by
  unfold tailWord_43865
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599887986092071390677049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1066591990728047593784699 1599887986092071390677049)
  ·
    refine ⟨1199915989569053543007787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1599887986092071390677049 1199915989569053543007787)
    ·
      refine ⟨1799873984353580314511681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1199915989569053543007787 1799873984353580314511681)
      ·
        refine ⟨1349905488265185235883761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1799873984353580314511681 1349905488265185235883761)
        ·
          refine ⟨1012429116198888926912821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1349905488265185235883761 1012429116198888926912821)
          ·
            refine ⟨94915229643645836898077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1012429116198888926912821 94915229643645836898077)
            ·
              refine ⟨35593211116367188836779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94915229643645836898077 35593211116367188836779)
              ·
                refine ⟨53389816674550783255169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35593211116367188836779 53389816674550783255169)
                ·
                  refine ⟨40042362505913087441377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53389816674550783255169 40042362505913087441377)
                  ·
                    refine ⟨30031771879434815581033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40042362505913087441377 30031771879434815581033)
                    ·
                      refine ⟨22523828909576111685775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 30031771879434815581033 22523828909576111685775)
                      ·
                        rfl

theorem cell23_43865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_43865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43865 prefixEnd_43865 := by exact prefixLift 43865
  have htrace : WordTrace (prefixWord ++ tailWord_43865) baseStart_43865 baseEnd_43865 := by
    simpa [prefixWord, tailWord_43865, baseEnd_43865] using wordTrace_append hprefix tailTrace_43865
  have hstable : (prefixWord ++ tailWord_43865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43865).length < 2 ^ (prefixWord ++ tailWord_43865).sum := by decide
  have hdescent : baseEnd_43865 < baseStart_43865 := by decide
  rcases family_descends (prefixWord ++ tailWord_43865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43884 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_43884 : Nat := 118140960795 + 43884 * 2 ^ 59
def prefixEnd_43884 : Nat := 4983230072969 + 3 ^ 40 * 43884 * 2
def baseEnd_43884 : Nat := 7511195014003845782729

theorem tailTrace_43884 : CollatzResearch.WordTrace tailWord_43884 prefixEnd_43884 7511195014003845782729 := by
  unfold tailWord_43884
  simp only [CollatzResearch.WordTrace]
  refine ⟨800290486511618817809353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1067053982015491757079137 800290486511618817809353)
  ·
    refine ⟨600217864883714113357015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 800290486511618817809353 600217864883714113357015)
    ·
      refine ⟨900326797325571170035523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600217864883714113357015 900326797325571170035523)
      ·
        refine ⟨1350490195988356755053285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900326797325571170035523 1350490195988356755053285)
        ·
          refine ⟨253216911747816891572491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1350490195988356755053285 253216911747816891572491)
          ·
            refine ⟨379825367621725337358737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253216911747816891572491 379825367621725337358737)
            ·
              refine ⟨284869025716294003019053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379825367621725337358737 284869025716294003019053)
              ·
                refine ⟨106825884643610251132145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284869025716294003019053 106825884643610251132145)
                ·
                  refine ⟨80119413482707688349109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106825884643610251132145 80119413482707688349109)
                  ·
                    refine ⟨7511195014003845782729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80119413482707688349109 7511195014003845782729)
                    ·
                      rfl

theorem cell23_43884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_43884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43884 prefixEnd_43884 := by exact prefixLift 43884
  have htrace : WordTrace (prefixWord ++ tailWord_43884) baseStart_43884 baseEnd_43884 := by
    simpa [prefixWord, tailWord_43884, baseEnd_43884] using wordTrace_append hprefix tailTrace_43884
  have hstable : (prefixWord ++ tailWord_43884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43884).length < 2 ^ (prefixWord ++ tailWord_43884).sum := by decide
  have hdescent : baseEnd_43884 < baseStart_43884 := by decide
  rcases family_descends (prefixWord ++ tailWord_43884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43938 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_43938 : Nat := 118140960795 + 43938 * 2 ^ 59
def prefixEnd_43938 : Nat := 4983230072969 + 3 ^ 40 * 43938 * 2
def baseEnd_43938 : Nat := 22561312997354326072939

theorem tailTrace_43938 : CollatzResearch.WordTrace tailWord_43938 prefixEnd_43938 22561312997354326072939 := by
  unfold tailWord_43938
  simp only [CollatzResearch.WordTrace]
  refine ⟨400637628706901214521117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1068367009885069905389645 400637628706901214521117)
  ·
    refine ⟨150239110765087955445419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 400637628706901214521117 150239110765087955445419)
    ·
      refine ⟨225358666147631933168129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150239110765087955445419 225358666147631933168129)
      ·
        refine ⟨169018999610723949876097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225358666147631933168129 169018999610723949876097)
        ·
          refine ⟨126764249708042962407073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169018999610723949876097 126764249708042962407073)
          ·
            refine ⟨95073187281032221805305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126764249708042962407073 95073187281032221805305)
            ·
              refine ⟨71304890460774166353979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95073187281032221805305 71304890460774166353979)
              ·
                refine ⟨106957335691161249530969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71304890460774166353979 106957335691161249530969)
                ·
                  refine ⟨80218001768370937148227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106957335691161249530969 80218001768370937148227)
                  ·
                    refine ⟨120327002652556405722341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80218001768370937148227 120327002652556405722341)
                    ·
                      refine ⟨22561312997354326072939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 120327002652556405722341 22561312997354326072939)
                      ·
                        rfl

theorem cell23_43938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_43938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43938 prefixEnd_43938 := by exact prefixLift 43938
  have htrace : WordTrace (prefixWord ++ tailWord_43938) baseStart_43938 baseEnd_43938 := by
    simpa [prefixWord, tailWord_43938, baseEnd_43938] using wordTrace_append hprefix tailTrace_43938
  have hstable : (prefixWord ++ tailWord_43938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43938).length < 2 ^ (prefixWord ++ tailWord_43938).sum := by decide
  have hdescent : baseEnd_43938 < baseStart_43938 := by decide
  rcases family_descends (prefixWord ++ tailWord_43938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43961 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 6]
def baseStart_43961 : Nat := 118140960795 + 43961 * 2 ^ 59
def prefixEnd_43961 : Nat := 4983230072969 + 3 ^ 40 * 43961 * 2
def baseEnd_43961 : Nat := 2508124783600859565037

theorem tailTrace_43961 : CollatzResearch.WordTrace tailWord_43961 prefixEnd_43961 2508124783600859565037 := by
  unfold tailWord_43961
  simp only [CollatzResearch.WordTrace]
  refine ⟨1603389393744279786171737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1068926262496186524114491 1603389393744279786171737)
  ·
    refine ⟨1202542045308209839628803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1603389393744279786171737 1202542045308209839628803)
    ·
      refine ⟨1803813067962314759443205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1202542045308209839628803 1803813067962314759443205)
      ·
        refine ⟨338214950242934017395601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1803813067962314759443205 338214950242934017395601)
        ·
          refine ⟨253661212682200513046701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338214950242934017395601 253661212682200513046701)
          ·
            refine ⟨95122954755825192392513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253661212682200513046701 95122954755825192392513)
            ·
              refine ⟨71342216066868894294385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95122954755825192392513 71342216066868894294385)
              ·
                refine ⟨53506662050151670720789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71342216066868894294385 53506662050151670720789)
                ·
                  refine ⟨2508124783600859565037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53506662050151670720789 2508124783600859565037)
                  ·
                    rfl

theorem cell23_43961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 6].length) (baseStart_43961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43961 prefixEnd_43961 := by exact prefixLift 43961
  have htrace : WordTrace (prefixWord ++ tailWord_43961) baseStart_43961 baseEnd_43961 := by
    simpa [prefixWord, tailWord_43961, baseEnd_43961] using wordTrace_append hprefix tailTrace_43961
  have hstable : (prefixWord ++ tailWord_43961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43961).length < 2 ^ (prefixWord ++ tailWord_43961).sum := by decide
  have hdescent : baseEnd_43961 < baseStart_43961 := by decide
  rcases family_descends (prefixWord ++ tailWord_43961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43965 : List Nat := [1, 4, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_43965 : Nat := 118140960795 + 43965 * 2 ^ 59
def prefixEnd_43965 : Nat := 4983230072969 + 3 ^ 40 * 43965 * 2
def baseEnd_43965 : Nat := 7525058991675240145105

theorem tailTrace_43965 : CollatzResearch.WordTrace tailWord_43965 prefixEnd_43965 7525058991675240145105 := by
  unfold tailWord_43965
  simp only [CollatzResearch.WordTrace]
  refine ⟨1603535285729788469317349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1069023523819858979544899 1603535285729788469317349)
  ·
    refine ⟨300662866074335337997003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1603535285729788469317349 300662866074335337997003)
    ·
      refine ⟨450994299111503006995505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300662866074335337997003 450994299111503006995505)
      ·
        refine ⟨338245724333627255246629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450994299111503006995505 338245724333627255246629)
        ·
          refine ⟨63421073312555110358743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 338245724333627255246629 63421073312555110358743)
          ·
            refine ⟨95131609968832665538115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63421073312555110358743 95131609968832665538115)
            ·
              refine ⟨142697414953248998307173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95131609968832665538115 142697414953248998307173)
              ·
                refine ⟨26755765303734187182595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142697414953248998307173 26755765303734187182595)
                ·
                  refine ⟨40133647955601280773893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26755765303734187182595 40133647955601280773893)
                  ·
                    refine ⟨7525058991675240145105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40133647955601280773893 7525058991675240145105)
                    ·
                      rfl

theorem cell23_43965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_43965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43965 prefixEnd_43965 := by exact prefixLift 43965
  have htrace : WordTrace (prefixWord ++ tailWord_43965) baseStart_43965 baseEnd_43965 := by
    simpa [prefixWord, tailWord_43965, baseEnd_43965] using wordTrace_append hprefix tailTrace_43965
  have hstable : (prefixWord ++ tailWord_43965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43965).length < 2 ^ (prefixWord ++ tailWord_43965).sum := by decide
  have hdescent : baseEnd_43965 < baseStart_43965 := by decide
  rcases family_descends (prefixWord ++ tailWord_43965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43988 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_43988 : Nat := 118140960795 + 43988 * 2 ^ 59
def prefixEnd_43988 : Nat := 4983230072969 + 3 ^ 40 * 43988 * 2
def baseEnd_43988 : Nat := 22586987030079130447709

theorem tailTrace_43988 : CollatzResearch.WordTrace tailWord_43988 prefixEnd_43988 22586987030079130447709 := by
  unfold tailWord_43988
  simp only [CollatzResearch.WordTrace]
  refine ⟨802187082323231698702309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1069582776430975598269745 802187082323231698702309)
  ·
    refine ⟨150410077935605943506683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 802187082323231698702309 150410077935605943506683)
    ·
      refine ⟨225615116903408915260025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150410077935605943506683 225615116903408915260025)
      ·
        refine ⟨169211337677556686445019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225615116903408915260025 169211337677556686445019)
        ·
          refine ⟨253817006516335029667529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169211337677556686445019 253817006516335029667529)
          ·
            refine ⟨190362754887251272250647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253817006516335029667529 190362754887251272250647)
            ·
              refine ⟨285544132330876908375971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190362754887251272250647 285544132330876908375971)
              ·
                refine ⟨428316198496315362563957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285544132330876908375971 428316198496315362563957)
                ·
                  refine ⟨40154643609029565240371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428316198496315362563957 40154643609029565240371)
                  ·
                    refine ⟨60231965413544347860557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40154643609029565240371 60231965413544347860557)
                    ·
                      refine ⟨22586987030079130447709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 60231965413544347860557 22586987030079130447709)
                      ·
                        rfl

theorem cell23_43988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_43988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_43988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_43988 prefixEnd_43988 := by exact prefixLift 43988
  have htrace : WordTrace (prefixWord ++ tailWord_43988) baseStart_43988 baseEnd_43988 := by
    simpa [prefixWord, tailWord_43988, baseEnd_43988] using wordTrace_append hprefix tailTrace_43988
  have hstable : (prefixWord ++ tailWord_43988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43988).length < 2 ^ (prefixWord ++ tailWord_43988).sum := by decide
  have hdescent : baseEnd_43988 < baseStart_43988 := by decide
  rcases family_descends (prefixWord ++ tailWord_43988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44004 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_44004 : Nat := 118140960795 + 44004 * 2 ^ 59
def prefixEnd_44004 : Nat := 4983230072969 + 3 ^ 40 * 44004 * 2
def baseEnd_44004 : Nat := 7531734240183689282545

theorem tailTrace_44004 : CollatzResearch.WordTrace tailWord_44004 prefixEnd_44004 7531734240183689282545 := by
  unfold tailWord_44004
  simp only [CollatzResearch.WordTrace]
  refine ⟨802478866294249064993533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1069971821725665419991377 802478866294249064993533)
  ·
    refine ⟨300929574860343399372575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 802478866294249064993533 300929574860343399372575)
    ·
      refine ⟨451394362290515099058863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300929574860343399372575 451394362290515099058863)
      ·
        refine ⟨677091543435772648588295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451394362290515099058863 677091543435772648588295)
        ·
          refine ⟨1015637315153658972882443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677091543435772648588295 1015637315153658972882443)
          ·
            refine ⟨1523455972730488459323665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015637315153658972882443 1523455972730488459323665)
            ·
              refine ⟨1142591979547866344492749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523455972730488459323665 1142591979547866344492749)
              ·
                refine ⟨428471992330449879184781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1142591979547866344492749 428471992330449879184781)
                ·
                  refine ⟨160676997123918704694293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428471992330449879184781 160676997123918704694293)
                  ·
                    refine ⟨7531734240183689282545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 160676997123918704694293 7531734240183689282545)
                    ·
                      rfl

theorem cell23_44004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_44004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44004 prefixEnd_44004 := by exact prefixLift 44004
  have htrace : WordTrace (prefixWord ++ tailWord_44004) baseStart_44004 baseEnd_44004 := by
    simpa [prefixWord, tailWord_44004, baseEnd_44004] using wordTrace_append hprefix tailTrace_44004
  have hstable : (prefixWord ++ tailWord_44004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44004).length < 2 ^ (prefixWord ++ tailWord_44004).sum := by decide
  have hdescent : baseEnd_44004 < baseStart_44004 := by decide
  rcases family_descends (prefixWord ++ tailWord_44004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44008 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 1, 5]
def baseStart_44008 : Nat := 118140960795 + 44008 * 2 ^ 59
def prefixEnd_44008 : Nat := 4983230072969 + 3 ^ 40 * 44008 * 2
def baseEnd_44008 : Nat := 7532418881056350732539

theorem tailTrace_44008 : CollatzResearch.WordTrace tailWord_44008 prefixEnd_44008 7532418881056350732539 := by
  unfold tailWord_44008
  simp only [CollatzResearch.WordTrace]
  refine ⟨802551812287003406566339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1070069083049337875421785 802551812287003406566339)
  ·
    refine ⟨1203827718430505109849509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 802551812287003406566339 1203827718430505109849509)
    ·
      refine ⟨225717697205719708096783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1203827718430505109849509 225717697205719708096783)
      ·
        refine ⟨338576545808579562145175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225717697205719708096783 338576545808579562145175)
        ·
          refine ⟨507864818712869343217763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338576545808579562145175 507864818712869343217763)
          ·
            refine ⟨761797228069304014826645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507864818712869343217763 761797228069304014826645)
            ·
              refine ⟨35709245065748625694999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 761797228069304014826645 35709245065748625694999)
              ·
                refine ⟨53563867598622938542499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35709245065748625694999 53563867598622938542499)
                ·
                  refine ⟨80345801397934407813749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53563867598622938542499 80345801397934407813749)
                  ·
                    refine ⟨7532418881056350732539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80345801397934407813749 7532418881056350732539)
                    ·
                      rfl

theorem cell23_44008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_44008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44008 prefixEnd_44008 := by exact prefixLift 44008
  have htrace : WordTrace (prefixWord ++ tailWord_44008) baseStart_44008 baseEnd_44008 := by
    simpa [prefixWord, tailWord_44008, baseEnd_44008] using wordTrace_append hprefix tailTrace_44008
  have hstable : (prefixWord ++ tailWord_44008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44008).length < 2 ^ (prefixWord ++ tailWord_44008).sum := by decide
  have hdescent : baseEnd_44008 < baseStart_44008 := by decide
  rcases family_descends (prefixWord ++ tailWord_44008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44022 : List Nat := [5, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_44022 : Nat := 118140960795 + 44022 * 2 ^ 59
def prefixEnd_44022 : Nat := 4983230072969 + 3 ^ 40 * 44022 * 2
def baseEnd_44022 : Nat := 22604445372331997422553

theorem tailTrace_44022 : CollatzResearch.WordTrace tailWord_44022 prefixEnd_44022 22604445372331997422553 := by
  unfold tailWord_44022
  simp only [CollatzResearch.WordTrace]
  refine ⟨100350890407705450258895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1070409497682191469428213 100350890407705450258895)
  ·
    refine ⟨150526335611558175388343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100350890407705450258895 150526335611558175388343)
    ·
      refine ⟨225789503417337263082515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150526335611558175388343 225789503417337263082515)
      ·
        refine ⟨338684255126005894623773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225789503417337263082515 338684255126005894623773)
        ·
          refine ⟨127006595672252210483915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338684255126005894623773 127006595672252210483915)
          ·
            refine ⟨190509893508378315725873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127006595672252210483915 190509893508378315725873)
            ·
              refine ⟨142882420131283736794405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190509893508378315725873 142882420131283736794405)
              ·
                refine ⟨26790453774615700648951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142882420131283736794405 26790453774615700648951)
                ·
                  refine ⟨40185680661923550973427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26790453774615700648951 40185680661923550973427)
                  ·
                    refine ⟨60278520992885326460141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40185680661923550973427 60278520992885326460141)
                    ·
                      refine ⟨22604445372331997422553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 60278520992885326460141 22604445372331997422553)
                      ·
                        rfl

theorem cell23_44022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_44022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44022 prefixEnd_44022 := by exact prefixLift 44022
  have htrace : WordTrace (prefixWord ++ tailWord_44022) baseStart_44022 baseEnd_44022 := by
    simpa [prefixWord, tailWord_44022, baseEnd_44022] using wordTrace_append hprefix tailTrace_44022
  have hstable : (prefixWord ++ tailWord_44022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44022).length < 2 ^ (prefixWord ++ tailWord_44022).sum := by decide
  have hdescent : baseEnd_44022 < baseStart_44022 := by decide
  rcases family_descends (prefixWord ++ tailWord_44022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44024 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_44024 : Nat := 118140960795 + 44024 * 2 ^ 59
def prefixEnd_44024 : Nat := 4983230072969 + 3 ^ 40 * 44024 * 2
def baseEnd_44024 : Nat := 22605472333640989597543

theorem tailTrace_44024 : CollatzResearch.WordTrace tailWord_44024 prefixEnd_44024 22605472333640989597543 := by
  unfold tailWord_44024
  simp only [CollatzResearch.WordTrace]
  refine ⟨802843596258020772857563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1070458128344027697143417 802843596258020772857563)
  ·
    refine ⟨1204265394387031159286345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 802843596258020772857563 1204265394387031159286345)
    ·
      refine ⟨903199045790273369464759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1204265394387031159286345 903199045790273369464759)
      ·
        refine ⟨1354798568685410054197139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903199045790273369464759 1354798568685410054197139)
        ·
          refine ⟨2032197853028115081295709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354798568685410054197139 2032197853028115081295709)
          ·
            refine ⟨762074194885543155485891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2032197853028115081295709 762074194885543155485891)
            ·
              refine ⟨1143111292328314733228837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762074194885543155485891 1143111292328314733228837)
              ·
                refine ⟨214333367311559012480407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1143111292328314733228837 214333367311559012480407)
                ·
                  refine ⟨321500050967338518720611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214333367311559012480407 321500050967338518720611)
                  ·
                    refine ⟨482250076451007778080917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 321500050967338518720611 482250076451007778080917)
                    ·
                      refine ⟨22605472333640989597543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 482250076451007778080917 22605472333640989597543)
                      ·
                        rfl

theorem cell23_44024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_44024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44024 prefixEnd_44024 := by exact prefixLift 44024
  have htrace : WordTrace (prefixWord ++ tailWord_44024) baseStart_44024 baseEnd_44024 := by
    simpa [prefixWord, tailWord_44024, baseEnd_44024] using wordTrace_append hprefix tailTrace_44024
  have hstable : (prefixWord ++ tailWord_44024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44024).length < 2 ^ (prefixWord ++ tailWord_44024).sum := by decide
  have hdescent : baseEnd_44024 < baseStart_44024 := by decide
  rcases family_descends (prefixWord ++ tailWord_44024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44131 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 4]
def baseStart_44131 : Nat := 118140960795 + 44131 * 2 ^ 59
def prefixEnd_44131 : Nat := 4983230072969 + 3 ^ 40 * 44131 * 2
def baseEnd_44131 : Nat := 22660414763672070959551

theorem tailTrace_44131 : CollatzResearch.WordTrace tailWord_44131 prefixEnd_44131 22660414763672070959551 := by
  unfold tailWord_44131
  simp only [CollatzResearch.WordTrace]
  refine ⟨1609589803128398819860247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1073059868752265879906831 1609589803128398819860247)
  ·
    refine ⟨2414384704692598229790371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1609589803128398819860247 2414384704692598229790371)
    ·
      refine ⟨3621577057038897344685557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414384704692598229790371 3621577057038897344685557)
      ·
        refine ⟨339522849097396626064271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3621577057038897344685557 339522849097396626064271)
        ·
          refine ⟨509284273646094939096407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339522849097396626064271 509284273646094939096407)
          ·
            refine ⟨763926410469142408644611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509284273646094939096407 763926410469142408644611)
            ·
              refine ⟨1145889615703713612966917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763926410469142408644611 1145889615703713612966917)
              ·
                refine ⟨214854302944446302431297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1145889615703713612966917 214854302944446302431297)
                ·
                  refine ⟨161140727208334726823473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214854302944446302431297 161140727208334726823473)
                  ·
                    refine ⟨120855545406251045117605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161140727208334726823473 120855545406251045117605)
                    ·
                      refine ⟨22660414763672070959551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 120855545406251045117605 22660414763672070959551)
                      ·
                        rfl

theorem cell23_44131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_44131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44131 prefixEnd_44131 := by exact prefixLift 44131
  have htrace : WordTrace (prefixWord ++ tailWord_44131) baseStart_44131 baseEnd_44131 := by
    simpa [prefixWord, tailWord_44131, baseEnd_44131] using wordTrace_append hprefix tailTrace_44131
  have hstable : (prefixWord ++ tailWord_44131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44131).length < 2 ^ (prefixWord ++ tailWord_44131).sum := by decide
  have hdescent : baseEnd_44131 < baseStart_44131 := by decide
  rcases family_descends (prefixWord ++ tailWord_44131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44138 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_44138 : Nat := 118140960795 + 44138 * 2 ^ 59
def prefixEnd_44138 : Nat := 4983230072969 + 3 ^ 40 * 44138 * 2
def baseEnd_44138 : Nat := 22664009128253543572019

theorem tailTrace_44138 : CollatzResearch.WordTrace tailWord_44138 prefixEnd_44138 22664009128253543572019 := by
  unfold tailWord_44138
  simp only [CollatzResearch.WordTrace]
  refine ⟨402461278525759753841267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1073230076068692676910045 402461278525759753841267)
  ·
    refine ⟨603691917788639630761901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 402461278525759753841267 603691917788639630761901)
    ·
      refine ⟨226384469170739861535713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 603691917788639630761901 226384469170739861535713)
      ·
        refine ⟨169788351878054896151785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226384469170739861535713 169788351878054896151785)
        ·
          refine ⟨127341263908541172113839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169788351878054896151785 127341263908541172113839)
          ·
            refine ⟨191011895862811758170759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127341263908541172113839 191011895862811758170759)
            ·
              refine ⟨286517843794217637256139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191011895862811758170759 286517843794217637256139)
              ·
                refine ⟨429776765691326455884209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286517843794217637256139 429776765691326455884209)
                ·
                  refine ⟨322332574268494841913157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429776765691326455884209 322332574268494841913157)
                  ·
                    refine ⟨60437357675342782858717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322332574268494841913157 60437357675342782858717)
                    ·
                      refine ⟨22664009128253543572019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 60437357675342782858717 22664009128253543572019)
                      ·
                        rfl

theorem cell23_44138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_44138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44138 prefixEnd_44138 := by exact prefixLift 44138
  have htrace : WordTrace (prefixWord ++ tailWord_44138) baseStart_44138 baseEnd_44138 := by
    simpa [prefixWord, tailWord_44138, baseEnd_44138] using wordTrace_append hprefix tailTrace_44138
  have hstable : (prefixWord ++ tailWord_44138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44138).length < 2 ^ (prefixWord ++ tailWord_44138).sum := by decide
  have hdescent : baseEnd_44138 < baseStart_44138 := by decide
  rcases family_descends (prefixWord ++ tailWord_44138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44181 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_44181 : Nat := 118140960795 + 44181 * 2 ^ 59
def prefixEnd_44181 : Nat := 4983230072969 + 3 ^ 40 * 44181 * 2
def baseEnd_44181 : Nat := 22686088796396875334321

theorem tailTrace_44181 : CollatzResearch.WordTrace tailWord_44181 prefixEnd_44181 22686088796396875334321 := by
  unfold tailWord_44181
  simp only [CollatzResearch.WordTrace]
  refine ⟨1611413452947257359180397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1074275635298171572786931 1611413452947257359180397)
  ·
    refine ⟨604280044855221509692649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1611413452947257359180397 604280044855221509692649)
    ·
      refine ⟨453210033641416132269487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 604280044855221509692649 453210033641416132269487)
      ·
        refine ⟨679815050462124198404231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453210033641416132269487 679815050462124198404231)
        ·
          refine ⟨1019722575693186297606347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679815050462124198404231 1019722575693186297606347)
          ·
            refine ⟨1529583863539779446409521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019722575693186297606347 1529583863539779446409521)
            ·
              refine ⟨1147187897654834584807141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529583863539779446409521 1147187897654834584807141)
              ·
                refine ⟨215097730810281484651339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1147187897654834584807141 215097730810281484651339)
                ·
                  refine ⟨322646596215422226977009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215097730810281484651339 322646596215422226977009)
                  ·
                    refine ⟨241984947161566670232757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322646596215422226977009 241984947161566670232757)
                    ·
                      refine ⟨22686088796396875334321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 241984947161566670232757 22686088796396875334321)
                      ·
                        rfl

theorem cell23_44181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_44181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44181 prefixEnd_44181 := by exact prefixLift 44181
  have htrace : WordTrace (prefixWord ++ tailWord_44181) baseStart_44181 baseEnd_44181 := by
    simpa [prefixWord, tailWord_44181, baseEnd_44181] using wordTrace_append hprefix tailTrace_44181
  have hstable : (prefixWord ++ tailWord_44181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44181).length < 2 ^ (prefixWord ++ tailWord_44181).sum := by decide
  have hdescent : baseEnd_44181 < baseStart_44181 := by decide
  rcases family_descends (prefixWord ++ tailWord_44181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44225 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_44225 : Nat := 118140960795 + 44225 * 2 ^ 59
def prefixEnd_44225 : Nat := 4983230072969 + 3 ^ 40 * 44225 * 2
def baseEnd_44225 : Nat := 22708681945194703184119

theorem tailTrace_44225 : CollatzResearch.WordTrace tailWord_44225 prefixEnd_44225 22708681945194703184119 := by
  unfold tailWord_44225
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613018264787852873782129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1075345509858568582521419 1613018264787852873782129)
  ·
    refine ⟨1209763698590889655336597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1613018264787852873782129 1209763698590889655336597)
    ·
      refine ⟨56707673371447952593903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1209763698590889655336597 56707673371447952593903)
      ·
        refine ⟨85061510057171928890855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56707673371447952593903 85061510057171928890855)
        ·
          refine ⟨127592265085757893336283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85061510057171928890855 127592265085757893336283)
          ·
            refine ⟨191388397628636840004425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127592265085757893336283 191388397628636840004425)
            ·
              refine ⟨143541298221477630003319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191388397628636840004425 143541298221477630003319)
              ·
                refine ⟨215311947332216445004979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143541298221477630003319 215311947332216445004979)
                ·
                  refine ⟨322967920998324667507469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215311947332216445004979 322967920998324667507469)
                  ·
                    refine ⟨121112970374371750315301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322967920998324667507469 121112970374371750315301)
                    ·
                      refine ⟨22708681945194703184119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 121112970374371750315301 22708681945194703184119)
                      ·
                        rfl

theorem cell23_44225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_44225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44225 prefixEnd_44225 := by exact prefixLift 44225
  have htrace : WordTrace (prefixWord ++ tailWord_44225) baseStart_44225 baseEnd_44225 := by
    simpa [prefixWord, tailWord_44225, baseEnd_44225] using wordTrace_append hprefix tailTrace_44225
  have hstable : (prefixWord ++ tailWord_44225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44225).length < 2 ^ (prefixWord ++ tailWord_44225).sum := by decide
  have hdescent : baseEnd_44225 < baseStart_44225 := by decide
  rcases family_descends (prefixWord ++ tailWord_44225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44226 : List Nat := [3, 5, 1, 1, 2, 2, 1, 3, 5]
def baseStart_44226 : Nat := 118140960795 + 44226 * 2 ^ 59
def prefixEnd_44226 : Nat := 4983230072969 + 3 ^ 40 * 44226 * 2
def baseEnd_44226 : Nat := 2523243936205466585735

theorem tailTrace_44226 : CollatzResearch.WordTrace tailWord_44226 prefixEnd_44226 2523243936205466585735 := by
  unfold tailWord_44226
  simp only [CollatzResearch.WordTrace]
  refine ⟨403263684446057511142133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1075369825189486696379021 403263684446057511142133)
  ·
    refine ⟨37805970416817891669575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 403263684446057511142133 37805970416817891669575)
    ·
      refine ⟨56708955625226837504363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37805970416817891669575 56708955625226837504363)
      ·
        refine ⟨85063433437840256256545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56708955625226837504363 85063433437840256256545)
        ·
          refine ⟨63797575078380192192409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85063433437840256256545 63797575078380192192409)
          ·
            refine ⟨47848181308785144144307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63797575078380192192409 47848181308785144144307)
            ·
              refine ⟨71772271963177716216461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47848181308785144144307 71772271963177716216461)
              ·
                refine ⟨26914601986191643581173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71772271963177716216461 26914601986191643581173)
                ·
                  refine ⟨2523243936205466585735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26914601986191643581173 2523243936205466585735)
                  ·
                    rfl

theorem cell23_44226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_44226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44226 prefixEnd_44226 := by exact prefixLift 44226
  have htrace : WordTrace (prefixWord ++ tailWord_44226) baseStart_44226 baseEnd_44226 := by
    simpa [prefixWord, tailWord_44226, baseEnd_44226] using wordTrace_append hprefix tailTrace_44226
  have hstable : (prefixWord ++ tailWord_44226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44226).length < 2 ^ (prefixWord ++ tailWord_44226).sum := by decide
  have hdescent : baseEnd_44226 < baseStart_44226 := by decide
  rcases family_descends (prefixWord ++ tailWord_44226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44235 : List Nat := [1, 1, 1, 1, 3, 2, 2, 7, 1, 4]
def baseStart_44235 : Nat := 118140960795 + 44235 * 2 ^ 59
def prefixEnd_44235 : Nat := 4983230072969 + 3 ^ 40 * 44235 * 2
def baseEnd_44235 : Nat := 7571272250579888019691

theorem tailTrace_44235 : CollatzResearch.WordTrace tailWord_44235 prefixEnd_44235 7571272250579888019691 := by
  unfold tailWord_44235
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613382994751624581646159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1075588663167749721097439 1613382994751624581646159)
  ·
    refine ⟨2420074492127436872469239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1613382994751624581646159 2420074492127436872469239)
    ·
      refine ⟨3630111738191155308703859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2420074492127436872469239 3630111738191155308703859)
      ·
        refine ⟨5445167607286732963055789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630111738191155308703859 5445167607286732963055789)
        ·
          refine ⟨2041937852732524861145921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5445167607286732963055789 2041937852732524861145921)
          ·
            refine ⟨1531453389549393645859441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041937852732524861145921 1531453389549393645859441)
            ·
              refine ⟨1148590042162045234394581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531453389549393645859441 1148590042162045234394581)
              ·
                refine ⟨26920079113172935181123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1148590042162045234394581 26920079113172935181123)
                ·
                  refine ⟨40380118669759402771685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26920079113172935181123 40380118669759402771685)
                  ·
                    refine ⟨7571272250579888019691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40380118669759402771685 7571272250579888019691)
                    ·
                      rfl

theorem cell23_44235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 1, 4].length) (baseStart_44235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44235 prefixEnd_44235 := by exact prefixLift 44235
  have htrace : WordTrace (prefixWord ++ tailWord_44235) baseStart_44235 baseEnd_44235 := by
    simpa [prefixWord, tailWord_44235, baseEnd_44235] using wordTrace_append hprefix tailTrace_44235
  have hstable : (prefixWord ++ tailWord_44235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44235).length < 2 ^ (prefixWord ++ tailWord_44235).sum := by decide
  have hdescent : baseEnd_44235 < baseStart_44235 := by decide
  rcases family_descends (prefixWord ++ tailWord_44235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44245 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_44245 : Nat := 118140960795 + 44245 * 2 ^ 59
def prefixEnd_44245 : Nat := 4983230072969 + 3 ^ 40 * 44245 * 2
def baseEnd_44245 : Nat := 22718951558284624934027

theorem tailTrace_44245 : CollatzResearch.WordTrace tailWord_44245 prefixEnd_44245 22718951558284624934027 := by
  unfold tailWord_44245
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613747724715396289510189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1075831816476930859673459 1613747724715396289510189)
  ·
    refine ⟨605155396768273608566321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1613747724715396289510189 605155396768273608566321)
    ·
      refine ⟨453866547576205206424741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 605155396768273608566321 453866547576205206424741)
      ·
        refine ⟨85099977670538476204639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 453866547576205206424741 85099977670538476204639)
        ·
          refine ⟨127649966505807714306959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85099977670538476204639 127649966505807714306959)
          ·
            refine ⟨191474949758711571460439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127649966505807714306959 191474949758711571460439)
            ·
              refine ⟨287212424638067357190659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191474949758711571460439 287212424638067357190659)
              ·
                refine ⟨430818636957101035785989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287212424638067357190659 430818636957101035785989)
                ·
                  refine ⟨80778494429456444209873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430818636957101035785989 80778494429456444209873)
                  ·
                    refine ⟨60583870822092333157405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80778494429456444209873 60583870822092333157405)
                    ·
                      refine ⟨22718951558284624934027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 60583870822092333157405 22718951558284624934027)
                      ·
                        rfl

theorem cell23_44245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_44245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44245 prefixEnd_44245 := by exact prefixLift 44245
  have htrace : WordTrace (prefixWord ++ tailWord_44245) baseStart_44245 baseEnd_44245 := by
    simpa [prefixWord, tailWord_44245, baseEnd_44245] using wordTrace_append hprefix tailTrace_44245
  have hstable : (prefixWord ++ tailWord_44245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44245).length < 2 ^ (prefixWord ++ tailWord_44245).sum := by decide
  have hdescent : baseEnd_44245 < baseStart_44245 := by decide
  rcases family_descends (prefixWord ++ tailWord_44245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44276 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_44276 : Nat := 118140960795 + 44276 * 2 ^ 59
def prefixEnd_44276 : Nat := 4983230072969 + 3 ^ 40 * 44276 * 2
def baseEnd_44276 : Nat := 22734869458574003646385

theorem tailTrace_44276 : CollatzResearch.WordTrace tailWord_44276 prefixEnd_44276 22734869458574003646385 := by
  unfold tailWord_44276
  simp only [CollatzResearch.WordTrace]
  refine ⟨807439193801544291944341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1076585591735392389259121 807439193801544291944341)
  ·
    refine ⟨37848712209447388684891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 807439193801544291944341 37848712209447388684891)
    ·
      refine ⟨56773068314171083027337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37848712209447388684891 56773068314171083027337)
      ·
        refine ⟨42579801235628312270503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56773068314171083027337 42579801235628312270503)
        ·
          refine ⟨63869701853442468405755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42579801235628312270503 63869701853442468405755)
          ·
            refine ⟨95804552780163702608633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63869701853442468405755 95804552780163702608633)
            ·
              refine ⟨71853414585122776956475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95804552780163702608633 71853414585122776956475)
              ·
                refine ⟨107780121877684165434713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71853414585122776956475 107780121877684165434713)
                ·
                  refine ⟨80835091408263124076035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107780121877684165434713 80835091408263124076035)
                  ·
                    refine ⟨121252637112394686114053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80835091408263124076035 121252637112394686114053)
                    ·
                      refine ⟨22734869458574003646385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 121252637112394686114053 22734869458574003646385)
                      ·
                        rfl

theorem cell23_44276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_44276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44276 prefixEnd_44276 := by exact prefixLift 44276
  have htrace : WordTrace (prefixWord ++ tailWord_44276) baseStart_44276 baseEnd_44276 := by
    simpa [prefixWord, tailWord_44276, baseEnd_44276] using wordTrace_append hprefix tailTrace_44276
  have hstable : (prefixWord ++ tailWord_44276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44276).length < 2 ^ (prefixWord ++ tailWord_44276).sum := by decide
  have hdescent : baseEnd_44276 < baseStart_44276 := by decide
  rcases family_descends (prefixWord ++ tailWord_44276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44302 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2]
def baseStart_44302 : Nat := 118140960795 + 44302 * 2 ^ 59
def prefixEnd_44302 : Nat := 4983230072969 + 3 ^ 40 * 44302 * 2
def baseEnd_44302 : Nat := 22748219955590901921265

theorem tailTrace_44302 : CollatzResearch.WordTrace tailWord_44302 prefixEnd_44302 22748219955590901921265 := by
  unfold tailWord_44302
  simp only [CollatzResearch.WordTrace]
  refine ⟨201978335688611878041895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1077217790339263349556773 201978335688611878041895)
  ·
    refine ⟨302967503532917817062843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201978335688611878041895 302967503532917817062843)
    ·
      refine ⟨454451255299376725594265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302967503532917817062843 454451255299376725594265)
      ·
        refine ⟨340838441474532544195699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454451255299376725594265 340838441474532544195699)
        ·
          refine ⟨511257662211798816293549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340838441474532544195699 511257662211798816293549)
          ·
            refine ⟨191721623329424556110081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 511257662211798816293549 191721623329424556110081)
            ·
              refine ⟨143791217497068417082561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191721623329424556110081 143791217497068417082561)
              ·
                refine ⟨107843413122801312811921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143791217497068417082561 107843413122801312811921)
                ·
                  refine ⟨80882559842100984608941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107843413122801312811921 80882559842100984608941)
                  ·
                    refine ⟨30330959940787869228353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80882559842100984608941 30330959940787869228353)
                    ·
                      refine ⟨22748219955590901921265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 30330959940787869228353 22748219955590901921265)
                      ·
                        rfl

theorem cell23_44302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_44302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44302 prefixEnd_44302 := by exact prefixLift 44302
  have htrace : WordTrace (prefixWord ++ tailWord_44302) baseStart_44302 baseEnd_44302 := by
    simpa [prefixWord, tailWord_44302, baseEnd_44302] using wordTrace_append hprefix tailTrace_44302
  have hstable : (prefixWord ++ tailWord_44302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44302).length < 2 ^ (prefixWord ++ tailWord_44302).sum := by decide
  have hdescent : baseEnd_44302 < baseStart_44302 := by decide
  rcases family_descends (prefixWord ++ tailWord_44302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44325 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_44325 : Nat := 118140960795 + 44325 * 2 ^ 59
def prefixEnd_44325 : Nat := 4983230072969 + 3 ^ 40 * 44325 * 2
def baseEnd_44325 : Nat := 7586676670214770644553

theorem tailTrace_44325 : CollatzResearch.WordTrace tailWord_44325 prefixEnd_44325 7586676670214770644553 := by
  unfold tailWord_44325
  simp only [CollatzResearch.WordTrace]
  refine ⟨1616665564425569952422429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1077777042950379968281619 1616665564425569952422429)
  ·
    refine ⟨606249586659588732158411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1616665564425569952422429 606249586659588732158411)
    ·
      refine ⟨909374379989383098237617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 606249586659588732158411 909374379989383098237617)
      ·
        refine ⟨682030784992037323678213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 909374379989383098237617 682030784992037323678213)
        ·
          refine ⟨127880772186006998189665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 682030784992037323678213 127880772186006998189665)
          ·
            refine ⟨95910579139505248642249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127880772186006998189665 95910579139505248642249)
            ·
              refine ⟨71932934354628936481687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95910579139505248642249 71932934354628936481687)
              ·
                refine ⟨107899401531943404722531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71932934354628936481687 107899401531943404722531)
                ·
                  refine ⟨161849102297915107083797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107899401531943404722531 161849102297915107083797)
                  ·
                    refine ⟨7586676670214770644553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161849102297915107083797 7586676670214770644553)
                    ·
                      rfl

theorem cell23_44325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_44325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44325 prefixEnd_44325 := by exact prefixLift 44325
  have htrace : WordTrace (prefixWord ++ tailWord_44325) baseStart_44325 baseEnd_44325 := by
    simpa [prefixWord, tailWord_44325, baseEnd_44325] using wordTrace_append hprefix tailTrace_44325
  have hstable : (prefixWord ++ tailWord_44325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44325).length < 2 ^ (prefixWord ++ tailWord_44325).sum := by decide
  have hdescent : baseEnd_44325 < baseStart_44325 := by decide
  rcases family_descends (prefixWord ++ tailWord_44325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44335 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 1, 2, 3]
def baseStart_44335 : Nat := 118140960795 + 44335 * 2 ^ 59
def prefixEnd_44335 : Nat := 4983230072969 + 3 ^ 40 * 44335 * 2
def baseEnd_44335 : Nat := 22765164817189272808613

theorem tailTrace_44335 : CollatzResearch.WordTrace tailWord_44335 prefixEnd_44335 22765164817189272808613 := by
  unfold tailWord_44335
  simp only [CollatzResearch.WordTrace]
  refine ⟨1617030294389341660286459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1078020196259561106857639 1617030294389341660286459)
  ·
    refine ⟨2425545441584012490429689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1617030294389341660286459 2425545441584012490429689)
    ·
      refine ⟨1819159081188009367822267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2425545441584012490429689 1819159081188009367822267)
      ·
        refine ⟨2728738621782014051733401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1819159081188009367822267 2728738621782014051733401)
        ·
          refine ⟨2046553966336510538800051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2728738621782014051733401 2046553966336510538800051)
          ·
            refine ⟨3069830949504765808200077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046553966336510538800051 3069830949504765808200077)
            ·
              refine ⟨1151186606064287178075029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3069830949504765808200077 1151186606064287178075029)
              ·
                refine ⟨53961872159263461472267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1151186606064287178075029 53961872159263461472267)
                ·
                  refine ⟨80942808238895192208401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53961872159263461472267 80942808238895192208401)
                  ·
                    refine ⟨60707106179171394156301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80942808238895192208401 60707106179171394156301)
                    ·
                      refine ⟨22765164817189272808613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 60707106179171394156301 22765164817189272808613)
                      ·
                        rfl

theorem cell23_44335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 2, 3].length) (baseStart_44335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44335 prefixEnd_44335 := by exact prefixLift 44335
  have htrace : WordTrace (prefixWord ++ tailWord_44335) baseStart_44335 baseEnd_44335 := by
    simpa [prefixWord, tailWord_44335, baseEnd_44335] using wordTrace_append hprefix tailTrace_44335
  have hstable : (prefixWord ++ tailWord_44335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44335).length < 2 ^ (prefixWord ++ tailWord_44335).sum := by decide
  have hdescent : baseEnd_44335 < baseStart_44335 := by decide
  rcases family_descends (prefixWord ++ tailWord_44335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44349 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_44349 : Nat := 118140960795 + 44349 * 2 ^ 59
def prefixEnd_44349 : Nat := 4983230072969 + 3 ^ 40 * 44349 * 2
def baseEnd_44349 : Nat := 22772353546352218033549

theorem tailTrace_44349 : CollatzResearch.WordTrace tailWord_44349 prefixEnd_44349 22772353546352218033549 := by
  unfold tailWord_44349
  simp only [CollatzResearch.WordTrace]
  refine ⟨1617540916338622051296101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1078360610892414700864067 1617540916338622051296101)
  ·
    refine ⟨303288921813491634618019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1617540916338622051296101 303288921813491634618019)
    ·
      refine ⟨454933382720237451927029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303288921813491634618019 454933382720237451927029)
      ·
        refine ⟨42650004630022261118159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 454933382720237451927029 42650004630022261118159)
        ·
          refine ⟨63975006945033391677239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42650004630022261118159 63975006945033391677239)
          ·
            refine ⟨95962510417550087515859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63975006945033391677239 95962510417550087515859)
            ·
              refine ⟨143943765626325131273789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95962510417550087515859 143943765626325131273789)
              ·
                refine ⟨53978912109871924227671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143943765626325131273789 53978912109871924227671)
                ·
                  refine ⟨80968368164807886341507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53978912109871924227671 80968368164807886341507)
                  ·
                    refine ⟨121452552247211829512261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80968368164807886341507 121452552247211829512261)
                    ·
                      refine ⟨22772353546352218033549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 121452552247211829512261 22772353546352218033549)
                      ·
                        rfl

theorem cell23_44349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_44349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44349 prefixEnd_44349 := by exact prefixLift 44349
  have htrace : WordTrace (prefixWord ++ tailWord_44349) baseStart_44349 baseEnd_44349 := by
    simpa [prefixWord, tailWord_44349, baseEnd_44349] using wordTrace_append hprefix tailTrace_44349
  have hstable : (prefixWord ++ tailWord_44349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44349).length < 2 ^ (prefixWord ++ tailWord_44349).sum := by decide
  have hdescent : baseEnd_44349 < baseStart_44349 := by decide
  rcases family_descends (prefixWord ++ tailWord_44349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44456 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_44456 : Nat := 118140960795 + 44456 * 2 ^ 59
def prefixEnd_44456 : Nat := 4983230072969 + 3 ^ 40 * 44456 * 2
def baseEnd_44456 : Nat := 22827295976383299395557

theorem tailTrace_44456 : CollatzResearch.WordTrace tailWord_44456 prefixEnd_44456 22827295976383299395557 := by
  unfold tailWord_44456
  simp only [CollatzResearch.WordTrace]
  refine ⟨810721763475489662720611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1080962351300652883627481 810721763475489662720611)
  ·
    refine ⟨1216082645213234494080917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810721763475489662720611 1216082645213234494080917)
    ·
      refine ⟨57003873994370366910043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1216082645213234494080917 57003873994370366910043)
      ·
        refine ⟨85505810991555550365065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57003873994370366910043 85505810991555550365065)
        ·
          refine ⟨64129358243666662773799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85505810991555550365065 64129358243666662773799)
          ·
            refine ⟨96194037365499994160699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64129358243666662773799 96194037365499994160699)
            ·
              refine ⟨144291056048249991241049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96194037365499994160699 144291056048249991241049)
              ·
                refine ⟨108218292036187493430787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144291056048249991241049 108218292036187493430787)
                ·
                  refine ⟨162327438054281240146181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108218292036187493430787 162327438054281240146181)
                  ·
                    refine ⟨30436394635177732527409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162327438054281240146181 30436394635177732527409)
                    ·
                      refine ⟨22827295976383299395557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 30436394635177732527409 22827295976383299395557)
                      ·
                        rfl

theorem cell23_44456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_44456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44456 prefixEnd_44456 := by exact prefixLift 44456
  have htrace : WordTrace (prefixWord ++ tailWord_44456) baseStart_44456 baseEnd_44456 := by
    simpa [prefixWord, tailWord_44456, baseEnd_44456] using wordTrace_append hprefix tailTrace_44456
  have hstable : (prefixWord ++ tailWord_44456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44456).length < 2 ^ (prefixWord ++ tailWord_44456).sum := by decide
  have hdescent : baseEnd_44456 < baseStart_44456 := by decide
  rcases family_descends (prefixWord ++ tailWord_44456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44495 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 4]
def baseStart_44495 : Nat := 118140960795 + 44495 * 2 ^ 59
def prefixEnd_44495 : Nat := 4983230072969 + 3 ^ 40 * 44495 * 2
def baseEnd_44495 : Nat := 22847321721908646807877

theorem tailTrace_44495 : CollatzResearch.WordTrace tailWord_44495 prefixEnd_44495 22847321721908646807877 := by
  unfold tailWord_44495
  simp only [CollatzResearch.WordTrace]
  refine ⟨1622865973809688986110939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1081910649206459324073959 1622865973809688986110939)
  ·
    refine ⟨2434298960714533479166409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1622865973809688986110939 2434298960714533479166409)
    ·
      refine ⟨1825724220535900109374807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2434298960714533479166409 1825724220535900109374807)
      ·
        refine ⟨2738586330803850164062211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1825724220535900109374807 2738586330803850164062211)
        ·
          refine ⟨4107879496205775246093317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2738586330803850164062211 4107879496205775246093317)
          ·
            refine ⟨770227405538582858642497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4107879496205775246093317 770227405538582858642497)
            ·
              refine ⟨577670554153937143981873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770227405538582858642497 577670554153937143981873)
              ·
                refine ⟨433252915615452857986405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577670554153937143981873 433252915615452857986405)
                ·
                  refine ⟨81234921677897410872451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 433252915615452857986405 81234921677897410872451)
                  ·
                    refine ⟨121852382516846116308677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81234921677897410872451 121852382516846116308677)
                    ·
                      refine ⟨22847321721908646807877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 121852382516846116308677 22847321721908646807877)
                      ·
                        rfl

theorem cell23_44495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_44495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44495 prefixEnd_44495 := by exact prefixLift 44495
  have htrace : WordTrace (prefixWord ++ tailWord_44495) baseStart_44495 baseEnd_44495 := by
    simpa [prefixWord, tailWord_44495, baseEnd_44495] using wordTrace_append hprefix tailTrace_44495
  have hstable : (prefixWord ++ tailWord_44495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44495).length < 2 ^ (prefixWord ++ tailWord_44495).sum := by decide
  have hdescent : baseEnd_44495 < baseStart_44495 := by decide
  rcases family_descends (prefixWord ++ tailWord_44495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44509 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_44509 : Nat := 118140960795 + 44509 * 2 ^ 59
def prefixEnd_44509 : Nat := 4983230072969 + 3 ^ 40 * 44509 * 2
def baseEnd_44509 : Nat := 7618170150357197344271

theorem tailTrace_44509 : CollatzResearch.WordTrace tailWord_44509 prefixEnd_44509 7618170150357197344271 := by
  unfold tailWord_44509
  simp only [CollatzResearch.WordTrace]
  refine ⟨1623376595758969377120581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1082251063839312918080387 1623376595758969377120581)
  ·
    refine ⟨304383111704806758210109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1623376595758969377120581 304383111704806758210109)
    ·
      refine ⟨114143666889302534328791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304383111704806758210109 114143666889302534328791)
      ·
        refine ⟨171215500333953801493187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114143666889302534328791 171215500333953801493187)
        ·
          refine ⟨256823250500930702239781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171215500333953801493187 256823250500930702239781)
          ·
            refine ⟨48154359468924506669959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256823250500930702239781 48154359468924506669959)
            ·
              refine ⟨72231539203386760004939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48154359468924506669959 72231539203386760004939)
              ·
                refine ⟨108347308805080140007409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72231539203386760004939 108347308805080140007409)
                ·
                  refine ⟨81260481603810105005557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108347308805080140007409 81260481603810105005557)
                  ·
                    refine ⟨7618170150357197344271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81260481603810105005557 7618170150357197344271)
                    ·
                      rfl

theorem cell23_44509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_44509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44509 prefixEnd_44509 := by exact prefixLift 44509
  have htrace : WordTrace (prefixWord ++ tailWord_44509) baseStart_44509 baseEnd_44509 := by
    simpa [prefixWord, tailWord_44509, baseEnd_44509] using wordTrace_append hprefix tailTrace_44509
  have hstable : (prefixWord ++ tailWord_44509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44509).length < 2 ^ (prefixWord ++ tailWord_44509).sum := by decide
  have hdescent : baseEnd_44509 < baseStart_44509 := by decide
  rcases family_descends (prefixWord ++ tailWord_44509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44535 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 6]
def baseStart_44535 : Nat := 118140960795 + 44535 * 2 ^ 59
def prefixEnd_44535 : Nat := 4983230072969 + 3 ^ 40 * 44535 * 2
def baseEnd_44535 : Nat := 2540873438676498923077

theorem tailTrace_44535 : CollatzResearch.WordTrace tailWord_44535 prefixEnd_44535 2540873438676498923077 := by
  unfold tailWord_44535
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624324893664775817567059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1082883262443183878378039 1624324893664775817567059)
  ·
    refine ⟨2436487340497163726350589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1624324893664775817567059 2436487340497163726350589)
    ·
      refine ⟨913682752686436397381471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2436487340497163726350589 913682752686436397381471)
      ·
        refine ⟨1370524129029654596072207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913682752686436397381471 1370524129029654596072207)
        ·
          refine ⟨2055786193544481894108311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370524129029654596072207 2055786193544481894108311)
          ·
            refine ⟨3083679290316722841162467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055786193544481894108311 3083679290316722841162467)
            ·
              refine ⟨4625518935475084261743701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083679290316722841162467 4625518935475084261743701)
              ·
                refine ⟨54205300025098643692309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4625518935475084261743701 54205300025098643692309)
                ·
                  refine ⟨2540873438676498923077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54205300025098643692309 2540873438676498923077)
                  ·
                    rfl

theorem cell23_44535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 6].length) (baseStart_44535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44535 prefixEnd_44535 := by exact prefixLift 44535
  have htrace : WordTrace (prefixWord ++ tailWord_44535) baseStart_44535 baseEnd_44535 := by
    simpa [prefixWord, tailWord_44535, baseEnd_44535] using wordTrace_append hprefix tailTrace_44535
  have hstable : (prefixWord ++ tailWord_44535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44535).length < 2 ^ (prefixWord ++ tailWord_44535).sum := by decide
  have hdescent : baseEnd_44535 < baseStart_44535 := by decide
  rcases family_descends (prefixWord ++ tailWord_44535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44546 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_44546 : Nat := 118140960795 + 44546 * 2 ^ 59
def prefixEnd_44546 : Nat := 4983230072969 + 3 ^ 40 * 44546 * 2
def baseEnd_44546 : Nat := 22873509235287947270143

theorem tailTrace_44546 : CollatzResearch.WordTrace tailWord_44546 prefixEnd_44546 22873509235287947270143 := by
  unfold tailWord_44546
  simp only [CollatzResearch.WordTrace]
  refine ⟨406181524156231174054373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1083150731083283130811661 406181524156231174054373)
  ·
    refine ⟨76159035779293345135195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 406181524156231174054373 76159035779293345135195)
    ·
      refine ⟨114238553668940017702793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76159035779293345135195 114238553668940017702793)
      ·
        refine ⟨85678915251705013277095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114238553668940017702793 85678915251705013277095)
        ·
          refine ⟨128518372877557519915643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85678915251705013277095 128518372877557519915643)
          ·
            refine ⟨192777559316336279873465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128518372877557519915643 192777559316336279873465)
            ·
              refine ⟨144583169487252209905099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192777559316336279873465 144583169487252209905099)
              ·
                refine ⟨216874754230878314857649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144583169487252209905099 216874754230878314857649)
                ·
                  refine ⟨162656065673158736143237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216874754230878314857649 162656065673158736143237)
                  ·
                    refine ⟨30498012313717263026857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162656065673158736143237 30498012313717263026857)
                    ·
                      refine ⟨22873509235287947270143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 30498012313717263026857 22873509235287947270143)
                      ·
                        rfl

theorem cell23_44546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_44546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44546 prefixEnd_44546 := by exact prefixLift 44546
  have htrace : WordTrace (prefixWord ++ tailWord_44546) baseStart_44546 baseEnd_44546 := by
    simpa [prefixWord, tailWord_44546, baseEnd_44546] using wordTrace_append hprefix tailTrace_44546
  have hstable : (prefixWord ++ tailWord_44546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44546).length < 2 ^ (prefixWord ++ tailWord_44546).sum := by decide
  have hdescent : baseEnd_44546 < baseStart_44546 := by decide
  rcases family_descends (prefixWord ++ tailWord_44546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44602 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_44602 : Nat := 118140960795 + 44602 * 2 ^ 59
def prefixEnd_44602 : Nat := 4983230072969 + 3 ^ 40 * 44602 * 2
def baseEnd_44602 : Nat := 22902264151939728169885

theorem tailTrace_44602 : CollatzResearch.WordTrace tailWord_44602 prefixEnd_44602 22902264151939728169885 := by
  unfold tailWord_44602
  simp only [CollatzResearch.WordTrace]
  refine ⟨406692146105511565064015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1084512389614697506837373 406692146105511565064015)
  ·
    refine ⟨610038219158267347596023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 406692146105511565064015 610038219158267347596023)
    ·
      refine ⟨915057328737401021394035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610038219158267347596023 915057328737401021394035)
      ·
        refine ⟨1372585993106101532091053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915057328737401021394035 1372585993106101532091053)
        ·
          refine ⟨514719747414788074534145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1372585993106101532091053 514719747414788074534145)
          ·
            refine ⟨386039810561091055900609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514719747414788074534145 386039810561091055900609)
            ·
              refine ⟨289529857920818291925457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386039810561091055900609 289529857920818291925457)
              ·
                refine ⟨217147393440613718944093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289529857920818291925457 217147393440613718944093)
                ·
                  refine ⟨81430272540230144604035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217147393440613718944093 81430272540230144604035)
                  ·
                    refine ⟨122145408810345216906053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81430272540230144604035 122145408810345216906053)
                    ·
                      refine ⟨22902264151939728169885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 122145408810345216906053 22902264151939728169885)
                      ·
                        rfl

theorem cell23_44602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_44602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44602 prefixEnd_44602 := by exact prefixLift 44602
  have htrace : WordTrace (prefixWord ++ tailWord_44602) baseStart_44602 baseEnd_44602 := by
    simpa [prefixWord, tailWord_44602, baseEnd_44602] using wordTrace_append hprefix tailTrace_44602
  have hstable : (prefixWord ++ tailWord_44602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44602).length < 2 ^ (prefixWord ++ tailWord_44602).sum := by decide
  have hdescent : baseEnd_44602 < baseStart_44602 := by decide
  rcases family_descends (prefixWord ++ tailWord_44602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44619 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 5, 2, 2]
def baseStart_44619 : Nat := 118140960795 + 44619 * 2 ^ 59
def prefixEnd_44619 : Nat := 4983230072969 + 3 ^ 40 * 44619 * 2
def baseEnd_44619 : Nat := 22910993323066161657307

theorem tailTrace_44619 : CollatzResearch.WordTrace tailWord_44619 prefixEnd_44619 22910993323066161657307 := by
  unfold tailWord_44619
  simp only [CollatzResearch.WordTrace]
  refine ⟨1627388625360458163624911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1084925750240305442416607 1627388625360458163624911)
  ·
    refine ⟨2441082938040687245437367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1627388625360458163624911 2441082938040687245437367)
    ·
      refine ⟨3661624407061030868156051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2441082938040687245437367 3661624407061030868156051)
      ·
        refine ⟨5492436610591546302234077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3661624407061030868156051 5492436610591546302234077)
        ·
          refine ⟨2059663728971829863337779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5492436610591546302234077 2059663728971829863337779)
          ·
            refine ⟨3089495593457744795006669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059663728971829863337779 3089495593457744795006669)
            ·
              refine ⟨1158560847546654298127501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3089495593457744795006669 1158560847546654298127501)
              ·
                refine ⟨434460317829995361797813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1158560847546654298127501 434460317829995361797813)
                ·
                  refine ⟨40730654796562065168545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 434460317829995361797813 40730654796562065168545)
                  ·
                    refine ⟨30547991097421548876409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40730654796562065168545 30547991097421548876409)
                    ·
                      refine ⟨22910993323066161657307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 30547991097421548876409 22910993323066161657307)
                      ·
                        rfl

theorem cell23_44619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 2, 2].length) (baseStart_44619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44619 prefixEnd_44619 := by exact prefixLift 44619
  have htrace : WordTrace (prefixWord ++ tailWord_44619) baseStart_44619 baseEnd_44619 := by
    simpa [prefixWord, tailWord_44619, baseEnd_44619] using wordTrace_append hprefix tailTrace_44619
  have hstable : (prefixWord ++ tailWord_44619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44619).length < 2 ^ (prefixWord ++ tailWord_44619).sum := by decide
  have hdescent : baseEnd_44619 < baseStart_44619 := by decide
  rcases family_descends (prefixWord ++ tailWord_44619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44625 : List Nat := [1, 2, 2, 1, 3, 2, 1, 11]
def baseStart_44625 : Nat := 118140960795 + 44625 * 2 ^ 59
def prefixEnd_44625 : Nat := 4983230072969 + 3 ^ 40 * 44625 * 2
def baseEnd_44625 : Nat := 848669415073819932677

theorem tailTrace_44625 : CollatzResearch.WordTrace tailWord_44625 prefixEnd_44625 848669415073819932677 := by
  unfold tailWord_44625
  simp only [CollatzResearch.WordTrace]
  refine ⟨1627607463338721188343329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1085071642225814125562219 1627607463338721188343329)
  ·
    refine ⟨1220705597504040891257497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1627607463338721188343329 1220705597504040891257497)
    ·
      refine ⟨915529198128030668443123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1220705597504040891257497 915529198128030668443123)
      ·
        refine ⟨1373293797192046002664685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915529198128030668443123 1373293797192046002664685)
        ·
          refine ⟨514985173947017250999257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1373293797192046002664685 514985173947017250999257)
          ·
            refine ⟨386238880460262938249443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514985173947017250999257 386238880460262938249443)
            ·
              refine ⟨579358320690394407374165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386238880460262938249443 579358320690394407374165)
              ·
                refine ⟨848669415073819932677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 579358320690394407374165 848669415073819932677)
                ·
                  rfl

theorem cell23_44625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 11].length) (baseStart_44625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44625 prefixEnd_44625 := by exact prefixLift 44625
  have htrace : WordTrace (prefixWord ++ tailWord_44625) baseStart_44625 baseEnd_44625 := by
    simpa [prefixWord, tailWord_44625, baseEnd_44625] using wordTrace_append hprefix tailTrace_44625
  have hstable : (prefixWord ++ tailWord_44625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44625).length < 2 ^ (prefixWord ++ tailWord_44625).sum := by decide
  have hdescent : baseEnd_44625 < baseStart_44625 := by decide
  rcases family_descends (prefixWord ++ tailWord_44625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44652 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 3]
def baseStart_44652 : Nat := 118140960795 + 44652 * 2 ^ 59
def prefixEnd_44652 : Nat := 4983230072969 + 3 ^ 40 * 44652 * 2
def baseEnd_44652 : Nat := 22927938184664532544655

theorem tailTrace_44652 : CollatzResearch.WordTrace tailWord_44652 prefixEnd_44652 22927938184664532544655 := by
  unfold tailWord_44652
  simp only [CollatzResearch.WordTrace]
  refine ⟨814296117120452399788105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1085728156160603199717473 814296117120452399788105)
  ·
    refine ⟨610722087840339299841079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 814296117120452399788105 610722087840339299841079)
    ·
      refine ⟨916083131760508949761619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610722087840339299841079 916083131760508949761619)
      ·
        refine ⟨1374124697640763424642429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916083131760508949761619 1374124697640763424642429)
        ·
          refine ⟨515296761615286284240911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1374124697640763424642429 515296761615286284240911)
          ·
            refine ⟨772945142422929426361367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515296761615286284240911 772945142422929426361367)
            ·
              refine ⟨1159417713634394139542051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772945142422929426361367 1159417713634394139542051)
              ·
                refine ⟨1739126570451591209313077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159417713634394139542051 1739126570451591209313077)
                ·
                  refine ⟨163043115979836675873101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1739126570451591209313077 163043115979836675873101)
                  ·
                    refine ⟨61141168492438753452413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163043115979836675873101 61141168492438753452413)
                    ·
                      refine ⟨22927938184664532544655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 61141168492438753452413 22927938184664532544655)
                      ·
                        rfl

theorem cell23_44652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_44652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44652 prefixEnd_44652 := by exact prefixLift 44652
  have htrace : WordTrace (prefixWord ++ tailWord_44652) baseStart_44652 baseEnd_44652 := by
    simpa [prefixWord, tailWord_44652, baseEnd_44652] using wordTrace_append hprefix tailTrace_44652
  have hstable : (prefixWord ++ tailWord_44652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44652).length < 2 ^ (prefixWord ++ tailWord_44652).sum := by decide
  have hdescent : baseEnd_44652 < baseStart_44652 := by decide
  rcases family_descends (prefixWord ++ tailWord_44652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44669 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_44669 : Nat := 118140960795 + 44669 * 2 ^ 59
def prefixEnd_44669 : Nat := 4983230072969 + 3 ^ 40 * 44669 * 2
def baseEnd_44669 : Nat := 22936667355790966032077

theorem tailTrace_44669 : CollatzResearch.WordTrace tailWord_44669 prefixEnd_44669 22936667355790966032077 := by
  unfold tailWord_44669
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629212275179316702945061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1086141516786211135296707 1629212275179316702945061)
  ·
    refine ⟨305477301596121881802199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1629212275179316702945061 305477301596121881802199)
    ·
      refine ⟨458215952394182822703299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305477301596121881802199 458215952394182822703299)
      ·
        refine ⟨687323928591274234054949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458215952394182822703299 687323928591274234054949)
        ·
          refine ⟨128873236610863918885303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 687323928591274234054949 128873236610863918885303)
          ·
            refine ⟨193309854916295878327955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128873236610863918885303 193309854916295878327955)
            ·
              refine ⟨289964782374443817491933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193309854916295878327955 289964782374443817491933)
              ·
                refine ⟨108736793390416431559475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289964782374443817491933 108736793390416431559475)
                ·
                  refine ⟨163105190085624647339213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108736793390416431559475 163105190085624647339213)
                  ·
                    refine ⟨61164446282109242752205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163105190085624647339213 61164446282109242752205)
                    ·
                      refine ⟨22936667355790966032077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 61164446282109242752205 22936667355790966032077)
                      ·
                        rfl

theorem cell23_44669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_44669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44669 prefixEnd_44669 := by exact prefixLift 44669
  have htrace : WordTrace (prefixWord ++ tailWord_44669) baseStart_44669 baseEnd_44669 := by
    simpa [prefixWord, tailWord_44669, baseEnd_44669] using wordTrace_append hprefix tailTrace_44669
  have hstable : (prefixWord ++ tailWord_44669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44669).length < 2 ^ (prefixWord ++ tailWord_44669).sum := by decide
  have hdescent : baseEnd_44669 < baseStart_44669 := by decide
  rcases family_descends (prefixWord ++ tailWord_44669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44690 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_44690 : Nat := 118140960795 + 44690 * 2 ^ 59
def prefixEnd_44690 : Nat := 4983230072969 + 3 ^ 40 * 44690 * 2
def baseEnd_44690 : Nat := 22947450449535383869481

theorem tailTrace_44690 : CollatzResearch.WordTrace tailWord_44690 prefixEnd_44690 22947450449535383869481 := by
  unfold tailWord_44690
  simp only [CollatzResearch.WordTrace]
  refine ⟨407494552025809322364881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1086652138735491526306349 407494552025809322364881)
  ·
    refine ⟨305620914019356991773661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 407494552025809322364881 305620914019356991773661)
    ·
      refine ⟨114607842757258871915123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305620914019356991773661 114607842757258871915123)
      ·
        refine ⟨171911764135888307872685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114607842757258871915123 171911764135888307872685)
        ·
          refine ⟨64466911550958115452257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171911764135888307872685 64466911550958115452257)
          ·
            refine ⟨48350183663218586589193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64466911550958115452257 48350183663218586589193)
            ·
              refine ⟨36262637747413939941895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48350183663218586589193 36262637747413939941895)
              ·
                refine ⟨54393956621120909912843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36262637747413939941895 54393956621120909912843)
                ·
                  refine ⟨81590934931681364869265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54393956621120909912843 81590934931681364869265)
                  ·
                    refine ⟨61193201198761023651949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81590934931681364869265 61193201198761023651949)
                    ·
                      refine ⟨22947450449535383869481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 61193201198761023651949 22947450449535383869481)
                      ·
                        rfl

theorem cell23_44690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_44690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44690 prefixEnd_44690 := by exact prefixLift 44690
  have htrace : WordTrace (prefixWord ++ tailWord_44690) baseStart_44690 baseEnd_44690 := by
    simpa [prefixWord, tailWord_44690, baseEnd_44690] using wordTrace_append hprefix tailTrace_44690
  have hstable : (prefixWord ++ tailWord_44690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44690).length < 2 ^ (prefixWord ++ tailWord_44690).sum := by decide
  have hdescent : baseEnd_44690 < baseStart_44690 := by decide
  rcases family_descends (prefixWord ++ tailWord_44690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44703 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 4, 1, 3]
def baseStart_44703 : Nat := 118140960795 + 44703 * 2 ^ 59
def prefixEnd_44703 : Nat := 4983230072969 + 3 ^ 40 * 44703 * 2
def baseEnd_44703 : Nat := 22954125698043833006921

theorem tailTrace_44703 : CollatzResearch.WordTrace tailWord_44703 prefixEnd_44703 22954125698043833006921 := by
  unfold tailWord_44703
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630452357056140509682763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1086968238037427006455175 1630452357056140509682763)
  ·
    refine ⟨2445678535584210764524145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1630452357056140509682763 2445678535584210764524145)
    ·
      refine ⟨1834258901688158073393109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2445678535584210764524145 1834258901688158073393109)
      ·
        refine ⟨42990443008316204845151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 1834258901688158073393109 42990443008316204845151)
        ·
          refine ⟨64485664512474307267727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42990443008316204845151 64485664512474307267727)
          ·
            refine ⟨96728496768711460901591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64485664512474307267727 96728496768711460901591)
            ·
              refine ⟨145092745153067191352387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96728496768711460901591 145092745153067191352387)
              ·
                refine ⟨217639117729600787028581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145092745153067191352387 217639117729600787028581)
                ·
                  refine ⟨40807334574300147567859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217639117729600787028581 40807334574300147567859)
                  ·
                    refine ⟨61211001861450221351789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40807334574300147567859 61211001861450221351789)
                    ·
                      refine ⟨22954125698043833006921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 61211001861450221351789 22954125698043833006921)
                      ·
                        rfl

theorem cell23_44703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_44703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44703 prefixEnd_44703 := by exact prefixLift 44703
  have htrace : WordTrace (prefixWord ++ tailWord_44703) baseStart_44703 baseEnd_44703 := by
    simpa [prefixWord, tailWord_44703, baseEnd_44703] using wordTrace_append hprefix tailTrace_44703
  have hstable : (prefixWord ++ tailWord_44703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44703).length < 2 ^ (prefixWord ++ tailWord_44703).sum := by decide
  have hdescent : baseEnd_44703 < baseStart_44703 := by decide
  rcases family_descends (prefixWord ++ tailWord_44703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44709 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 3, 4, 2]
def baseStart_44709 : Nat := 118140960795 + 44709 * 2 ^ 59
def prefixEnd_44709 : Nat := 4983230072969 + 3 ^ 40 * 44709 * 2
def baseEnd_44709 : Nat := 22957206581970809531893

theorem tailTrace_44709 : CollatzResearch.WordTrace tailWord_44709 prefixEnd_44709 22957206581970809531893 := by
  unfold tailWord_44709
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630671195034403534401181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1087114130022935689600787 1630671195034403534401181)
  ·
    refine ⟨611501698137901325400443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1630671195034403534401181 611501698137901325400443)
    ·
      refine ⟨917252547206851988100665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611501698137901325400443 917252547206851988100665)
      ·
        refine ⟨687939410405138991075499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 917252547206851988100665 687939410405138991075499)
        ·
          refine ⟨1031909115607708486613249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687939410405138991075499 1031909115607708486613249)
          ·
            refine ⟨773931836705781364959937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031909115607708486613249 773931836705781364959937)
            ·
              refine ⟨580448877529336023719953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773931836705781364959937 580448877529336023719953)
              ·
                refine ⟨435336658147002017789965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580448877529336023719953 435336658147002017789965)
                ·
                  refine ⟨163251246805125756671237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 435336658147002017789965 163251246805125756671237)
                  ·
                    refine ⟨30609608775961079375857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 163251246805125756671237 30609608775961079375857)
                    ·
                      refine ⟨22957206581970809531893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 30609608775961079375857 22957206581970809531893)
                      ·
                        rfl

theorem cell23_44709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_44709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44709 prefixEnd_44709 := by exact prefixLift 44709
  have htrace : WordTrace (prefixWord ++ tailWord_44709) baseStart_44709 baseEnd_44709 := by
    simpa [prefixWord, tailWord_44709, baseEnd_44709] using wordTrace_append hprefix tailTrace_44709
  have hstable : (prefixWord ++ tailWord_44709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44709).length < 2 ^ (prefixWord ++ tailWord_44709).sum := by decide
  have hdescent : baseEnd_44709 < baseStart_44709 := by decide
  rcases family_descends (prefixWord ++ tailWord_44709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44738 : List Nat := [3, 5, 1, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_44738 : Nat := 118140960795 + 44738 * 2 ^ 59
def prefixEnd_44738 : Nat := 4983230072969 + 3 ^ 40 * 44738 * 2
def baseEnd_44738 : Nat := 22972097520951196069261

theorem tailTrace_44738 : CollatzResearch.WordTrace tailWord_44738 prefixEnd_44738 22972097520951196069261 := by
  unfold tailWord_44738
  simp only [CollatzResearch.WordTrace]
  refine ⟨407932227982335371801717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1087819274619560991471245 407932227982335371801717)
  ·
    refine ⟨38243646373343941106411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 407932227982335371801717 38243646373343941106411)
    ·
      refine ⟨57365469560015911659617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38243646373343941106411 57365469560015911659617)
      ·
        refine ⟨43024102170011933744713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57365469560015911659617 43024102170011933744713)
        ·
          refine ⟨32268076627508950308535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43024102170011933744713 32268076627508950308535)
          ·
            refine ⟨48402114941263425462803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32268076627508950308535 48402114941263425462803)
            ·
              refine ⟨72603172411895138194205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48402114941263425462803 72603172411895138194205)
              ·
                refine ⟨27226189654460676822827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72603172411895138194205 27226189654460676822827)
                ·
                  refine ⟨40839284481691015234241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27226189654460676822827 40839284481691015234241)
                  ·
                    refine ⟨30629463361268261425681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40839284481691015234241 30629463361268261425681)
                    ·
                      refine ⟨22972097520951196069261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 30629463361268261425681 22972097520951196069261)
                      ·
                        rfl

theorem cell23_44738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_44738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44738 prefixEnd_44738 := by exact prefixLift 44738
  have htrace : WordTrace (prefixWord ++ tailWord_44738) baseStart_44738 baseEnd_44738 := by
    simpa [prefixWord, tailWord_44738, baseEnd_44738] using wordTrace_append hprefix tailTrace_44738
  have hstable : (prefixWord ++ tailWord_44738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44738).length < 2 ^ (prefixWord ++ tailWord_44738).sum := by decide
  have hdescent : baseEnd_44738 < baseStart_44738 := by decide
  rcases family_descends (prefixWord ++ tailWord_44738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44799 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 4]
def baseStart_44799 : Nat := 118140960795 + 44799 * 2 ^ 59
def prefixEnd_44799 : Nat := 4983230072969 + 3 ^ 40 * 44799 * 2
def baseEnd_44799 : Nat := 23003419840875457406479

theorem tailTrace_44799 : CollatzResearch.WordTrace tailWord_44799 prefixEnd_44799 23003419840875457406479 := by
  unfold tailWord_44799
  simp only [CollatzResearch.WordTrace]
  refine ⟨1633953764708348905177451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1089302509805565936784967 1633953764708348905177451)
  ·
    refine ⟨2450930647062523357766177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1633953764708348905177451 2450930647062523357766177)
    ·
      refine ⟨1838197985296892518324633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2450930647062523357766177 1838197985296892518324633)
      ·
        refine ⟨1378648488972669388743475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1838197985296892518324633 1378648488972669388743475)
        ·
          refine ⟨2067972733459004083115213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378648488972669388743475 2067972733459004083115213)
          ·
            refine ⟨775489775047126531168205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2067972733459004083115213 775489775047126531168205)
            ·
              refine ⟨290808665642672449188077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 775489775047126531168205 290808665642672449188077)
              ·
                refine ⟨109053249616002168445529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290808665642672449188077 109053249616002168445529)
                ·
                  refine ⟨81789937212001626334147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109053249616002168445529 81789937212001626334147)
                  ·
                    refine ⟨122684905818002439501221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81789937212001626334147 122684905818002439501221)
                    ·
                      refine ⟨23003419840875457406479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 122684905818002439501221 23003419840875457406479)
                      ·
                        rfl

theorem cell23_44799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_44799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44799 prefixEnd_44799 := by exact prefixLift 44799
  have htrace : WordTrace (prefixWord ++ tailWord_44799) baseStart_44799 baseEnd_44799 := by
    simpa [prefixWord, tailWord_44799, baseEnd_44799] using wordTrace_append hprefix tailTrace_44799
  have hstable : (prefixWord ++ tailWord_44799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44799).length < 2 ^ (prefixWord ++ tailWord_44799).sum := by decide
  have hdescent : baseEnd_44799 < baseStart_44799 := by decide
  rcases family_descends (prefixWord ++ tailWord_44799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44819 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 3]
def baseStart_44819 : Nat := 118140960795 + 44819 * 2 ^ 59
def prefixEnd_44819 : Nat := 4983230072969 + 3 ^ 40 * 44819 * 2
def baseEnd_44819 : Nat := 23013689453965379156387

theorem tailTrace_44819 : CollatzResearch.WordTrace tailWord_44819 prefixEnd_44819 23013689453965379156387 := by
  unfold tailWord_44819
  simp only [CollatzResearch.WordTrace]
  refine ⟨1634683224635892320905511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1089788816423928213937007 1634683224635892320905511)
  ·
    refine ⟨2452024836953838481358267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1634683224635892320905511 2452024836953838481358267)
    ·
      refine ⟨3678037255430757722037401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2452024836953838481358267 3678037255430757722037401)
      ·
        refine ⟨2758527941573068291528051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3678037255430757722037401 2758527941573068291528051)
        ·
          refine ⟨4137791912359602437292077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758527941573068291528051 4137791912359602437292077)
          ·
            refine ⟨1551671967134850913984529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4137791912359602437292077 1551671967134850913984529)
            ·
              refine ⟨1163753975351138185488397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1551671967134850913984529 1163753975351138185488397)
              ·
                refine ⟨436407740756676819558149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1163753975351138185488397 436407740756676819558149)
                ·
                  refine ⟨81826451391876903667153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436407740756676819558149 81826451391876903667153)
                  ·
                    refine ⟨61369838543907677750365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81826451391876903667153 61369838543907677750365)
                    ·
                      refine ⟨23013689453965379156387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 61369838543907677750365 23013689453965379156387)
                      ·
                        rfl

theorem cell23_44819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 3].length) (baseStart_44819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44819 prefixEnd_44819 := by exact prefixLift 44819
  have htrace : WordTrace (prefixWord ++ tailWord_44819) baseStart_44819 baseEnd_44819 := by
    simpa [prefixWord, tailWord_44819, baseEnd_44819] using wordTrace_append hprefix tailTrace_44819
  have hstable : (prefixWord ++ tailWord_44819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44819).length < 2 ^ (prefixWord ++ tailWord_44819).sum := by decide
  have hdescent : baseEnd_44819 < baseStart_44819 := by decide
  rcases family_descends (prefixWord ++ tailWord_44819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44946 : List Nat := [3, 2, 3, 2, 1, 1, 1, 10]
def baseStart_44946 : Nat := 118140960795 + 44946 * 2 ^ 59
def prefixEnd_44946 : Nat := 4983230072969 + 3 ^ 40 * 44946 * 2
def baseEnd_44946 : Nat := 854774129521717861789

theorem tailTrace_44946 : CollatzResearch.WordTrace tailWord_44946 prefixEnd_44946 854774129521717861789 := by
  unfold tailWord_44946
  simp only [CollatzResearch.WordTrace]
  refine ⟨409828823793948252694673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1092876863450528673852461 409828823793948252694673)
  ·
    refine ⟨307371617845461189521005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 409828823793948252694673 307371617845461189521005)
    ·
      refine ⟨115264356692047946070377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307371617845461189521005 115264356692047946070377)
      ·
        refine ⟨86448267519035959552783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115264356692047946070377 86448267519035959552783)
        ·
          refine ⟨129672401278553939329175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86448267519035959552783 129672401278553939329175)
          ·
            refine ⟨194508601917830908993763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129672401278553939329175 194508601917830908993763)
            ·
              refine ⟨291762902876746363490645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194508601917830908993763 291762902876746363490645)
              ·
                refine ⟨854774129521717861789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 291762902876746363490645 854774129521717861789)
                ·
                  rfl

theorem cell23_44946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 10].length) (baseStart_44946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44946 prefixEnd_44946 := by exact prefixLift 44946
  have htrace : WordTrace (prefixWord ++ tailWord_44946) baseStart_44946 baseEnd_44946 := by
    simpa [prefixWord, tailWord_44946, baseEnd_44946] using wordTrace_append hprefix tailTrace_44946
  have hstable : (prefixWord ++ tailWord_44946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44946).length < 2 ^ (prefixWord ++ tailWord_44946).sum := by decide
  have hdescent : baseEnd_44946 < baseStart_44946 := by decide
  rcases family_descends (prefixWord ++ tailWord_44946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44949 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_44949 : Nat := 118140960795 + 44949 * 2 ^ 59
def prefixEnd_44949 : Nat := 4983230072969 + 3 ^ 40 * 44949 * 2
def baseEnd_44949 : Nat := 23080441939049870530789

theorem tailTrace_44949 : CollatzResearch.WordTrace tailWord_44949 prefixEnd_44949 23080441939049870530789 := by
  unfold tailWord_44949
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639424714164924523137901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1092949809443283015425267 1639424714164924523137901)
  ·
    refine ⟨614784267811846696176713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1639424714164924523137901 614784267811846696176713)
    ·
      refine ⟨461088200858885022132535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 614784267811846696176713 461088200858885022132535)
      ·
        refine ⟨691632301288327533198803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461088200858885022132535 691632301288327533198803)
        ·
          refine ⟨1037448451932491299798205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691632301288327533198803 1037448451932491299798205)
          ·
            refine ⟨389043169474684237424327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1037448451932491299798205 389043169474684237424327)
            ·
              refine ⟨583564754212026356136491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389043169474684237424327 583564754212026356136491)
              ·
                refine ⟨875347131318039534204737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583564754212026356136491 875347131318039534204737)
                ·
                  refine ⟨656510348488529650653553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 875347131318039534204737 656510348488529650653553)
                  ·
                    refine ⟨492382761366397237990165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 656510348488529650653553 492382761366397237990165)
                    ·
                      refine ⟨23080441939049870530789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 492382761366397237990165 23080441939049870530789)
                      ·
                        rfl

theorem cell23_44949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_44949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44949 prefixEnd_44949 := by exact prefixLift 44949
  have htrace : WordTrace (prefixWord ++ tailWord_44949) baseStart_44949 baseEnd_44949 := by
    simpa [prefixWord, tailWord_44949, baseEnd_44949] using wordTrace_append hprefix tailTrace_44949
  have hstable : (prefixWord ++ tailWord_44949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44949).length < 2 ^ (prefixWord ++ tailWord_44949).sum := by decide
  have hdescent : baseEnd_44949 < baseStart_44949 := by decide
  rcases family_descends (prefixWord ++ tailWord_44949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44969 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_44969 : Nat := 118140960795 + 44969 * 2 ^ 59
def prefixEnd_44969 : Nat := 4983230072969 + 3 ^ 40 * 44969 * 2
def baseEnd_44969 : Nat := 23090711552139792280697

theorem tailTrace_44969 : CollatzResearch.WordTrace tailWord_44969 prefixEnd_44969 23090711552139792280697 := by
  unfold tailWord_44969
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640154174092467938865961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1093436116061645292577307 1640154174092467938865961)
  ·
    refine ⟨1230115630569350954149471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1640154174092467938865961 1230115630569350954149471)
    ·
      refine ⟨1845173445854026431224207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230115630569350954149471 1845173445854026431224207)
      ·
        refine ⟨2767760168781039646836311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845173445854026431224207 2767760168781039646836311)
        ·
          refine ⟨4151640253171559470254467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767760168781039646836311 4151640253171559470254467)
          ·
            refine ⟨6227460379757339205381701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4151640253171559470254467 6227460379757339205381701)
            ·
              refine ⟨1167648821204501101009069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6227460379757339205381701 1167648821204501101009069)
              ·
                refine ⟨437868307951687912878401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1167648821204501101009069 437868307951687912878401)
                ·
                  refine ⟨328401230963765934658801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437868307951687912878401 328401230963765934658801)
                  ·
                    refine ⟨246300923222824450994101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328401230963765934658801 246300923222824450994101)
                    ·
                      refine ⟨23090711552139792280697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 246300923222824450994101 23090711552139792280697)
                      ·
                        rfl

theorem cell23_44969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_44969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44969 prefixEnd_44969 := by exact prefixLift 44969
  have htrace : WordTrace (prefixWord ++ tailWord_44969) baseStart_44969 baseEnd_44969 := by
    simpa [prefixWord, tailWord_44969, baseEnd_44969] using wordTrace_append hprefix tailTrace_44969
  have hstable : (prefixWord ++ tailWord_44969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44969).length < 2 ^ (prefixWord ++ tailWord_44969).sum := by decide
  have hdescent : baseEnd_44969 < baseStart_44969 := by decide
  rcases family_descends (prefixWord ++ tailWord_44969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44990 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_44990 : Nat := 118140960795 + 44990 * 2 ^ 59
def prefixEnd_44990 : Nat := 4983230072969 + 3 ^ 40 * 44990 * 2
def baseEnd_44990 : Nat := 23101494645884210118101

theorem tailTrace_44990 : CollatzResearch.WordTrace tailWord_44990 prefixEnd_44990 23101494645884210118101 := by
  unfold tailWord_44990
  simp only [CollatzResearch.WordTrace]
  refine ⟨205115013377048565672553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1093946738010925683586949 205115013377048565672553)
  ·
    refine ⟨153836260032786424254415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205115013377048565672553 153836260032786424254415)
    ·
      refine ⟨230754390049179636381623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153836260032786424254415 230754390049179636381623)
      ·
        refine ⟨346131585073769454572435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230754390049179636381623 346131585073769454572435)
        ·
          refine ⟨519197377610654181858653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346131585073769454572435 519197377610654181858653)
          ·
            refine ⟨194699016603995318196995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 519197377610654181858653 194699016603995318196995)
            ·
              refine ⟨292048524905992977295493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194699016603995318196995 292048524905992977295493)
              ·
                refine ⟨54759098419873683242905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292048524905992977295493 54759098419873683242905)
                ·
                  refine ⟨41069323814905262432179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54759098419873683242905 41069323814905262432179)
                  ·
                    refine ⟨61603985722357893648269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41069323814905262432179 61603985722357893648269)
                    ·
                      refine ⟨23101494645884210118101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 61603985722357893648269 23101494645884210118101)
                      ·
                        rfl

theorem cell23_44990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_44990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_44990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_44990 prefixEnd_44990 := by exact prefixLift 44990
  have htrace : WordTrace (prefixWord ++ tailWord_44990) baseStart_44990 baseEnd_44990 := by
    simpa [prefixWord, tailWord_44990, baseEnd_44990] using wordTrace_append hprefix tailTrace_44990
  have hstable : (prefixWord ++ tailWord_44990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44990).length < 2 ^ (prefixWord ++ tailWord_44990).sum := by decide
  have hdescent : baseEnd_44990 < baseStart_44990 := by decide
  rcases family_descends (prefixWord ++ tailWord_44990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45006 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_45006 : Nat := 118140960795 + 45006 * 2 ^ 59
def prefixEnd_45006 : Nat := 4983230072969 + 3 ^ 40 * 45006 * 2
def baseEnd_45006 : Nat := 7703236778785382506009

theorem tailTrace_45006 : CollatzResearch.WordTrace tailWord_45006 prefixEnd_45006 7703236778785382506009 := by
  unfold tailWord_45006
  simp only [CollatzResearch.WordTrace]
  refine ⟨205187959369802907245359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1094335783305615505308581 205187959369802907245359)
  ·
    refine ⟨307781939054704360868039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205187959369802907245359 307781939054704360868039)
    ·
      refine ⟨461672908582056541302059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307781939054704360868039 461672908582056541302059)
      ·
        refine ⟨692509362873084811953089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461672908582056541302059 692509362873084811953089)
        ·
          refine ⟨519382022154813608964817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692509362873084811953089 519382022154813608964817)
          ·
            refine ⟨389536516616110206723613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519382022154813608964817 389536516616110206723613)
            ·
              refine ⟨146076193731041327521355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389536516616110206723613 146076193731041327521355)
              ·
                refine ⟨219114290596561991282033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146076193731041327521355 219114290596561991282033)
                ·
                  refine ⟨164335717947421493461525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219114290596561991282033 164335717947421493461525)
                  ·
                    refine ⟨7703236778785382506009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 164335717947421493461525 7703236778785382506009)
                    ·
                      rfl

theorem cell23_45006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_45006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45006 prefixEnd_45006 := by exact prefixLift 45006
  have htrace : WordTrace (prefixWord ++ tailWord_45006) baseStart_45006 baseEnd_45006 := by
    simpa [prefixWord, tailWord_45006, baseEnd_45006] using wordTrace_append hprefix tailTrace_45006
  have hstable : (prefixWord ++ tailWord_45006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45006).length < 2 ^ (prefixWord ++ tailWord_45006).sum := by decide
  have hdescent : baseEnd_45006 < baseStart_45006 := by decide
  rcases family_descends (prefixWord ++ tailWord_45006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45016 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 2, 4, 3]
def baseStart_45016 : Nat := 118140960795 + 45016 * 2 ^ 59
def prefixEnd_45016 : Nat := 4983230072969 + 3 ^ 40 * 45016 * 2
def baseEnd_45016 : Nat := 23114845142901108392981

theorem tailTrace_45016 : CollatzResearch.WordTrace tailWord_45016 prefixEnd_45016 23114845142901108392981 := by
  unfold tailWord_45016
  simp only [CollatzResearch.WordTrace]
  refine ⟨820934202461097482913451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1094578936614796643884601 820934202461097482913451)
  ·
    refine ⟨1231401303691646224370177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 820934202461097482913451 1231401303691646224370177)
    ·
      refine ⟨923550977768734668277633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1231401303691646224370177 923550977768734668277633)
      ·
        refine ⟨692663233326551001208225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 923550977768734668277633 692663233326551001208225)
        ·
          refine ⟨519497424994913250906169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692663233326551001208225 519497424994913250906169)
          ·
            refine ⟨389623068746184938179627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519497424994913250906169 389623068746184938179627)
            ·
              refine ⟨584434603119277407269441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389623068746184938179627 584434603119277407269441)
              ·
                refine ⟨438325952339458055452081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584434603119277407269441 438325952339458055452081)
                ·
                  refine ⟨328744464254593541589061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438325952339458055452081 328744464254593541589061)
                  ·
                    refine ⟨61639587047736289047949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 328744464254593541589061 61639587047736289047949)
                    ·
                      refine ⟨23114845142901108392981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 61639587047736289047949 23114845142901108392981)
                      ·
                        rfl

theorem cell23_45016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_45016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45016 prefixEnd_45016 := by exact prefixLift 45016
  have htrace : WordTrace (prefixWord ++ tailWord_45016) baseStart_45016 baseEnd_45016 := by
    simpa [prefixWord, tailWord_45016, baseEnd_45016] using wordTrace_append hprefix tailTrace_45016
  have hstable : (prefixWord ++ tailWord_45016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45016).length < 2 ^ (prefixWord ++ tailWord_45016).sum := by decide
  have hdescent : baseEnd_45016 < baseStart_45016 := by decide
  rcases family_descends (prefixWord ++ tailWord_45016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45053 : List Nat := [1, 4, 1, 1, 1, 2, 4, 4, 5]
def baseStart_45053 : Nat := 118140960795 + 45053 * 2 ^ 59
def prefixEnd_45053 : Nat := 4983230072969 + 3 ^ 40 * 45053 * 2
def baseEnd_45053 : Nat := 2570427103013051514479

theorem tailTrace_45053 : CollatzResearch.WordTrace tailWord_45053 prefixEnd_45053 2570427103013051514479 := by
  unfold tailWord_45053
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643217905788150284923813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1095478603858766856615875 1643217905788150284923813)
  ·
    refine ⟨308103357335278178423215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1643217905788150284923813 308103357335278178423215)
    ·
      refine ⟨462155036002917267634823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308103357335278178423215 462155036002917267634823)
      ·
        refine ⟨693232554004375901452235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462155036002917267634823 693232554004375901452235)
        ·
          refine ⟨1039848831006563852178353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693232554004375901452235 1039848831006563852178353)
          ·
            refine ⟨779886623254922889133765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1039848831006563852178353 779886623254922889133765)
            ·
              refine ⟨146228741860298041712581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 779886623254922889133765 146228741860298041712581)
              ·
                refine ⟨27417889098805882821109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146228741860298041712581 27417889098805882821109)
                ·
                  refine ⟨2570427103013051514479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27417889098805882821109 2570427103013051514479)
                  ·
                    rfl

theorem cell23_45053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_45053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45053 prefixEnd_45053 := by exact prefixLift 45053
  have htrace : WordTrace (prefixWord ++ tailWord_45053) baseStart_45053 baseEnd_45053 := by
    simpa [prefixWord, tailWord_45053, baseEnd_45053] using wordTrace_append hprefix tailTrace_45053
  have hstable : (prefixWord ++ tailWord_45053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45053).length < 2 ^ (prefixWord ++ tailWord_45053).sum := by decide
  have hdescent : baseEnd_45053 < baseStart_45053 := by decide
  rcases family_descends (prefixWord ++ tailWord_45053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45063 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_45063 : Nat := 118140960795 + 45063 * 2 ^ 59
def prefixEnd_45063 : Nat := 4983230072969 + 3 ^ 40 * 45063 * 2
def baseEnd_45063 : Nat := 23138978733662424505265

theorem tailTrace_45063 : CollatzResearch.WordTrace tailWord_45063 prefixEnd_45063 23138978733662424505265 := by
  unfold tailWord_45063
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643582635751921992787843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1095721757167947995191895 1643582635751921992787843)
  ·
    refine ⟨2465373953627882989181765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1643582635751921992787843 2465373953627882989181765)
    ·
      refine ⟨462257616305228060471581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2465373953627882989181765 462257616305228060471581)
      ·
        refine ⟨173346606114460522676843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 462257616305228060471581 173346606114460522676843)
        ·
          refine ⟨260019909171690784015265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173346606114460522676843 260019909171690784015265)
          ·
            refine ⟨195014931878768088011449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260019909171690784015265 195014931878768088011449)
            ·
              refine ⟨146261198909076066008587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195014931878768088011449 146261198909076066008587)
              ·
                refine ⟨219391798363614099012881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146261198909076066008587 219391798363614099012881)
                ·
                  refine ⟨164543848772710574259661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219391798363614099012881 164543848772710574259661)
                  ·
                    refine ⟨61703943289766465347373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164543848772710574259661 61703943289766465347373)
                    ·
                      refine ⟨23138978733662424505265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 61703943289766465347373 23138978733662424505265)
                      ·
                        rfl

theorem cell23_45063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_45063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45063 prefixEnd_45063 := by exact prefixLift 45063
  have htrace : WordTrace (prefixWord ++ tailWord_45063) baseStart_45063 baseEnd_45063 := by
    simpa [prefixWord, tailWord_45063, baseEnd_45063] using wordTrace_append hprefix tailTrace_45063
  have hstable : (prefixWord ++ tailWord_45063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45063).length < 2 ^ (prefixWord ++ tailWord_45063).sum := by decide
  have hdescent : baseEnd_45063 < baseStart_45063 := by decide
  rcases family_descends (prefixWord ++ tailWord_45063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45103 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 2, 4, 2]
def baseStart_45103 : Nat := 118140960795 + 45103 * 2 ^ 59
def prefixEnd_45103 : Nat := 4983230072969 + 3 ^ 40 * 45103 * 2
def baseEnd_45103 : Nat := 23159517959842268005081

theorem tailTrace_45103 : CollatzResearch.WordTrace tailWord_45103 prefixEnd_45103 23159517959842268005081 := by
  unfold tailWord_45103
  simp only [CollatzResearch.WordTrace]
  refine ⟨1645041555607008824243963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1096694370404672549495975 1645041555607008824243963)
  ·
    refine ⟨2467562333410513236365945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1645041555607008824243963 2467562333410513236365945)
    ·
      refine ⟨1850671750057884927274459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2467562333410513236365945 1850671750057884927274459)
      ·
        refine ⟨2776007625086827390911689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1850671750057884927274459 2776007625086827390911689)
        ·
          refine ⟨2082005718815120543183767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2776007625086827390911689 2082005718815120543183767)
          ·
            refine ⟨3123008578222680814775651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082005718815120543183767 3123008578222680814775651)
            ·
              refine ⟨4684512867334021222163477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123008578222680814775651 4684512867334021222163477)
              ·
                refine ⟨219586540656282244788913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4684512867334021222163477 219586540656282244788913)
                ·
                  refine ⟨164689905492211683591685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219586540656282244788913 164689905492211683591685)
                  ·
                    refine ⟨30879357279789690673441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164689905492211683591685 30879357279789690673441)
                    ·
                      refine ⟨23159517959842268005081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 30879357279789690673441 23159517959842268005081)
                      ·
                        rfl

theorem cell23_45103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 4, 2].length) (baseStart_45103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45103 prefixEnd_45103 := by exact prefixLift 45103
  have htrace : WordTrace (prefixWord ++ tailWord_45103) baseStart_45103 baseEnd_45103 := by
    simpa [prefixWord, tailWord_45103, baseEnd_45103] using wordTrace_append hprefix tailTrace_45103
  have hstable : (prefixWord ++ tailWord_45103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45103).length < 2 ^ (prefixWord ++ tailWord_45103).sum := by decide
  have hdescent : baseEnd_45103 < baseStart_45103 := by decide
  rcases family_descends (prefixWord ++ tailWord_45103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45164 : List Nat := [2, 2, 1, 1, 3, 5, 2, 2, 1, 4]
def baseStart_45164 : Nat := 118140960795 + 45164 * 2 ^ 59
def prefixEnd_45164 : Nat := 4983230072969 + 3 ^ 40 * 45164 * 2
def baseEnd_45164 : Nat := 7730280093255509780767

theorem tailTrace_45164 : CollatzResearch.WordTrace tailWord_45164 prefixEnd_45164 7730280093255509780767 := by
  unfold tailWord_45164
  simp only [CollatzResearch.WordTrace]
  refine ⟨823633204193008121107273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1098177605590677494809697 823633204193008121107273)
  ·
    refine ⟨617724903144756090830455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 823633204193008121107273 617724903144756090830455)
    ·
      refine ⟨926587354717134136245683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 617724903144756090830455 926587354717134136245683)
      ·
        refine ⟨1389881032075701204368525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926587354717134136245683 1389881032075701204368525)
        ·
          refine ⟨521205387028387951638197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1389881032075701204368525 521205387028387951638197)
          ·
            refine ⟨48863005033911370466081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 521205387028387951638197 48863005033911370466081)
            ·
              refine ⟨36647253775433527849561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48863005033911370466081 36647253775433527849561)
              ·
                refine ⟨27485440331575145887171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36647253775433527849561 27485440331575145887171)
                ·
                  refine ⟨41228160497362718830757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27485440331575145887171 41228160497362718830757)
                  ·
                    refine ⟨7730280093255509780767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41228160497362718830757 7730280093255509780767)
                    ·
                      rfl

theorem cell23_45164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_45164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45164 prefixEnd_45164 := by exact prefixLift 45164
  have htrace : WordTrace (prefixWord ++ tailWord_45164) baseStart_45164 baseEnd_45164 := by
    simpa [prefixWord, tailWord_45164, baseEnd_45164] using wordTrace_append hprefix tailTrace_45164
  have hstable : (prefixWord ++ tailWord_45164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45164).length < 2 ^ (prefixWord ++ tailWord_45164).sum := by decide
  have hdescent : baseEnd_45164 < baseStart_45164 := by decide
  rcases family_descends (prefixWord ++ tailWord_45164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45193 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 4]
def baseStart_45193 : Nat := 118140960795 + 45193 * 2 ^ 59
def prefixEnd_45193 : Nat := 4983230072969 + 3 ^ 40 * 45193 * 2
def baseEnd_45193 : Nat := 23205731218746915879667

theorem tailTrace_45193 : CollatzResearch.WordTrace tailWord_45193 prefixEnd_45193 23205731218746915879667 := by
  unfold tailWord_45193
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648324125280954195020233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1098882750187302796680155 1648324125280954195020233)
  ·
    refine ⟨1236243093960715646265175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1648324125280954195020233 1236243093960715646265175)
    ·
      refine ⟨1854364640941073469397763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236243093960715646265175 1854364640941073469397763)
      ·
        refine ⟨2781546961411610204096645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854364640941073469397763 2781546961411610204096645)
        ·
          refine ⟨521540055264676913268121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2781546961411610204096645 521540055264676913268121)
          ·
            refine ⟨391155041448507684951091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521540055264676913268121 391155041448507684951091)
            ·
              refine ⟨586732562172761527426637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391155041448507684951091 586732562172761527426637)
              ·
                refine ⟨220024710814785572784989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 586732562172761527426637 220024710814785572784989)
                ·
                  refine ⟨82509266555544589794371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220024710814785572784989 82509266555544589794371)
                  ·
                    refine ⟨123763899833316884691557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82509266555544589794371 123763899833316884691557)
                    ·
                      refine ⟨23205731218746915879667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 123763899833316884691557 23205731218746915879667)
                      ·
                        rfl

theorem cell23_45193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_45193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45193 prefixEnd_45193 := by exact prefixLift 45193
  have htrace : WordTrace (prefixWord ++ tailWord_45193) baseStart_45193 baseEnd_45193 := by
    simpa [prefixWord, tailWord_45193, baseEnd_45193] using wordTrace_append hprefix tailTrace_45193
  have hstable : (prefixWord ++ tailWord_45193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45193).length < 2 ^ (prefixWord ++ tailWord_45193).sum := by decide
  have hdescent : baseEnd_45193 < baseStart_45193 := by decide
  rcases family_descends (prefixWord ++ tailWord_45193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45203 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 4, 4]
def baseStart_45203 : Nat := 118140960795 + 45203 * 2 ^ 59
def prefixEnd_45203 : Nat := 4983230072969 + 3 ^ 40 * 45203 * 2
def baseEnd_45203 : Nat := 7736955341763958918207

theorem tailTrace_45203 : CollatzResearch.WordTrace tailWord_45203 prefixEnd_45203 7736955341763958918207 := by
  unfold tailWord_45203
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648688855244725902884263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1099125903496483935256175 1648688855244725902884263)
  ·
    refine ⟨2473033282867088854326395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1648688855244725902884263 2473033282867088854326395)
    ·
      refine ⟨3709549924300633281489593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2473033282867088854326395 3709549924300633281489593)
      ·
        refine ⟨2782162443225474961117195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3709549924300633281489593 2782162443225474961117195)
        ·
          refine ⟨4173243664838212441675793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782162443225474961117195 4173243664838212441675793)
          ·
            refine ⟨3129932748628659331256845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4173243664838212441675793 3129932748628659331256845)
            ·
              refine ⟨1173724780735747249221317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3129932748628659331256845 1173724780735747249221317)
              ·
                refine ⟨220073396387952609228997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1173724780735747249221317 220073396387952609228997)
                ·
                  refine ⟨41263761822741114230437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220073396387952609228997 41263761822741114230437)
                  ·
                    refine ⟨7736955341763958918207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41263761822741114230437 7736955341763958918207)
                    ·
                      rfl

theorem cell23_45203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 4].length) (baseStart_45203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45203 prefixEnd_45203 := by exact prefixLift 45203
  have htrace : WordTrace (prefixWord ++ tailWord_45203) baseStart_45203 baseEnd_45203 := by
    simpa [prefixWord, tailWord_45203, baseEnd_45203] using wordTrace_append hprefix tailTrace_45203
  have hstable : (prefixWord ++ tailWord_45203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45203).length < 2 ^ (prefixWord ++ tailWord_45203).sum := by decide
  have hdescent : baseEnd_45203 < baseStart_45203 := by decide
  rcases family_descends (prefixWord ++ tailWord_45203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45317 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 4, 2, 2]
def baseStart_45317 : Nat := 118140960795 + 45317 * 2 ^ 59
def prefixEnd_45317 : Nat := 4983230072969 + 3 ^ 40 * 45317 * 2
def baseEnd_45317 : Nat := 23269402819904430729097

theorem tailTrace_45317 : CollatzResearch.WordTrace tailWord_45317 prefixEnd_45317 23269402819904430729097 := by
  unfold tailWord_45317
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652846776831723372534205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1101897851221148915022803 1652846776831723372534205)
  ·
    refine ⟨619817541311896264700327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1652846776831723372534205 619817541311896264700327)
    ·
      refine ⟨929726311967844397050491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 619817541311896264700327 929726311967844397050491)
      ·
        refine ⟨1394589467951766595575737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929726311967844397050491 1394589467951766595575737)
        ·
          refine ⟨1045942100963824946681803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1394589467951766595575737 1045942100963824946681803)
          ·
            refine ⟨1568913151445737420022705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045942100963824946681803 1568913151445737420022705)
            ·
              refine ⟨1176684863584303065017029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1568913151445737420022705 1176684863584303065017029)
              ·
                refine ⟨220628411922056824690693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1176684863584303065017029 220628411922056824690693)
                ·
                  refine ⟨41367827235385654629505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220628411922056824690693 41367827235385654629505)
                  ·
                    refine ⟨31025870426539240972129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41367827235385654629505 31025870426539240972129)
                    ·
                      refine ⟨23269402819904430729097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31025870426539240972129 23269402819904430729097)
                      ·
                        rfl

theorem cell23_45317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_45317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45317 prefixEnd_45317 := by exact prefixLift 45317
  have htrace : WordTrace (prefixWord ++ tailWord_45317) baseStart_45317 baseEnd_45317 := by
    simpa [prefixWord, tailWord_45317, baseEnd_45317] using wordTrace_append hprefix tailTrace_45317
  have hstable : (prefixWord ++ tailWord_45317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45317).length < 2 ^ (prefixWord ++ tailWord_45317).sum := by decide
  have hdescent : baseEnd_45317 < baseStart_45317 := by decide
  rcases family_descends (prefixWord ++ tailWord_45317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45320 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_45320 : Nat := 118140960795 + 45320 * 2 ^ 59
def prefixEnd_45320 : Nat := 4983230072969 + 3 ^ 40 * 45320 * 2
def baseEnd_45320 : Nat := 23270943261867918991583

theorem tailTrace_45320 : CollatzResearch.WordTrace tailWord_45320 prefixEnd_45320 23270943261867918991583 := by
  unfold tailWord_45320
  simp only [CollatzResearch.WordTrace]
  refine ⟨826478097910427442446707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1101970797213903256595609 826478097910427442446707)
  ·
    refine ⟨1239717146865641163670061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 826478097910427442446707 1239717146865641163670061)
    ·
      refine ⟨464893930074615436376273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1239717146865641163670061 464893930074615436376273)
      ·
        refine ⟨348670447555961577282205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464893930074615436376273 348670447555961577282205)
        ·
          refine ⟨130751417833485591480827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348670447555961577282205 130751417833485591480827)
          ·
            refine ⟨196127126750228387221241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130751417833485591480827 196127126750228387221241)
            ·
              refine ⟨147095345062671290415931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196127126750228387221241 147095345062671290415931)
              ·
                refine ⟨220643017594006935623897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147095345062671290415931 220643017594006935623897)
                ·
                  refine ⟨165482263195505201717923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220643017594006935623897 165482263195505201717923)
                  ·
                    refine ⟨248223394793257802576885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165482263195505201717923 248223394793257802576885)
                    ·
                      refine ⟨23270943261867918991583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 248223394793257802576885 23270943261867918991583)
                      ·
                        rfl

theorem cell23_45320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_45320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45320 prefixEnd_45320 := by exact prefixLift 45320
  have htrace : WordTrace (prefixWord ++ tailWord_45320) baseStart_45320 baseEnd_45320 := by
    simpa [prefixWord, tailWord_45320, baseEnd_45320] using wordTrace_append hprefix tailTrace_45320
  have hstable : (prefixWord ++ tailWord_45320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45320).length < 2 ^ (prefixWord ++ tailWord_45320).sum := by decide
  have hdescent : baseEnd_45320 < baseStart_45320 := by decide
  rcases family_descends (prefixWord ++ tailWord_45320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45333 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_45333 : Nat := 118140960795 + 45333 * 2 ^ 59
def prefixEnd_45333 : Nat := 4983230072969 + 3 ^ 40 * 45333 * 2
def baseEnd_45333 : Nat := 23277618510376368129023

theorem tailTrace_45333 : CollatzResearch.WordTrace tailWord_45333 prefixEnd_45333 23277618510376368129023 := by
  unfold tailWord_45333
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653430344773758105116653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1102286896515838736744435 1653430344773758105116653)
  ·
    refine ⟨620036379290159289418745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1653430344773758105116653 620036379290159289418745)
    ·
      refine ⟨465027284467619467064059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 620036379290159289418745 465027284467619467064059)
      ·
        refine ⟨697540926701429200596089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465027284467619467064059 697540926701429200596089)
        ·
          refine ⟨523155695026071900447067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697540926701429200596089 523155695026071900447067)
          ·
            refine ⟨784733542539107850670601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523155695026071900447067 784733542539107850670601)
            ·
              refine ⟨588550156904330888002951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784733542539107850670601 588550156904330888002951)
              ·
                refine ⟨882825235356496332004427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588550156904330888002951 882825235356496332004427)
                ·
                  refine ⟨1324237853034744498006641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882825235356496332004427 1324237853034744498006641)
                  ·
                    refine ⟨993178389776058373504981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1324237853034744498006641 993178389776058373504981)
                    ·
                      refine ⟨23277618510376368129023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 993178389776058373504981 23277618510376368129023)
                      ·
                        rfl

theorem cell23_45333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_45333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45333 prefixEnd_45333 := by exact prefixLift 45333
  have htrace : WordTrace (prefixWord ++ tailWord_45333) baseStart_45333 baseEnd_45333 := by
    simpa [prefixWord, tailWord_45333, baseEnd_45333] using wordTrace_append hprefix tailTrace_45333
  have hstable : (prefixWord ++ tailWord_45333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45333).length < 2 ^ (prefixWord ++ tailWord_45333).sum := by decide
  have hdescent : baseEnd_45333 < baseStart_45333 := by decide
  rcases family_descends (prefixWord ++ tailWord_45333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45370 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_45370 : Nat := 118140960795 + 45370 * 2 ^ 59
def prefixEnd_45370 : Nat := 4983230072969 + 3 ^ 40 * 45370 * 2
def baseEnd_45370 : Nat := 7765539098197574455451

theorem tailTrace_45370 : CollatzResearch.WordTrace tailWord_45370 prefixEnd_45370 7765539098197574455451 := by
  unfold tailWord_45370
  simp only [CollatzResearch.WordTrace]
  refine ⟨413694961409928356053391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1103186563759808949475709 413694961409928356053391)
  ·
    refine ⟨620542442114892534080087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 413694961409928356053391 620542442114892534080087)
    ·
      refine ⟨930813663172338801120131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620542442114892534080087 930813663172338801120131)
      ·
        refine ⟨1396220494758508201680197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930813663172338801120131 1396220494758508201680197)
        ·
          refine ⟨261791342767220287815037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1396220494758508201680197 261791342767220287815037)
          ·
            refine ⟨98171753537707607930639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261791342767220287815037 98171753537707607930639)
            ·
              refine ⟨147257630306561411895959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98171753537707607930639 147257630306561411895959)
              ·
                refine ⟨220886445459842117843939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147257630306561411895959 220886445459842117843939)
                ·
                  refine ⟨331329668189763176765909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220886445459842117843939 331329668189763176765909)
                  ·
                    refine ⟨7765539098197574455451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 331329668189763176765909 7765539098197574455451)
                    ·
                      rfl

theorem cell23_45370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_45370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45370 prefixEnd_45370 := by exact prefixLift 45370
  have htrace : WordTrace (prefixWord ++ tailWord_45370) baseStart_45370 baseEnd_45370 := by
    simpa [prefixWord, tailWord_45370, baseEnd_45370] using wordTrace_append hprefix tailTrace_45370
  have hstable : (prefixWord ++ tailWord_45370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45370).length < 2 ^ (prefixWord ++ tailWord_45370).sum := by decide
  have hdescent : baseEnd_45370 < baseStart_45370 := by decide
  rcases family_descends (prefixWord ++ tailWord_45370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45374 : List Nat := [4, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_45374 : Nat := 118140960795 + 45374 * 2 ^ 59
def prefixEnd_45374 : Nat := 4983230072969 + 3 ^ 40 * 45374 * 2
def baseEnd_45374 : Nat := 2588741246356745301815

theorem tailTrace_45374 : CollatzResearch.WordTrace tailWord_45374 prefixEnd_45374 2588741246356745301815 := by
  unfold tailWord_45374
  simp only [CollatzResearch.WordTrace]
  refine ⟨206865717203152763419897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1103283825083481404906117 206865717203152763419897)
  ·
    refine ⟨155149287902364572564923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206865717203152763419897 155149287902364572564923)
    ·
      refine ⟨232723931853546858847385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155149287902364572564923 232723931853546858847385)
      ·
        refine ⟨174542948890160144135539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232723931853546858847385 174542948890160144135539)
        ·
          refine ⟨261814423335240216203309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174542948890160144135539 261814423335240216203309)
          ·
            refine ⟨98180408750715081076241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261814423335240216203309 98180408750715081076241)
            ·
              refine ⟨73635306563036310807181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98180408750715081076241 73635306563036310807181)
              ·
                refine ⟨27613239961138616552693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73635306563036310807181 27613239961138616552693)
                ·
                  refine ⟨2588741246356745301815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27613239961138616552693 2588741246356745301815)
                  ·
                    rfl

theorem cell23_45374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_45374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45374 prefixEnd_45374 := by exact prefixLift 45374
  have htrace : WordTrace (prefixWord ++ tailWord_45374) baseStart_45374 baseEnd_45374 := by
    simpa [prefixWord, tailWord_45374, baseEnd_45374] using wordTrace_append hprefix tailTrace_45374
  have hstable : (prefixWord ++ tailWord_45374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45374).length < 2 ^ (prefixWord ++ tailWord_45374).sum := by decide
  have hdescent : baseEnd_45374 < baseStart_45374 := by decide
  rcases family_descends (prefixWord ++ tailWord_45374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45403 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 6]
def baseStart_45403 : Nat := 118140960795 + 45403 * 2 ^ 59
def prefixEnd_45403 : Nat := 4983230072969 + 3 ^ 40 * 45403 * 2
def baseEnd_45403 : Nat := 23313562156191094253701

theorem tailTrace_45403 : CollatzResearch.WordTrace tailWord_45403 prefixEnd_45403 23313562156191094253701 := by
  unfold tailWord_45403
  simp only [CollatzResearch.WordTrace]
  refine ⟨1655983454520160060164863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1103988969680106706776575 1655983454520160060164863)
  ·
    refine ⟨2483975181780240090247295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1655983454520160060164863 2483975181780240090247295)
    ·
      refine ⟨3725962772670360135370943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483975181780240090247295 3725962772670360135370943)
      ·
        refine ⟨5588944159005540203056415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725962772670360135370943 5588944159005540203056415)
        ·
          refine ⟨8383416238508310304584623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5588944159005540203056415 8383416238508310304584623)
          ·
            refine ⟨12575124357762465456876935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8383416238508310304584623 12575124357762465456876935)
            ·
              refine ⟨18862686536643698185315403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12575124357762465456876935 18862686536643698185315403)
              ·
                refine ⟨28294029804965547277973105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18862686536643698185315403 28294029804965547277973105)
                ·
                  refine ⟨21220522353724160458479829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28294029804965547277973105 21220522353724160458479829)
                  ·
                    refine ⟨497355992665410010745621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21220522353724160458479829 497355992665410010745621)
                    ·
                      refine ⟨23313562156191094253701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 497355992665410010745621 23313562156191094253701)
                      ·
                        rfl

theorem cell23_45403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_45403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45403 prefixEnd_45403 := by exact prefixLift 45403
  have htrace : WordTrace (prefixWord ++ tailWord_45403) baseStart_45403 baseEnd_45403 := by
    simpa [prefixWord, tailWord_45403, baseEnd_45403] using wordTrace_append hprefix tailTrace_45403
  have hstable : (prefixWord ++ tailWord_45403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45403).length < 2 ^ (prefixWord ++ tailWord_45403).sum := by decide
  have hdescent : baseEnd_45403 < baseStart_45403 := by decide
  rcases family_descends (prefixWord ++ tailWord_45403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45407 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 2, 4, 2]
def baseStart_45407 : Nat := 118140960795 + 45407 * 2 ^ 59
def prefixEnd_45407 : Nat := 4983230072969 + 3 ^ 40 * 45407 * 2
def baseEnd_45407 : Nat := 23315616078809078603683

theorem tailTrace_45407 : CollatzResearch.WordTrace tailWord_45407 prefixEnd_45407 23315616078809078603683 := by
  unfold tailWord_45407
  simp only [CollatzResearch.WordTrace]
  refine ⟨1656129346505668743310475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1104086231003779162206983 1656129346505668743310475)
  ·
    refine ⟨2484194019758503114965713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1656129346505668743310475 2484194019758503114965713)
    ·
      refine ⟨1863145514818877336224285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2484194019758503114965713 1863145514818877336224285)
      ·
        refine ⟨698679568057079001084107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1863145514818877336224285 698679568057079001084107)
        ·
          refine ⟨1048019352085618501626161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698679568057079001084107 1048019352085618501626161)
          ·
            refine ⟨786014514064213876219621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048019352085618501626161 786014514064213876219621)
            ·
              refine ⟨147377721387040101791179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 786014514064213876219621 147377721387040101791179)
              ·
                refine ⟨221066582080560152686769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147377721387040101791179 221066582080560152686769)
                ·
                  refine ⟨165799936560420114515077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221066582080560152686769 165799936560420114515077)
                  ·
                    refine ⟨31087488105078771471577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165799936560420114515077 31087488105078771471577)
                    ·
                      refine ⟨23315616078809078603683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31087488105078771471577 23315616078809078603683)
                      ·
                        rfl

theorem cell23_45407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_45407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45407 prefixEnd_45407 := by exact prefixLift 45407
  have htrace : WordTrace (prefixWord ++ tailWord_45407) baseStart_45407 baseEnd_45407 := by
    simpa [prefixWord, tailWord_45407, baseEnd_45407] using wordTrace_append hprefix tailTrace_45407
  have hstable : (prefixWord ++ tailWord_45407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45407).length < 2 ^ (prefixWord ++ tailWord_45407).sum := by decide
  have hdescent : baseEnd_45407 < baseStart_45407 := by decide
  rcases family_descends (prefixWord ++ tailWord_45407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45451 : List Nat := [1, 1, 1, 1, 4, 5, 3, 2, 1, 4]
def baseStart_45451 : Nat := 118140960795 + 45451 * 2 ^ 59
def prefixEnd_45451 : Nat := 4983230072969 + 3 ^ 40 * 45451 * 2
def baseEnd_45451 : Nat := 7779403075868968817827

theorem tailTrace_45451 : CollatzResearch.WordTrace tailWord_45451 prefixEnd_45451 7779403075868968817827 := by
  unfold tailWord_45451
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657734158346264257912207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1105156105564176171941471 1657734158346264257912207)
  ·
    refine ⟨2486601237519396386868311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1657734158346264257912207 2486601237519396386868311)
    ·
      refine ⟨3729901856279094580302467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2486601237519396386868311 3729901856279094580302467)
      ·
        refine ⟨5594852784418641870453701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3729901856279094580302467 5594852784418641870453701)
        ·
          refine ⟨1049034897078495350710069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5594852784418641870453701 1049034897078495350710069)
          ·
            refine ⟨98347021601108939129069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1049034897078495350710069 98347021601108939129069)
            ·
              refine ⟨36880133100415852173401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98347021601108939129069 36880133100415852173401)
              ·
                refine ⟨27660099825311889130051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36880133100415852173401 27660099825311889130051)
                ·
                  refine ⟨41490149737967833695077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27660099825311889130051 41490149737967833695077)
                  ·
                    refine ⟨7779403075868968817827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41490149737967833695077 7779403075868968817827)
                    ·
                      rfl

theorem cell23_45451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 1, 4].length) (baseStart_45451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45451 prefixEnd_45451 := by exact prefixLift 45451
  have htrace : WordTrace (prefixWord ++ tailWord_45451) baseStart_45451 baseEnd_45451 := by
    simpa [prefixWord, tailWord_45451, baseEnd_45451] using wordTrace_append hprefix tailTrace_45451
  have hstable : (prefixWord ++ tailWord_45451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45451).length < 2 ^ (prefixWord ++ tailWord_45451).sum := by decide
  have hdescent : baseEnd_45451 < baseStart_45451 := by decide
  rcases family_descends (prefixWord ++ tailWord_45451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45464 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 6]
def baseStart_45464 : Nat := 118140960795 + 45464 * 2 ^ 59
def prefixEnd_45464 : Nat := 4983230072969 + 3 ^ 40 * 45464 * 2
def baseEnd_45464 : Nat := 2593876052901706176769

theorem tailTrace_45464 : CollatzResearch.WordTrace tailWord_45464 prefixEnd_45464 2593876052901706176769 := by
  unfold tailWord_45464
  simp only [CollatzResearch.WordTrace]
  refine ⟨829104153649583739067723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1105472204866111652090297 829104153649583739067723)
  ·
    refine ⟨1243656230474375608601585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 829104153649583739067723 1243656230474375608601585)
    ·
      refine ⟨932742172855781706451189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1243656230474375608601585 932742172855781706451189)
      ·
        refine ⟨87444578705229534979799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 932742172855781706451189 87444578705229534979799)
        ·
          refine ⟨131166868057844302469699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87444578705229534979799 131166868057844302469699)
          ·
            refine ⟨196750302086766453704549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131166868057844302469699 196750302086766453704549)
            ·
              refine ⟨36890681641268710069603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196750302086766453704549 36890681641268710069603)
              ·
                refine ⟨55336022461903065104405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36890681641268710069603 55336022461903065104405)
                ·
                  refine ⟨2593876052901706176769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55336022461903065104405 2593876052901706176769)
                  ·
                    rfl

theorem cell23_45464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 6].length) (baseStart_45464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45464 prefixEnd_45464 := by exact prefixLift 45464
  have htrace : WordTrace (prefixWord ++ tailWord_45464) baseStart_45464 baseEnd_45464 := by
    simpa [prefixWord, tailWord_45464, baseEnd_45464] using wordTrace_append hprefix tailTrace_45464
  have hstable : (prefixWord ++ tailWord_45464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45464).length < 2 ^ (prefixWord ++ tailWord_45464).sum := by decide
  have hdescent : baseEnd_45464 < baseStart_45464 := by decide
  rcases family_descends (prefixWord ++ tailWord_45464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45474 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_45474 : Nat := 118140960795 + 45474 * 2 ^ 59
def prefixEnd_45474 : Nat := 4983230072969 + 3 ^ 40 * 45474 * 2
def baseEnd_45474 : Nat := 23350019282660316465875

theorem tailTrace_45474 : CollatzResearch.WordTrace tailWord_45474 prefixEnd_45474 23350019282660316465875 := by
  unfold tailWord_45474
  simp only [CollatzResearch.WordTrace]
  refine ⟨414643259315734796499869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1105715358175292790666317 414643259315734796499869)
  ·
    refine ⟨155491222243400548687451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 414643259315734796499869 155491222243400548687451)
    ·
      refine ⟨233236833365100823031177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155491222243400548687451 233236833365100823031177)
      ·
        refine ⟨174927625023825617273383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233236833365100823031177 174927625023825617273383)
        ·
          refine ⟨262391437535738425910075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174927625023825617273383 262391437535738425910075)
          ·
            refine ⟨393587156303607638865113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262391437535738425910075 393587156303607638865113)
            ·
              refine ⟨295190367227705729148835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393587156303607638865113 295190367227705729148835)
              ·
                refine ⟨442785550841558593723253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295190367227705729148835 442785550841558593723253)
                ·
                  refine ⟨41511145391396118161555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 442785550841558593723253 41511145391396118161555)
                  ·
                    refine ⟨62266718087094177242333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41511145391396118161555 62266718087094177242333)
                    ·
                      refine ⟨23350019282660316465875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 62266718087094177242333 23350019282660316465875)
                      ·
                        rfl

theorem cell23_45474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_45474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45474 prefixEnd_45474 := by exact prefixLift 45474
  have htrace : WordTrace (prefixWord ++ tailWord_45474) baseStart_45474 baseEnd_45474 := by
    simpa [prefixWord, tailWord_45474, baseEnd_45474] using wordTrace_append hprefix tailTrace_45474
  have hstable : (prefixWord ++ tailWord_45474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45474).length < 2 ^ (prefixWord ++ tailWord_45474).sum := by decide
  have hdescent : baseEnd_45474 < baseStart_45474 := by decide
  rcases family_descends (prefixWord ++ tailWord_45474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45524 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_45524 : Nat := 118140960795 + 45524 * 2 ^ 59
def prefixEnd_45524 : Nat := 4983230072969 + 3 ^ 40 * 45524 * 2
def baseEnd_45524 : Nat := 7791897771795040280215

theorem tailTrace_45524 : CollatzResearch.WordTrace tailWord_45524 prefixEnd_45524 7791897771795040280215 := by
  unfold tailWord_45524
  simp only [CollatzResearch.WordTrace]
  refine ⟨830198343540898862659813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1106931124721198483546417 830198343540898862659813)
  ·
    refine ⟨155662189413918536748715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 830198343540898862659813 155662189413918536748715)
    ·
      refine ⟨233493284120877805123073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155662189413918536748715 233493284120877805123073)
      ·
        refine ⟨175119963090658353842305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233493284120877805123073 175119963090658353842305)
        ·
          refine ⟨131339972317993765381729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175119963090658353842305 131339972317993765381729)
          ·
            refine ⟨98504979238495324036297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131339972317993765381729 98504979238495324036297)
            ·
              refine ⟨73878734428871493027223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98504979238495324036297 73878734428871493027223)
              ·
                refine ⟨110818101643307239540835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73878734428871493027223 110818101643307239540835)
                ·
                  refine ⟨166227152464960859311253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110818101643307239540835 166227152464960859311253)
                  ·
                    refine ⟨7791897771795040280215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 166227152464960859311253 7791897771795040280215)
                    ·
                      rfl

theorem cell23_45524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_45524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45524 prefixEnd_45524 := by exact prefixLift 45524
  have htrace : WordTrace (prefixWord ++ tailWord_45524) baseStart_45524 baseEnd_45524 := by
    simpa [prefixWord, tailWord_45524, baseEnd_45524] using wordTrace_append hprefix tailTrace_45524
  have hstable : (prefixWord ++ tailWord_45524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45524).length < 2 ^ (prefixWord ++ tailWord_45524).sum := by decide
  have hdescent : baseEnd_45524 < baseStart_45524 := by decide
  rcases family_descends (prefixWord ++ tailWord_45524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45537 : List Nat := [1, 2, 3, 1, 2, 2, 5, 7]
def baseStart_45537 : Nat := 118140960795 + 45537 * 2 ^ 59
def prefixEnd_45537 : Nat := 4983230072969 + 3 ^ 40 * 45537 * 2
def baseEnd_45537 : Nat := 866013650514576665855

theorem tailTrace_45537 : CollatzResearch.WordTrace tailWord_45537 prefixEnd_45537 866013650514576665855 := by
  unfold tailWord_45537
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660870836034700945542865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1107247224023133963695243 1660870836034700945542865)
  ·
    refine ⟨1245653127026025709157149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1660870836034700945542865 1245653127026025709157149)
    ·
      refine ⟨467119922634759640933931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1245653127026025709157149 467119922634759640933931)
      ·
        refine ⟨700679883952139461400897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467119922634759640933931 700679883952139461400897)
        ·
          refine ⟨525509912964104596050673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 700679883952139461400897 525509912964104596050673)
          ·
            refine ⟨394132434723078447038005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525509912964104596050673 394132434723078447038005)
            ·
              refine ⟨36949915755288604409813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 394132434723078447038005 36949915755288604409813)
              ·
                refine ⟨866013650514576665855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36949915755288604409813 866013650514576665855)
                ·
                  rfl

theorem cell23_45537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 7].length) (baseStart_45537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45537 prefixEnd_45537 := by exact prefixLift 45537
  have htrace : WordTrace (prefixWord ++ tailWord_45537) baseStart_45537 baseEnd_45537 := by
    simpa [prefixWord, tailWord_45537, baseEnd_45537] using wordTrace_append hprefix tailTrace_45537
  have hstable : (prefixWord ++ tailWord_45537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45537).length < 2 ^ (prefixWord ++ tailWord_45537).sum := by decide
  have hdescent : baseEnd_45537 < baseStart_45537 := by decide
  rcases family_descends (prefixWord ++ tailWord_45537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45547 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 3]
def baseStart_45547 : Nat := 118140960795 + 45547 * 2 ^ 59
def prefixEnd_45547 : Nat := 4983230072969 + 3 ^ 40 * 45547 * 2
def baseEnd_45547 : Nat := 23387503370438530853039

theorem tailTrace_45547 : CollatzResearch.WordTrace tailWord_45547 prefixEnd_45547 23387503370438530853039 := by
  unfold tailWord_45547
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661235565998472653406895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1107490377332315102271263 1661235565998472653406895)
  ·
    refine ⟨2491853348997708980110343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1661235565998472653406895 2491853348997708980110343)
    ·
      refine ⟨3737780023496563470165515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491853348997708980110343 3737780023496563470165515)
      ·
        refine ⟨5606670035244845205248273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3737780023496563470165515 5606670035244845205248273)
        ·
          refine ⟨4205002526433633903936205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5606670035244845205248273 4205002526433633903936205)
          ·
            refine ⟨1576875947412612713976077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4205002526433633903936205 1576875947412612713976077)
            ·
              refine ⟨591328480279729767741029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1576875947412612713976077 591328480279729767741029)
              ·
                refine ⟨110874090052449331451443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591328480279729767741029 110874090052449331451443)
                ·
                  refine ⟨166311135078673997177165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110874090052449331451443 166311135078673997177165)
                  ·
                    refine ⟨62366675654502748941437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166311135078673997177165 62366675654502748941437)
                    ·
                      refine ⟨23387503370438530853039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 62366675654502748941437 23387503370438530853039)
                      ·
                        rfl

theorem cell23_45547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 3].length) (baseStart_45547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45547 prefixEnd_45547 := by exact prefixLift 45547
  have htrace : WordTrace (prefixWord ++ tailWord_45547) baseStart_45547 baseEnd_45547 := by
    simpa [prefixWord, tailWord_45547, baseEnd_45547] using wordTrace_append hprefix tailTrace_45547
  have hstable : (prefixWord ++ tailWord_45547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45547).length < 2 ^ (prefixWord ++ tailWord_45547).sum := by decide
  have hdescent : baseEnd_45547 < baseStart_45547 := by decide
  rcases family_descends (prefixWord ++ tailWord_45547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45548 : List Nat := [2, 2, 1, 1, 2, 1, 6, 3, 1, 2, 2]
def baseStart_45548 : Nat := 118140960795 + 45548 * 2 ^ 59
def prefixEnd_45548 : Nat := 4983230072969 + 3 ^ 40 * 45548 * 2
def baseEnd_45548 : Nat := 23388016851093026940535

theorem tailTrace_45548 : CollatzResearch.WordTrace tailWord_45548 prefixEnd_45548 23388016851093026940535 := by
  unfold tailWord_45548
  simp only [CollatzResearch.WordTrace]
  refine ⟨830636019497424912096649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1107514692663233216128865 830636019497424912096649)
  ·
    refine ⟨622977014623068684072487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 830636019497424912096649 622977014623068684072487)
    ·
      refine ⟨934465521934603026108731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622977014623068684072487 934465521934603026108731)
      ·
        refine ⟨1401698282901904539163097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934465521934603026108731 1401698282901904539163097)
        ·
          refine ⟨1051273712176428404372323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1401698282901904539163097 1051273712176428404372323)
          ·
            refine ⟨1576910568264642606558485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051273712176428404372323 1576910568264642606558485)
            ·
              refine ⟨73917682887405122182429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1576910568264642606558485 73917682887405122182429)
              ·
                refine ⟨27719131082776920818411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73917682887405122182429 27719131082776920818411)
                ·
                  refine ⟨41578696624165381227617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27719131082776920818411 41578696624165381227617)
                  ·
                    refine ⟨31184022468124035920713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41578696624165381227617 31184022468124035920713)
                    ·
                      refine ⟨23388016851093026940535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31184022468124035920713 23388016851093026940535)
                      ·
                        rfl

theorem cell23_45548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 1, 2, 2].length) (baseStart_45548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45548 prefixEnd_45548 := by exact prefixLift 45548
  have htrace : WordTrace (prefixWord ++ tailWord_45548) baseStart_45548 baseEnd_45548 := by
    simpa [prefixWord, tailWord_45548, baseEnd_45548] using wordTrace_append hprefix tailTrace_45548
  have hstable : (prefixWord ++ tailWord_45548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45548).length < 2 ^ (prefixWord ++ tailWord_45548).sum := by decide
  have hdescent : baseEnd_45548 < baseStart_45548 := by decide
  rcases family_descends (prefixWord ++ tailWord_45548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45608 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_45608 : Nat := 118140960795 + 45608 * 2 ^ 59
def prefixEnd_45608 : Nat := 4983230072969 + 3 ^ 40 * 45608 * 2
def baseEnd_45608 : Nat := 23418825690362792190259

theorem tailTrace_45608 : CollatzResearch.WordTrace tailWord_45608 prefixEnd_45608 23418825690362792190259 := by
  unfold tailWord_45608
  simp only [CollatzResearch.WordTrace]
  refine ⟨831730209388740035688739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1108973612518320047584985 831730209388740035688739)
  ·
    refine ⟨1247595314083110053533109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 831730209388740035688739 1247595314083110053533109)
    ·
      refine ⟨116962060695291567518729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1247595314083110053533109 116962060695291567518729)
      ·
        refine ⟨87721545521468675639047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116962060695291567518729 87721545521468675639047)
        ·
          refine ⟨131582318282203013458571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87721545521468675639047 131582318282203013458571)
          ·
            refine ⟨197373477423304520187857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131582318282203013458571 197373477423304520187857)
            ·
              refine ⟨148030108067478390140893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197373477423304520187857 148030108067478390140893)
              ·
                refine ⟨55511290525304396302835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148030108067478390140893 55511290525304396302835)
                ·
                  refine ⟨83266935787956594454253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55511290525304396302835 83266935787956594454253)
                  ·
                    refine ⟨31225100920483722920345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83266935787956594454253 31225100920483722920345)
                    ·
                      refine ⟨23418825690362792190259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31225100920483722920345 23418825690362792190259)
                      ·
                        rfl

theorem cell23_45608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_45608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45608 prefixEnd_45608 := by exact prefixLift 45608
  have htrace : WordTrace (prefixWord ++ tailWord_45608) baseStart_45608 baseEnd_45608 := by
    simpa [prefixWord, tailWord_45608, baseEnd_45608] using wordTrace_append hprefix tailTrace_45608
  have hstable : (prefixWord ++ tailWord_45608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45608).length < 2 ^ (prefixWord ++ tailWord_45608).sum := by decide
  have hdescent : baseEnd_45608 < baseStart_45608 := by decide
  rcases family_descends (prefixWord ++ tailWord_45608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45617 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_45617 : Nat := 118140960795 + 45617 * 2 ^ 59
def prefixEnd_45617 : Nat := 4983230072969 + 3 ^ 40 * 45617 * 2
def baseEnd_45617 : Nat := 23423447016253256977717

theorem tailTrace_45617 : CollatzResearch.WordTrace tailWord_45617 prefixEnd_45617 23423447016253256977717 := by
  unfold tailWord_45617
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663788675744874608455105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1109192450496583072303403 1663788675744874608455105)
  ·
    refine ⟨1247841506808655956341329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1663788675744874608455105 1247841506808655956341329)
    ·
      refine ⟨935881130106491967255997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1247841506808655956341329 935881130106491967255997)
      ·
        refine ⟨350955423789934487720999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 935881130106491967255997 350955423789934487720999)
        ·
          refine ⟨526433135684901731581499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350955423789934487720999 526433135684901731581499)
          ·
            refine ⟨789649703527352597372249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526433135684901731581499 789649703527352597372249)
            ·
              refine ⟨592237277645514448029187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789649703527352597372249 592237277645514448029187)
              ·
                refine ⟨888355916468271672043781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592237277645514448029187 888355916468271672043781)
                ·
                  refine ⟨166566734337800938508209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 888355916468271672043781 166566734337800938508209)
                  ·
                    refine ⟨124925050753350703881157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166566734337800938508209 124925050753350703881157)
                    ·
                      refine ⟨23423447016253256977717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 124925050753350703881157 23423447016253256977717)
                      ·
                        rfl

theorem cell23_45617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_45617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45617 prefixEnd_45617 := by exact prefixLift 45617
  have htrace : WordTrace (prefixWord ++ tailWord_45617) baseStart_45617 baseEnd_45617 := by
    simpa [prefixWord, tailWord_45617, baseEnd_45617] using wordTrace_append hprefix tailTrace_45617
  have hstable : (prefixWord ++ tailWord_45617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45617).length < 2 ^ (prefixWord ++ tailWord_45617).sum := by decide
  have hdescent : baseEnd_45617 < baseStart_45617 := by decide
  rcases family_descends (prefixWord ++ tailWord_45617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45621 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_45621 : Nat := 118140960795 + 45621 * 2 ^ 59
def prefixEnd_45621 : Nat := 4983230072969 + 3 ^ 40 * 45621 * 2
def baseEnd_45621 : Nat := 23425500938871241327699

theorem tailTrace_45621 : CollatzResearch.WordTrace tailWord_45621 prefixEnd_45621 23425500938871241327699 := by
  unfold tailWord_45621
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663934567730383291600717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1109289711820255527733811 1663934567730383291600717)
  ·
    refine ⟨623975462898893734350269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1663934567730383291600717 623975462898893734350269)
    ·
      refine ⟨233990798587085150381351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 623975462898893734350269 233990798587085150381351)
      ·
        refine ⟨350986197880627725572027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233990798587085150381351 350986197880627725572027)
        ·
          refine ⟨526479296820941588358041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350986197880627725572027 526479296820941588358041)
          ·
            refine ⟨394859472615706191268531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526479296820941588358041 394859472615706191268531)
            ·
              refine ⟨592289208923559286902797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394859472615706191268531 592289208923559286902797)
              ·
                refine ⟨222108453346334732588549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 592289208923559286902797 222108453346334732588549)
                ·
                  refine ⟨41645335002437762360353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222108453346334732588549 41645335002437762360353)
                  ·
                    refine ⟨31234001251828321770265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41645335002437762360353 31234001251828321770265)
                    ·
                      refine ⟨23425500938871241327699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31234001251828321770265 23425500938871241327699)
                      ·
                        rfl

theorem cell23_45621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_45621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45621 prefixEnd_45621 := by exact prefixLift 45621
  have htrace : WordTrace (prefixWord ++ tailWord_45621) baseStart_45621 baseEnd_45621 := by
    simpa [prefixWord, tailWord_45621, baseEnd_45621] using wordTrace_append hprefix tailTrace_45621
  have hstable : (prefixWord ++ tailWord_45621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45621).length < 2 ^ (prefixWord ++ tailWord_45621).sum := by decide
  have hdescent : baseEnd_45621 < baseStart_45621 := by decide
  rcases family_descends (prefixWord ++ tailWord_45621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45667 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 5]
def baseStart_45667 : Nat := 118140960795 + 45667 * 2 ^ 59
def prefixEnd_45667 : Nat := 4983230072969 + 3 ^ 40 * 45667 * 2
def baseEnd_45667 : Nat := 23449121048978061352487

theorem tailTrace_45667 : CollatzResearch.WordTrace tailWord_45667 prefixEnd_45667 23449121048978061352487 := by
  unfold tailWord_45667
  simp only [CollatzResearch.WordTrace]
  refine ⟨1665612325563733147775255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1110408217042488765183503 1665612325563733147775255)
  ·
    refine ⟨2498418488345599721662883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1665612325563733147775255 2498418488345599721662883)
    ·
      refine ⟨3747627732518399582494325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2498418488345599721662883 3747627732518399582494325)
      ·
        refine ⟨351340099923599960858843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3747627732518399582494325 351340099923599960858843)
        ·
          refine ⟨527010149885399941288265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351340099923599960858843 527010149885399941288265)
          ·
            refine ⟨395257612414049955966199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527010149885399941288265 395257612414049955966199)
            ·
              refine ⟨592886418621074933949299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395257612414049955966199 592886418621074933949299)
              ·
                refine ⟨889329627931612400923949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592886418621074933949299 889329627931612400923949)
                ·
                  refine ⟨333498610474354650346481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889329627931612400923949 333498610474354650346481)
                  ·
                    refine ⟨250123957855765987759861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 333498610474354650346481 250123957855765987759861)
                    ·
                      refine ⟨23449121048978061352487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 250123957855765987759861 23449121048978061352487)
                      ·
                        rfl

theorem cell23_45667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_45667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45667 prefixEnd_45667 := by exact prefixLift 45667
  have htrace : WordTrace (prefixWord ++ tailWord_45667) baseStart_45667 baseEnd_45667 := by
    simpa [prefixWord, tailWord_45667, baseEnd_45667] using wordTrace_append hprefix tailTrace_45667
  have hstable : (prefixWord ++ tailWord_45667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45667).length < 2 ^ (prefixWord ++ tailWord_45667).sum := by decide
  have hdescent : baseEnd_45667 < baseStart_45667 := by decide
  rcases family_descends (prefixWord ++ tailWord_45667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45674 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_45674 : Nat := 118140960795 + 45674 * 2 ^ 59
def prefixEnd_45674 : Nat := 4983230072969 + 3 ^ 40 * 45674 * 2
def baseEnd_45674 : Nat := 7817571804519844654985

theorem tailTrace_45674 : CollatzResearch.WordTrace tailWord_45674 prefixEnd_45674 7817571804519844654985 := by
  unfold tailWord_45674
  simp only [CollatzResearch.WordTrace]
  refine ⟨416466909134593335820019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1110578424358915562186717 416466909134593335820019)
  ·
    refine ⟨624700363701890003730029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 416466909134593335820019 624700363701890003730029)
    ·
      refine ⟨234262636388208751398761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 624700363701890003730029 234262636388208751398761)
      ·
        refine ⟨175696977291156563549071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234262636388208751398761 175696977291156563549071)
        ·
          refine ⟨263545465936734845323607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175696977291156563549071 263545465936734845323607)
          ·
            refine ⟨395318198905102267985411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263545465936734845323607 395318198905102267985411)
            ·
              refine ⟨592977298357653401978117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395318198905102267985411 592977298357653401978117)
              ·
                refine ⟨111183243442060012870897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 592977298357653401978117 111183243442060012870897)
                ·
                  refine ⟨83387432581545009653173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111183243442060012870897 83387432581545009653173)
                  ·
                    refine ⟨7817571804519844654985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83387432581545009653173 7817571804519844654985)
                    ·
                      rfl

theorem cell23_45674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_45674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45674 prefixEnd_45674 := by exact prefixLift 45674
  have htrace : WordTrace (prefixWord ++ tailWord_45674) baseStart_45674 baseEnd_45674 := by
    simpa [prefixWord, tailWord_45674, baseEnd_45674] using wordTrace_append hprefix tailTrace_45674
  have hstable : (prefixWord ++ tailWord_45674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45674).length < 2 ^ (prefixWord ++ tailWord_45674).sum := by decide
  have hdescent : baseEnd_45674 < baseStart_45674 := by decide
  rcases family_descends (prefixWord ++ tailWord_45674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45678 : List Nat := [4, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_45678 : Nat := 118140960795 + 45678 * 2 ^ 59
def prefixEnd_45678 : Nat := 4983230072969 + 3 ^ 40 * 45678 * 2
def baseEnd_45678 : Nat := 2606085481797502034993

theorem tailTrace_45678 : CollatzResearch.WordTrace tailWord_45678 prefixEnd_45678 2606085481797502034993 := by
  unfold tailWord_45678
  simp only [CollatzResearch.WordTrace]
  refine ⟨208251691065485253303211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1110675685682588017617125 208251691065485253303211)
  ·
    refine ⟨312377536598227879954817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208251691065485253303211 312377536598227879954817)
    ·
      refine ⟨234283152448670909966113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312377536598227879954817 234283152448670909966113)
      ·
        refine ⟨175712364336503182474585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234283152448670909966113 175712364336503182474585)
        ·
          refine ⟨131784273252377386855939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175712364336503182474585 131784273252377386855939)
          ·
            refine ⟨197676409878566080283909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131784273252377386855939 197676409878566080283909)
            ·
              refine ⟨37064326852231140053233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197676409878566080283909 37064326852231140053233)
              ·
                refine ⟨27798245139173355039925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37064326852231140053233 27798245139173355039925)
                ·
                  refine ⟨2606085481797502034993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27798245139173355039925 2606085481797502034993)
                  ·
                    rfl

theorem cell23_45678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_45678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45678 prefixEnd_45678 := by exact prefixLift 45678
  have htrace : WordTrace (prefixWord ++ tailWord_45678) baseStart_45678 baseEnd_45678 := by
    simpa [prefixWord, tailWord_45678, baseEnd_45678] using wordTrace_append hprefix tailTrace_45678
  have hstable : (prefixWord ++ tailWord_45678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45678).length < 2 ^ (prefixWord ++ tailWord_45678).sum := by decide
  have hdescent : baseEnd_45678 < baseStart_45678 := by decide
  rcases family_descends (prefixWord ++ tailWord_45678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45707 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 4]
def baseStart_45707 : Nat := 118140960795 + 45707 * 2 ^ 59
def prefixEnd_45707 : Nat := 4983230072969 + 3 ^ 40 * 45707 * 2
def baseEnd_45707 : Nat := 23469660275157904852303

theorem tailTrace_45707 : CollatzResearch.WordTrace tailWord_45707 prefixEnd_45707 23469660275157904852303 := by
  unfold tailWord_45707
  simp only [CollatzResearch.WordTrace]
  refine ⟨1667071245418819979231375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1111380830279213319487583 1667071245418819979231375)
  ·
    refine ⟨2500606868128229968847063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1667071245418819979231375 2500606868128229968847063)
    ·
      refine ⟨3750910302192344953270595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2500606868128229968847063 3750910302192344953270595)
      ·
        refine ⟨5626365453288517429905893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3750910302192344953270595 5626365453288517429905893)
        ·
          refine ⟨1054943522491597018107355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5626365453288517429905893 1054943522491597018107355)
          ·
            refine ⟨1582415283737395527161033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054943522491597018107355 1582415283737395527161033)
            ·
              refine ⟨1186811462803046645370775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582415283737395527161033 1186811462803046645370775)
              ·
                refine ⟨1780217194204569968056163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186811462803046645370775 1780217194204569968056163)
                ·
                  refine ⟨2670325791306854952084245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780217194204569968056163 2670325791306854952084245)
                  ·
                    refine ⟨125171521467508825878949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2670325791306854952084245 125171521467508825878949)
                    ·
                      refine ⟨23469660275157904852303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 125171521467508825878949 23469660275157904852303)
                      ·
                        rfl

theorem cell23_45707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 4].length) (baseStart_45707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45707 prefixEnd_45707 := by exact prefixLift 45707
  have htrace : WordTrace (prefixWord ++ tailWord_45707) baseStart_45707 baseEnd_45707 := by
    simpa [prefixWord, tailWord_45707, baseEnd_45707] using wordTrace_append hprefix tailTrace_45707
  have hstable : (prefixWord ++ tailWord_45707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45707).length < 2 ^ (prefixWord ++ tailWord_45707).sum := by decide
  have hdescent : baseEnd_45707 < baseStart_45707 := by decide
  rcases family_descends (prefixWord ++ tailWord_45707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45724 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_45724 : Nat := 118140960795 + 45724 * 2 ^ 59
def prefixEnd_45724 : Nat := 4983230072969 + 3 ^ 40 * 45724 * 2
def baseEnd_45724 : Nat := 23478389446284338339725

theorem tailTrace_45724 : CollatzResearch.WordTrace tailWord_45724 prefixEnd_45724 23478389446284338339725 := by
  unfold tailWord_45724
  simp only [CollatzResearch.WordTrace]
  refine ⟨833845643178615941300113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1111794190904821255066817 833845643178615941300113)
  ·
    refine ⟨625384232383961955975085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 833845643178615941300113 625384232383961955975085)
    ·
      refine ⟨234519087143985733490657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 625384232383961955975085 234519087143985733490657)
      ·
        refine ⟨175889315357989300117993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234519087143985733490657 175889315357989300117993)
        ·
          refine ⟨131916986518491975088495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175889315357989300117993 131916986518491975088495)
          ·
            refine ⟨197875479777737962632743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131916986518491975088495 197875479777737962632743)
            ·
              refine ⟨296813219666606943949115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197875479777737962632743 296813219666606943949115)
              ·
                refine ⟨445219829499910415923673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296813219666606943949115 445219829499910415923673)
                ·
                  refine ⟨333914872124932811942755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445219829499910415923673 333914872124932811942755)
                  ·
                    refine ⟨500872308187399217914133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 333914872124932811942755 500872308187399217914133)
                    ·
                      refine ⟨23478389446284338339725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 500872308187399217914133 23478389446284338339725)
                      ·
                        rfl

theorem cell23_45724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_45724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45724 prefixEnd_45724 := by exact prefixLift 45724
  have htrace : WordTrace (prefixWord ++ tailWord_45724) baseStart_45724 baseEnd_45724 := by
    simpa [prefixWord, tailWord_45724, baseEnd_45724] using wordTrace_append hprefix tailTrace_45724
  have hstable : (prefixWord ++ tailWord_45724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45724).length < 2 ^ (prefixWord ++ tailWord_45724).sum := by decide
  have hdescent : baseEnd_45724 < baseStart_45724 := by decide
  rcases family_descends (prefixWord ++ tailWord_45724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45737 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_45737 : Nat := 118140960795 + 45737 * 2 ^ 59
def prefixEnd_45737 : Nat := 4983230072969 + 3 ^ 40 * 45737 * 2
def baseEnd_45737 : Nat := 23485064694792787477165

theorem tailTrace_45737 : CollatzResearch.WordTrace tailWord_45737 prefixEnd_45737 23485064694792787477165 := by
  unfold tailWord_45737
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668165435310135102823465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1112110290206756735215643 1668165435310135102823465)
  ·
    refine ⟨1251124076482601327117599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1668165435310135102823465 1251124076482601327117599)
    ·
      refine ⟨1876686114723901990676399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1251124076482601327117599 1876686114723901990676399)
      ·
        refine ⟨2815029172085852986014599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876686114723901990676399 2815029172085852986014599)
        ·
          refine ⟨4222543758128779479021899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815029172085852986014599 4222543758128779479021899)
          ·
            refine ⟨6333815637193169218532849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222543758128779479021899 6333815637193169218532849)
            ·
              refine ⟨4750361727894876913899637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6333815637193169218532849 4750361727894876913899637)
              ·
                refine ⟨445346411990144710678091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4750361727894876913899637 445346411990144710678091)
                ·
                  refine ⟨668019617985217066017137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445346411990144710678091 668019617985217066017137)
                  ·
                    refine ⟨501014713488912799512853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 668019617985217066017137 501014713488912799512853)
                    ·
                      refine ⟨23485064694792787477165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 501014713488912799512853 23485064694792787477165)
                      ·
                        rfl

theorem cell23_45737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_45737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45737 prefixEnd_45737 := by exact prefixLift 45737
  have htrace : WordTrace (prefixWord ++ tailWord_45737) baseStart_45737 baseEnd_45737 := by
    simpa [prefixWord, tailWord_45737, baseEnd_45737] using wordTrace_append hprefix tailTrace_45737
  have hstable : (prefixWord ++ tailWord_45737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45737).length < 2 ^ (prefixWord ++ tailWord_45737).sum := by decide
  have hdescent : baseEnd_45737 < baseStart_45737 := by decide
  rcases family_descends (prefixWord ++ tailWord_45737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45795 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 3, 1, 3]
def baseStart_45795 : Nat := 118140960795 + 45795 * 2 ^ 59
def prefixEnd_45795 : Nat := 4983230072969 + 3 ^ 40 * 45795 * 2
def baseEnd_45795 : Nat := 23514846572753560551899

theorem tailTrace_45795 : CollatzResearch.WordTrace tailWord_45795 prefixEnd_45795 23514846572753560551899 := by
  unfold tailWord_45795
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670280869100011008434839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1113520579400007338956559 1670280869100011008434839)
  ·
    refine ⟨2505421303650016512652259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1670280869100011008434839 2505421303650016512652259)
    ·
      refine ⟨3758131955475024768978389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2505421303650016512652259 3758131955475024768978389)
      ·
        refine ⟨88081217706445893022931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3758131955475024768978389 88081217706445893022931)
        ·
          refine ⟨132121826559668839534397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88081217706445893022931 132121826559668839534397)
          ·
            refine ⟨49545684959875814825399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132121826559668839534397 49545684959875814825399)
            ·
              refine ⟨74318527439813722238099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49545684959875814825399 74318527439813722238099)
              ·
                refine ⟨111477791159720583357149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74318527439813722238099 111477791159720583357149)
                ·
                  refine ⟨41804171684895218758931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111477791159720583357149 41804171684895218758931)
                  ·
                    refine ⟨62706257527342828138397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41804171684895218758931 62706257527342828138397)
                    ·
                      refine ⟨23514846572753560551899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 62706257527342828138397 23514846572753560551899)
                      ·
                        rfl

theorem cell23_45795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_45795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45795 prefixEnd_45795 := by exact prefixLift 45795
  have htrace : WordTrace (prefixWord ++ tailWord_45795) baseStart_45795 baseEnd_45795 := by
    simpa [prefixWord, tailWord_45795, baseEnd_45795] using wordTrace_append hprefix tailTrace_45795
  have hstable : (prefixWord ++ tailWord_45795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45795).length < 2 ^ (prefixWord ++ tailWord_45795).sum := by decide
  have hdescent : baseEnd_45795 < baseStart_45795 := by decide
  rcases family_descends (prefixWord ++ tailWord_45795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45804 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 3]
def baseStart_45804 : Nat := 118140960795 + 45804 * 2 ^ 59
def prefixEnd_45804 : Nat := 4983230072969 + 3 ^ 40 * 45804 * 2
def baseEnd_45804 : Nat := 23519467898644025339357

theorem tailTrace_45804 : CollatzResearch.WordTrace tailWord_45804 prefixEnd_45804 23519467898644025339357 := by
  unfold tailWord_45804
  simp only [CollatzResearch.WordTrace]
  refine ⟨835304563033702772756233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1113739417378270363674977 835304563033702772756233)
  ·
    refine ⟨626478422275277079567175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 835304563033702772756233 626478422275277079567175)
    ·
      refine ⟨939717633412915619350763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626478422275277079567175 939717633412915619350763)
      ·
        refine ⟨1409576450119373429026145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939717633412915619350763 1409576450119373429026145)
        ·
          refine ⟨1057182337589530071769609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1409576450119373429026145 1057182337589530071769609)
          ·
            refine ⟨792886753192147553827207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057182337589530071769609 792886753192147553827207)
            ·
              refine ⟨1189330129788221330740811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792886753192147553827207 1189330129788221330740811)
              ·
                refine ⟨1783995194682331996111217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189330129788221330740811 1783995194682331996111217)
                ·
                  refine ⟨1337996396011748997083413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1783995194682331996111217 1337996396011748997083413)
                  ·
                    refine ⟨62718581063050734238285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1337996396011748997083413 62718581063050734238285)
                    ·
                      refine ⟨23519467898644025339357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 62718581063050734238285 23519467898644025339357)
                      ·
                        rfl

theorem cell23_45804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_45804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45804 prefixEnd_45804 := by exact prefixLift 45804
  have htrace : WordTrace (prefixWord ++ tailWord_45804) baseStart_45804 baseEnd_45804 := by
    simpa [prefixWord, tailWord_45804, baseEnd_45804] using wordTrace_append hprefix tailTrace_45804
  have hstable : (prefixWord ++ tailWord_45804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45804).length < 2 ^ (prefixWord ++ tailWord_45804).sum := by decide
  have hdescent : baseEnd_45804 < baseStart_45804 := by decide
  rcases family_descends (prefixWord ++ tailWord_45804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45818 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2]
def baseStart_45818 : Nat := 118140960795 + 45818 * 2 ^ 59
def prefixEnd_45818 : Nat := 4983230072969 + 3 ^ 40 * 45818 * 2
def baseEnd_45818 : Nat := 23526656627806970564293

theorem tailTrace_45818 : CollatzResearch.WordTrace tailWord_45818 prefixEnd_45818 23526656627806970564293 := by
  unfold tailWord_45818
  simp only [CollatzResearch.WordTrace]
  refine ⟨417779937004171484130527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1114079832011123957681405 417779937004171484130527)
  ·
    refine ⟨626669905506257226195791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 417779937004171484130527 626669905506257226195791)
    ·
      refine ⟨940004858259385839293687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626669905506257226195791 940004858259385839293687)
      ·
        refine ⟨1410007287389078758940531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940004858259385839293687 1410007287389078758940531)
        ·
          refine ⟨2115010931083618138410797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1410007287389078758940531 2115010931083618138410797)
          ·
            refine ⟨793129099156356801904049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2115010931083618138410797 793129099156356801904049)
            ·
              refine ⟨594846824367267601428037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793129099156356801904049 594846824367267601428037)
              ·
                refine ⟨111533779568862675267757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 594846824367267601428037 111533779568862675267757)
                ·
                  refine ⟨41825167338323503225409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111533779568862675267757 41825167338323503225409)
                  ·
                    refine ⟨31368875503742627419057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41825167338323503225409 31368875503742627419057)
                    ·
                      refine ⟨23526656627806970564293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31368875503742627419057 23526656627806970564293)
                      ·
                        rfl

theorem cell23_45818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_45818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45818 prefixEnd_45818 := by exact prefixLift 45818
  have htrace : WordTrace (prefixWord ++ tailWord_45818) baseStart_45818 baseEnd_45818 := by
    simpa [prefixWord, tailWord_45818, baseEnd_45818] using wordTrace_append hprefix tailTrace_45818
  have hstable : (prefixWord ++ tailWord_45818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45818).length < 2 ^ (prefixWord ++ tailWord_45818).sum := by decide
  have hdescent : baseEnd_45818 < baseStart_45818 := by decide
  rcases family_descends (prefixWord ++ tailWord_45818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45821 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_45821 : Nat := 118140960795 + 45821 * 2 ^ 59
def prefixEnd_45821 : Nat := 4983230072969 + 3 ^ 40 * 45821 * 2
def baseEnd_45821 : Nat := 23528197069770458826779

theorem tailTrace_45821 : CollatzResearch.WordTrace tailWord_45821 prefixEnd_45821 23528197069770458826779 := by
  unfold tailWord_45821
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671229167005817448881317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1114152778003878299254211 1671229167005817448881317)
  ·
    refine ⟨313355468813590771665247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1671229167005817448881317 313355468813590771665247)
    ·
      refine ⟨470033203220386157497871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313355468813590771665247 470033203220386157497871)
      ·
        refine ⟨705049804830579236246807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470033203220386157497871 705049804830579236246807)
        ·
          refine ⟨1057574707245868854370211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705049804830579236246807 1057574707245868854370211)
          ·
            refine ⟨1586362060868803281555317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057574707245868854370211 1586362060868803281555317)
            ·
              refine ⟨148721443206450307645811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1586362060868803281555317 148721443206450307645811)
              ·
                refine ⟨223082164809675461468717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148721443206450307645811 223082164809675461468717)
                ·
                  refine ⟨83655811803628298050769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223082164809675461468717 83655811803628298050769)
                  ·
                    refine ⟨62741858852721223538077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83655811803628298050769 62741858852721223538077)
                    ·
                      refine ⟨23528197069770458826779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 62741858852721223538077 23528197069770458826779)
                      ·
                        rfl

theorem cell23_45821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_45821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45821 prefixEnd_45821 := by exact prefixLift 45821
  have htrace : WordTrace (prefixWord ++ tailWord_45821) baseStart_45821 baseEnd_45821 := by
    simpa [prefixWord, tailWord_45821, baseEnd_45821] using wordTrace_append hprefix tailTrace_45821
  have hstable : (prefixWord ++ tailWord_45821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45821).length < 2 ^ (prefixWord ++ tailWord_45821).sum := by decide
  have hdescent : baseEnd_45821 < baseStart_45821 := by decide
  rcases family_descends (prefixWord ++ tailWord_45821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45831 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_45831 : Nat := 118140960795 + 45831 * 2 ^ 59
def prefixEnd_45831 : Nat := 4983230072969 + 3 ^ 40 * 45831 * 2
def baseEnd_45831 : Nat := 23533331876315419701733

theorem tailTrace_45831 : CollatzResearch.WordTrace tailWord_45831 prefixEnd_45831 23533331876315419701733 := by
  unfold tailWord_45831
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671593896969589156745347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1114395931313059437830231 1671593896969589156745347)
  ·
    refine ⟨2507390845454383735118021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1671593896969589156745347 2507390845454383735118021)
    ·
      refine ⟨470135783522696950334629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2507390845454383735118021 470135783522696950334629)
      ·
        refine ⟨88150459410505678187743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 470135783522696950334629 88150459410505678187743)
        ·
          refine ⟨132225689115758517281615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88150459410505678187743 132225689115758517281615)
          ·
            refine ⟨198338533673637775922423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132225689115758517281615 198338533673637775922423)
            ·
              refine ⟨297507800510456663883635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198338533673637775922423 297507800510456663883635)
              ·
                refine ⟨446261700765684995825453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297507800510456663883635 446261700765684995825453)
                ·
                  refine ⟨167348137787131873434545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446261700765684995825453 167348137787131873434545)
                  ·
                    refine ⟨125511103340348905075909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167348137787131873434545 125511103340348905075909)
                    ·
                      refine ⟨23533331876315419701733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 125511103340348905075909 23533331876315419701733)
                      ·
                        rfl

theorem cell23_45831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_45831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45831 prefixEnd_45831 := by exact prefixLift 45831
  have htrace : WordTrace (prefixWord ++ tailWord_45831) baseStart_45831 baseEnd_45831 := by
    simpa [prefixWord, tailWord_45831, baseEnd_45831] using wordTrace_append hprefix tailTrace_45831
  have hstable : (prefixWord ++ tailWord_45831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45831).length < 2 ^ (prefixWord ++ tailWord_45831).sum := by decide
  have hdescent : baseEnd_45831 < baseStart_45831 := by decide
  rcases family_descends (prefixWord ++ tailWord_45831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45835 : List Nat := [1, 1, 1, 1, 5, 1, 1, 7, 1, 2, 2]
def baseStart_45835 : Nat := 118140960795 + 45835 * 2 ^ 59
def prefixEnd_45835 : Nat := 4983230072969 + 3 ^ 40 * 45835 * 2
def baseEnd_45835 : Nat := 23535385798933404051715

theorem tailTrace_45835 : CollatzResearch.WordTrace tailWord_45835 prefixEnd_45835 23535385798933404051715 := by
  unfold tailWord_45835
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671739788955097839890959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1114493192636731893260639 1671739788955097839890959)
  ·
    refine ⟨2507609683432646759836439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1671739788955097839890959 2507609683432646759836439)
    ·
      refine ⟨3761414525148970139754659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507609683432646759836439 3761414525148970139754659)
      ·
        refine ⟨5642121787723455209631989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761414525148970139754659 5642121787723455209631989)
        ·
          refine ⟨528948917599073925902999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5642121787723455209631989 528948917599073925902999)
          ·
            refine ⟨793423376398610888854499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528948917599073925902999 793423376398610888854499)
            ·
              refine ⟨1190135064597916333281749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793423376398610888854499 1190135064597916333281749)
              ·
                refine ⟨27893790576513664061291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1190135064597916333281749 27893790576513664061291)
                ·
                  refine ⟨41840685864770496091937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27893790576513664061291 41840685864770496091937)
                  ·
                    refine ⟨31380514398577872068953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41840685864770496091937 31380514398577872068953)
                    ·
                      refine ⟨23535385798933404051715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31380514398577872068953 23535385798933404051715)
                      ·
                        rfl

theorem cell23_45835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 1, 2, 2].length) (baseStart_45835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45835 prefixEnd_45835 := by exact prefixLift 45835
  have htrace : WordTrace (prefixWord ++ tailWord_45835) baseStart_45835 baseEnd_45835 := by
    simpa [prefixWord, tailWord_45835, baseEnd_45835] using wordTrace_append hprefix tailTrace_45835
  have hstable : (prefixWord ++ tailWord_45835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45835).length < 2 ^ (prefixWord ++ tailWord_45835).sum := by decide
  have hdescent : baseEnd_45835 < baseStart_45835 := by decide
  rcases family_descends (prefixWord ++ tailWord_45835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45852 : List Nat := [2, 2, 3, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_45852 : Nat := 118140960795 + 45852 * 2 ^ 59
def prefixEnd_45852 : Nat := 4983230072969 + 3 ^ 40 * 45852 * 2
def baseEnd_45852 : Nat := 23544114970059837539137

theorem tailTrace_45852 : CollatzResearch.WordTrace tailWord_45852 prefixEnd_45852 23544114970059837539137 := by
  unfold tailWord_45852
  simp only [CollatzResearch.WordTrace]
  refine ⟨836179914946754871629905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1114906553262339828839873 836179914946754871629905)
  ·
    refine ⟨627134936210066153722429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 836179914946754871629905 627134936210066153722429)
    ·
      refine ⟨235175601078774807645911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 627134936210066153722429 235175601078774807645911)
      ·
        refine ⟨352763401618162211468867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235175601078774807645911 352763401618162211468867)
        ·
          refine ⟨529145102427243317203301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352763401618162211468867 529145102427243317203301)
          ·
            refine ⟨99214706705108121975619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 529145102427243317203301 99214706705108121975619)
            ·
              refine ⟨148822060057662182963429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99214706705108121975619 148822060057662182963429)
              ·
                refine ⟨27904136260811659305643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148822060057662182963429 27904136260811659305643)
                ·
                  refine ⟨41856204391217488958465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27904136260811659305643 41856204391217488958465)
                  ·
                    refine ⟨31392153293413116718849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41856204391217488958465 31392153293413116718849)
                    ·
                      refine ⟨23544114970059837539137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31392153293413116718849 23544114970059837539137)
                      ·
                        rfl

theorem cell23_45852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_45852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45852 prefixEnd_45852 := by exact prefixLift 45852
  have htrace : WordTrace (prefixWord ++ tailWord_45852) baseStart_45852 baseEnd_45852 := by
    simpa [prefixWord, tailWord_45852, baseEnd_45852] using wordTrace_append hprefix tailTrace_45852
  have hstable : (prefixWord ++ tailWord_45852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45852).length < 2 ^ (prefixWord ++ tailWord_45852).sum := by decide
  have hdescent : baseEnd_45852 < baseStart_45852 := by decide
  rcases family_descends (prefixWord ++ tailWord_45852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45868 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 3]
def baseStart_45868 : Nat := 118140960795 + 45868 * 2 ^ 59
def prefixEnd_45868 : Nat := 4983230072969 + 3 ^ 40 * 45868 * 2
def baseEnd_45868 : Nat := 23552330660531774939063

theorem tailTrace_45868 : CollatzResearch.WordTrace tailWord_45868 prefixEnd_45868 23552330660531774939063 := by
  unfold tailWord_45868
  simp only [CollatzResearch.WordTrace]
  refine ⟨836471698917772237921129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1115295598557029650561505 836471698917772237921129)
  ·
    refine ⟨627353774188329178440847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 836471698917772237921129 627353774188329178440847)
    ·
      refine ⟨941030661282493767661271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 627353774188329178440847 941030661282493767661271)
      ·
        refine ⟨1411545991923740651491907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941030661282493767661271 1411545991923740651491907)
        ·
          refine ⟨2117318987885610977237861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411545991923740651491907 2117318987885610977237861)
          ·
            refine ⟨396997310228552058232099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2117318987885610977237861 396997310228552058232099)
            ·
              refine ⟨595495965342828087348149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396997310228552058232099 595495965342828087348149)
              ·
                refine ⟨55827746750890133188889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 595495965342828087348149 55827746750890133188889)
                ·
                  refine ⟨41870810063167599891667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55827746750890133188889 41870810063167599891667)
                  ·
                    refine ⟨62806215094751399837501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41870810063167599891667 62806215094751399837501)
                    ·
                      refine ⟨23552330660531774939063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 62806215094751399837501 23552330660531774939063)
                      ·
                        rfl

theorem cell23_45868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_45868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45868 prefixEnd_45868 := by exact prefixLift 45868
  have htrace : WordTrace (prefixWord ++ tailWord_45868) baseStart_45868 baseEnd_45868 := by
    simpa [prefixWord, tailWord_45868, baseEnd_45868] using wordTrace_append hprefix tailTrace_45868
  have hstable : (prefixWord ++ tailWord_45868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45868).length < 2 ^ (prefixWord ++ tailWord_45868).sum := by decide
  have hdescent : baseEnd_45868 < baseStart_45868 := by decide
  rcases family_descends (prefixWord ++ tailWord_45868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45869 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_45869 : Nat := 118140960795 + 45869 * 2 ^ 59
def prefixEnd_45869 : Nat := 4983230072969 + 3 ^ 40 * 45869 * 2
def baseEnd_45869 : Nat := 23552844141186271026559

theorem tailTrace_45869 : CollatzResearch.WordTrace tailWord_45869 prefixEnd_45869 23552844141186271026559 := by
  unfold tailWord_45869
  simp only [CollatzResearch.WordTrace]
  refine ⟨1672979870831921646628661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1115319913887947764419107 1672979870831921646628661)
  ·
    refine ⟨156841862890492654371437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1672979870831921646628661 156841862890492654371437)
    ·
      refine ⟨58815698583934745389289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156841862890492654371437 58815698583934745389289)
      ·
        refine ⟨44111773937951059041967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58815698583934745389289 44111773937951059041967)
        ·
          refine ⟨66167660906926588562951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44111773937951059041967 66167660906926588562951)
          ·
            refine ⟨99251491360389882844427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66167660906926588562951 99251491360389882844427)
            ·
              refine ⟨148877237040584824266641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99251491360389882844427 148877237040584824266641)
              ·
                refine ⟨111657927780438618199981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148877237040584824266641 111657927780438618199981)
                ·
                  refine ⟨41871722917664481824993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111657927780438618199981 41871722917664481824993)
                  ·
                    refine ⟨31403792188248361368745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41871722917664481824993 31403792188248361368745)
                    ·
                      refine ⟨23552844141186271026559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31403792188248361368745 23552844141186271026559)
                      ·
                        rfl

theorem cell23_45869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_45869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45869 prefixEnd_45869 := by exact prefixLift 45869
  have htrace : WordTrace (prefixWord ++ tailWord_45869) baseStart_45869 baseEnd_45869 := by
    simpa [prefixWord, tailWord_45869, baseEnd_45869] using wordTrace_append hprefix tailTrace_45869
  have hstable : (prefixWord ++ tailWord_45869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45869).length < 2 ^ (prefixWord ++ tailWord_45869).sum := by decide
  have hdescent : baseEnd_45869 < baseStart_45869 := by decide
  rcases family_descends (prefixWord ++ tailWord_45869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45884 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_45884 : Nat := 118140960795 + 45884 * 2 ^ 59
def prefixEnd_45884 : Nat := 4983230072969 + 3 ^ 40 * 45884 * 2
def baseEnd_45884 : Nat := 7853515450334570779663

theorem tailTrace_45884 : CollatzResearch.WordTrace tailWord_45884 prefixEnd_45884 7853515450334570779663 := by
  unfold tailWord_45884
  simp only [CollatzResearch.WordTrace]
  refine ⟨836763482888789604212353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1115684643851719472283137 836763482888789604212353)
  ·
    refine ⟨627572612166592203159265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 836763482888789604212353 627572612166592203159265)
    ·
      refine ⟨470679459124944152369449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 627572612166592203159265 470679459124944152369449)
      ·
        refine ⟨353009594343708114277087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470679459124944152369449 353009594343708114277087)
        ·
          refine ⟨529514391515562171415631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353009594343708114277087 529514391515562171415631)
          ·
            refine ⟨794271587273343257123447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529514391515562171415631 794271587273343257123447)
            ·
              refine ⟨1191407380910014885685171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794271587273343257123447 1191407380910014885685171)
              ·
                refine ⟨1787111071365022328527757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191407380910014885685171 1787111071365022328527757)
                ·
                  refine ⟨670166651761883373197909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1787111071365022328527757 670166651761883373197909)
                  ·
                    refine ⟨7853515450334570779663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 670166651761883373197909 7853515450334570779663)
                    ·
                      rfl

theorem cell23_45884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_45884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45884 prefixEnd_45884 := by exact prefixLift 45884
  have htrace : WordTrace (prefixWord ++ tailWord_45884) baseStart_45884 baseEnd_45884 := by
    simpa [prefixWord, tailWord_45884, baseEnd_45884] using wordTrace_append hprefix tailTrace_45884
  have hstable : (prefixWord ++ tailWord_45884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45884).length < 2 ^ (prefixWord ++ tailWord_45884).sum := by decide
  have hdescent : baseEnd_45884 < baseStart_45884 := by decide
  rcases family_descends (prefixWord ++ tailWord_45884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45889 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_45889 : Nat := 118140960795 + 45889 * 2 ^ 59
def prefixEnd_45889 : Nat := 4983230072969 + 3 ^ 40 * 45889 * 2
def baseEnd_45889 : Nat := 23563113754276192776467

theorem tailTrace_45889 : CollatzResearch.WordTrace tailWord_45889 prefixEnd_45889 23563113754276192776467 := by
  unfold tailWord_45889
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673709330759465062356721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1115806220506310041571147 1673709330759465062356721)
  ·
    refine ⟨1255281998069598796767541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1673709330759465062356721 1255281998069598796767541)
    ·
      refine ⟨117682687319024887196957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1255281998069598796767541 117682687319024887196957)
      ·
        refine ⟨44131007744634332698859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117682687319024887196957 44131007744634332698859)
        ·
          refine ⟨66196511616951499048289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44131007744634332698859 66196511616951499048289)
          ·
            refine ⟨49647383712713624286217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66196511616951499048289 49647383712713624286217)
            ·
              refine ⟨37235537784535218214663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49647383712713624286217 37235537784535218214663)
              ·
                refine ⟨55853306676802827321995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37235537784535218214663 55853306676802827321995)
                ·
                  refine ⟨83779960015204240982993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55853306676802827321995 83779960015204240982993)
                  ·
                    refine ⟨62834970011403180737245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83779960015204240982993 62834970011403180737245)
                    ·
                      refine ⟨23563113754276192776467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 62834970011403180737245 23563113754276192776467)
                      ·
                        rfl

theorem cell23_45889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_45889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45889 prefixEnd_45889 := by exact prefixLift 45889
  have htrace : WordTrace (prefixWord ++ tailWord_45889) baseStart_45889 baseEnd_45889 := by
    simpa [prefixWord, tailWord_45889, baseEnd_45889] using wordTrace_append hprefix tailTrace_45889
  have hstable : (prefixWord ++ tailWord_45889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45889).length < 2 ^ (prefixWord ++ tailWord_45889).sum := by decide
  have hdescent : baseEnd_45889 < baseStart_45889 := by decide
  rcases family_descends (prefixWord ++ tailWord_45889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45925 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 2, 2, 2]
def baseStart_45925 : Nat := 118140960795 + 45925 * 2 ^ 59
def prefixEnd_45925 : Nat := 4983230072969 + 3 ^ 40 * 45925 * 2
def baseEnd_45925 : Nat := 23581599057838051926301

theorem tailTrace_45925 : CollatzResearch.WordTrace tailWord_45925 prefixEnd_45925 23581599057838051926301 := by
  unfold tailWord_45925
  simp only [CollatzResearch.WordTrace]
  refine ⟨1675022358629043210667229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1116681572419362140444819 1675022358629043210667229)
  ·
    refine ⟨628133384485891204000211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1675022358629043210667229 628133384485891204000211)
    ·
      refine ⟨942200076728836806000317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628133384485891204000211 942200076728836806000317)
      ·
        refine ⟨353325028773313802250119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 942200076728836806000317 353325028773313802250119)
        ·
          refine ⟨529987543159970703375179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353325028773313802250119 529987543159970703375179)
          ·
            refine ⟨794981314739956055062769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529987543159970703375179 794981314739956055062769)
            ·
              refine ⟨596235986054967041297077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794981314739956055062769 596235986054967041297077)
              ·
                refine ⟨55897123692653160121601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 596235986054967041297077 55897123692653160121601)
                ·
                  refine ⟨41922842769489870091201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55897123692653160121601 41922842769489870091201)
                  ·
                    refine ⟨31442132077117402568401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41922842769489870091201 31442132077117402568401)
                    ·
                      refine ⟨23581599057838051926301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31442132077117402568401 23581599057838051926301)
                      ·
                        rfl

theorem cell23_45925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_45925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45925 prefixEnd_45925 := by exact prefixLift 45925
  have htrace : WordTrace (prefixWord ++ tailWord_45925) baseStart_45925 baseEnd_45925 := by
    simpa [prefixWord, tailWord_45925, baseEnd_45925] using wordTrace_append hprefix tailTrace_45925
  have hstable : (prefixWord ++ tailWord_45925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45925).length < 2 ^ (prefixWord ++ tailWord_45925).sum := by decide
  have hdescent : baseEnd_45925 < baseStart_45925 := by decide
  rcases family_descends (prefixWord ++ tailWord_45925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45942 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_45942 : Nat := 118140960795 + 45942 * 2 ^ 59
def prefixEnd_45942 : Nat := 4983230072969 + 3 ^ 40 * 45942 * 2
def baseEnd_45942 : Nat := 23590328228964485413723

theorem tailTrace_45942 : CollatzResearch.WordTrace tailWord_45942 prefixEnd_45942 23590328228964485413723 := by
  unfold tailWord_45942
  simp only [CollatzResearch.WordTrace]
  refine ⟨104727649972965944627255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1117094933044970076024053 104727649972965944627255)
  ·
    refine ⟨157091474959448916940883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104727649972965944627255 157091474959448916940883)
    ·
      refine ⟨235637212439173375411325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157091474959448916940883 235637212439173375411325)
      ·
        refine ⟨88363954664690015779247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235637212439173375411325 88363954664690015779247)
        ·
          refine ⟨132545931997035023668871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88363954664690015779247 132545931997035023668871)
          ·
            refine ⟨198818897995552535503307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132545931997035023668871 198818897995552535503307)
            ·
              refine ⟨298228346993328803254961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198818897995552535503307 298228346993328803254961)
              ·
                refine ⟨223671260244996602441221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298228346993328803254961 223671260244996602441221)
                ·
                  refine ⟨41938361295936862957729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223671260244996602441221 41938361295936862957729)
                  ·
                    refine ⟨31453770971952647218297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41938361295936862957729 31453770971952647218297)
                    ·
                      refine ⟨23590328228964485413723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31453770971952647218297 23590328228964485413723)
                      ·
                        rfl

theorem cell23_45942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_45942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45942 prefixEnd_45942 := by exact prefixLift 45942
  have htrace : WordTrace (prefixWord ++ tailWord_45942) baseStart_45942 baseEnd_45942 := by
    simpa [prefixWord, tailWord_45942, baseEnd_45942] using wordTrace_append hprefix tailTrace_45942
  have hstable : (prefixWord ++ tailWord_45942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45942).length < 2 ^ (prefixWord ++ tailWord_45942).sum := by decide
  have hdescent : baseEnd_45942 < baseStart_45942 := by decide
  rcases family_descends (prefixWord ++ tailWord_45942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45961 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 4, 5]
def baseStart_45961 : Nat := 118140960795 + 45961 * 2 ^ 59
def prefixEnd_45961 : Nat := 4983230072969 + 3 ^ 40 * 45961 * 2
def baseEnd_45961 : Nat := 7866694787133303692045

theorem tailTrace_45961 : CollatzResearch.WordTrace tailWord_45961 prefixEnd_45961 7866694787133303692045 := by
  unfold tailWord_45961
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676335386498621358977737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1117556924332414239318491 1676335386498621358977737)
  ·
    refine ⟨1257251539873966019233303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1676335386498621358977737 1257251539873966019233303)
    ·
      refine ⟨1885877309810949028849955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1257251539873966019233303 1885877309810949028849955)
      ·
        refine ⟨2828815964716423543274933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885877309810949028849955 2828815964716423543274933)
        ·
          refine ⟨265201496692164707182025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2828815964716423543274933 265201496692164707182025)
          ·
            refine ⟨198901122519123530386519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265201496692164707182025 198901122519123530386519)
            ·
              refine ⟨298351683778685295579779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198901122519123530386519 298351683778685295579779)
              ·
                refine ⟨447527525668027943369669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298351683778685295579779 447527525668027943369669)
                ·
                  refine ⟨83911411062755239381813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447527525668027943369669 83911411062755239381813)
                  ·
                    refine ⟨7866694787133303692045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83911411062755239381813 7866694787133303692045)
                    ·
                      rfl

theorem cell23_45961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_45961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_45961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_45961 prefixEnd_45961 := by exact prefixLift 45961
  have htrace : WordTrace (prefixWord ++ tailWord_45961) baseStart_45961 baseEnd_45961 := by
    simpa [prefixWord, tailWord_45961, baseEnd_45961] using wordTrace_append hprefix tailTrace_45961
  have hstable : (prefixWord ++ tailWord_45961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45961).length < 2 ^ (prefixWord ++ tailWord_45961).sum := by decide
  have hdescent : baseEnd_45961 < baseStart_45961 := by decide
  rcases family_descends (prefixWord ++ tailWord_45961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46116 : List Nat := [2, 3, 1, 4, 1, 3, 1, 3, 1, 1, 3]
def baseStart_46116 : Nat := 118140960795 + 46116 * 2 ^ 59
def prefixEnd_46116 : Nat := 4983230072969 + 3 ^ 40 * 46116 * 2
def baseEnd_46116 : Nat := 23679673862846804637923

theorem tailTrace_46116 : CollatzResearch.WordTrace tailWord_46116 prefixEnd_46116 23679673862846804637923 := by
  unfold tailWord_46116
  simp only [CollatzResearch.WordTrace]
  refine ⟨840994350468541415435101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1121325800624721887246801 840994350468541415435101)
  ·
    refine ⟨315372881425703030788163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 840994350468541415435101 315372881425703030788163)
    ·
      refine ⟨473059322138554546182245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315372881425703030788163 473059322138554546182245)
      ·
        refine ⟨88698622900978977409171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 473059322138554546182245 88698622900978977409171)
        ·
          refine ⟨133047934351468466113757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88698622900978977409171 133047934351468466113757)
          ·
            refine ⟨49892975381800674792659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133047934351468466113757 49892975381800674792659)
            ·
              refine ⟨74839463072701012188989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49892975381800674792659 74839463072701012188989)
              ·
                refine ⟨28064798652262879570871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74839463072701012188989 28064798652262879570871)
                ·
                  refine ⟨42097197978394319356307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28064798652262879570871 42097197978394319356307)
                  ·
                    refine ⟨63145796967591479034461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42097197978394319356307 63145796967591479034461)
                    ·
                      refine ⟨23679673862846804637923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 63145796967591479034461 23679673862846804637923)
                      ·
                        rfl

theorem cell23_46116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_46116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46116 prefixEnd_46116 := by exact prefixLift 46116
  have htrace : WordTrace (prefixWord ++ tailWord_46116) baseStart_46116 baseEnd_46116 := by
    simpa [prefixWord, tailWord_46116, baseEnd_46116] using wordTrace_append hprefix tailTrace_46116
  have hstable : (prefixWord ++ tailWord_46116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46116).length < 2 ^ (prefixWord ++ tailWord_46116).sum := by decide
  have hdescent : baseEnd_46116 < baseStart_46116 := by decide
  rcases family_descends (prefixWord ++ tailWord_46116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46132 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_46132 : Nat := 118140960795 + 46132 * 2 ^ 59
def prefixEnd_46132 : Nat := 4983230072969 + 3 ^ 40 * 46132 * 2
def baseEnd_46132 : Nat := 7895963184439580679283

theorem tailTrace_46132 : CollatzResearch.WordTrace tailWord_46132 prefixEnd_46132 7895963184439580679283 := by
  unfold tailWord_46132
  simp only [CollatzResearch.WordTrace]
  refine ⟨841286134439558781726325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1121714845919411708968433 841286134439558781726325)
  ·
    refine ⟨78870575103708635786843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 841286134439558781726325 78870575103708635786843)
    ·
      refine ⟨118305862655562953680265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78870575103708635786843 118305862655562953680265)
      ·
        refine ⟨88729396991672215260199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118305862655562953680265 88729396991672215260199)
        ·
          refine ⟨133094095487508322890299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88729396991672215260199 133094095487508322890299)
          ·
            refine ⟨199641143231262484335449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133094095487508322890299 199641143231262484335449)
            ·
              refine ⟨149730857423446863251587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199641143231262484335449 149730857423446863251587)
              ·
                refine ⟨224596286135170294877381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149730857423446863251587 224596286135170294877381)
                ·
                  refine ⟨42111803650344430289509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224596286135170294877381 42111803650344430289509)
                  ·
                    refine ⟨7895963184439580679283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42111803650344430289509 7895963184439580679283)
                    ·
                      rfl

theorem cell23_46132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_46132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46132 prefixEnd_46132 := by exact prefixLift 46132
  have htrace : WordTrace (prefixWord ++ tailWord_46132) baseStart_46132 baseEnd_46132 := by
    simpa [prefixWord, tailWord_46132, baseEnd_46132] using wordTrace_append hprefix tailTrace_46132
  have hstable : (prefixWord ++ tailWord_46132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46132).length < 2 ^ (prefixWord ++ tailWord_46132).sum := by decide
  have hdescent : baseEnd_46132 < baseStart_46132 := by decide
  rcases family_descends (prefixWord ++ tailWord_46132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46145 : List Nat := [1, 2, 5, 1, 3, 1, 2, 8]
def baseStart_46145 : Nat := 118140960795 + 46145 * 2 ^ 59
def prefixEnd_46145 : Nat := 4983230072969 + 3 ^ 40 * 46145 * 2
def baseEnd_46145 : Nat := 877576474141747821307

theorem tailTrace_46145 : CollatzResearch.WordTrace tailWord_46145 prefixEnd_46145 877576474141747821307 := by
  unfold tailWord_46145
  simp only [CollatzResearch.WordTrace]
  refine ⟨1683046417832020783675889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1122030945221347189117259 1683046417832020783675889)
  ·
    refine ⟨1262284813374015587756917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1683046417832020783675889 1262284813374015587756917)
    ·
      refine ⟨118339201253813961352211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1262284813374015587756917 118339201253813961352211)
      ·
        refine ⟨177508801880720942028317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118339201253813961352211 177508801880720942028317)
        ·
          refine ⟨66565800705270353260619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177508801880720942028317 66565800705270353260619)
          ·
            refine ⟨99848701057905529890929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66565800705270353260619 99848701057905529890929)
            ·
              refine ⟨74886525793429147418197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99848701057905529890929 74886525793429147418197)
              ·
                refine ⟨877576474141747821307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 74886525793429147418197 877576474141747821307)
                ·
                  rfl

theorem cell23_46145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 8].length) (baseStart_46145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46145 prefixEnd_46145 := by exact prefixLift 46145
  have htrace : WordTrace (prefixWord ++ tailWord_46145) baseStart_46145 baseEnd_46145 := by
    simpa [prefixWord, tailWord_46145, baseEnd_46145] using wordTrace_append hprefix tailTrace_46145
  have hstable : (prefixWord ++ tailWord_46145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46145).length < 2 ^ (prefixWord ++ tailWord_46145).sum := by decide
  have hdescent : baseEnd_46145 < baseStart_46145 := by decide
  rcases family_descends (prefixWord ++ tailWord_46145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46188 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_46188 : Nat := 118140960795 + 46188 * 2 ^ 59
def prefixEnd_46188 : Nat := 4983230072969 + 3 ^ 40 * 46188 * 2
def baseEnd_46188 : Nat := 7905548156656840979197

theorem tailTrace_46188 : CollatzResearch.WordTrace tailWord_46188 prefixEnd_46188 7905548156656840979197 := by
  unfold tailWord_46188
  simp only [CollatzResearch.WordTrace]
  refine ⟨842307378338119563745609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1123076504450826084994145 842307378338119563745609)
  ·
    refine ⟨631730533753589672809207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 842307378338119563745609 631730533753589672809207)
    ·
      refine ⟨947595800630384509213811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 631730533753589672809207 947595800630384509213811)
      ·
        refine ⟨1421393700945576763820717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947595800630384509213811 1421393700945576763820717)
        ·
          refine ⟨533022637854591286432769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1421393700945576763820717 533022637854591286432769)
          ·
            refine ⟨399766978390943464824577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533022637854591286432769 399766978390943464824577)
            ·
              refine ⟨299825233793207598618433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399766978390943464824577 299825233793207598618433)
              ·
                refine ⟨224868925344905698963825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299825233793207598618433 224868925344905698963825)
                ·
                  refine ⟨168651694008679274222869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224868925344905698963825 168651694008679274222869)
                  ·
                    refine ⟨7905548156656840979197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 168651694008679274222869 7905548156656840979197)
                    ·
                      rfl

theorem cell23_46188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_46188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46188 prefixEnd_46188 := by exact prefixLift 46188
  have htrace : WordTrace (prefixWord ++ tailWord_46188) baseStart_46188 baseEnd_46188 := by
    simpa [prefixWord, tailWord_46188, baseEnd_46188] using wordTrace_append hprefix tailTrace_46188
  have hstable : (prefixWord ++ tailWord_46188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46188).length < 2 ^ (prefixWord ++ tailWord_46188).sum := by decide
  have hdescent : baseEnd_46188 < baseStart_46188 := by decide
  rcases family_descends (prefixWord ++ tailWord_46188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46189 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_46189 : Nat := 118140960795 + 46189 * 2 ^ 59
def prefixEnd_46189 : Nat := 4983230072969 + 3 ^ 40 * 46189 * 2
def baseEnd_46189 : Nat := 23717157950625019025087

theorem tailTrace_46189 : CollatzResearch.WordTrace tailWord_46189 prefixEnd_46189 23717157950625019025087 := by
  unfold tailWord_46189
  simp only [CollatzResearch.WordTrace]
  refine ⟨1684651229672616298277621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1123100819781744198851747 1684651229672616298277621)
  ·
    refine ⟨157936052781807777963527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1684651229672616298277621 157936052781807777963527)
    ·
      refine ⟨236904079172711666945291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157936052781807777963527 236904079172711666945291)
      ·
        refine ⟨355356118759067500417937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236904079172711666945291 355356118759067500417937)
        ·
          refine ⟨266517089069300625313453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355356118759067500417937 266517089069300625313453)
          ·
            refine ⟨99943908400987734492545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266517089069300625313453 99943908400987734492545)
            ·
              refine ⟨74957931300740800869409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99943908400987734492545 74957931300740800869409)
              ·
                refine ⟨56218448475555600652057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74957931300740800869409 56218448475555600652057)
                ·
                  refine ⟨42163836356666700489043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56218448475555600652057 42163836356666700489043)
                  ·
                    refine ⟨63245754535000050733565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42163836356666700489043 63245754535000050733565)
                    ·
                      refine ⟨23717157950625019025087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 63245754535000050733565 23717157950625019025087)
                      ·
                        rfl

theorem cell23_46189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_46189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46189 prefixEnd_46189 := by exact prefixLift 46189
  have htrace : WordTrace (prefixWord ++ tailWord_46189) baseStart_46189 baseEnd_46189 := by
    simpa [prefixWord, tailWord_46189, baseEnd_46189] using wordTrace_append hprefix tailTrace_46189
  have hstable : (prefixWord ++ tailWord_46189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46189).length < 2 ^ (prefixWord ++ tailWord_46189).sum := by decide
  have hdescent : baseEnd_46189 < baseStart_46189 := by decide
  rcases family_descends (prefixWord ++ tailWord_46189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46208 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_46208 : Nat := 118140960795 + 46208 * 2 ^ 59
def prefixEnd_46208 : Nat := 4983230072969 + 3 ^ 40 * 46208 * 2
def baseEnd_46208 : Nat := 23726914083060444687499

theorem tailTrace_46208 : CollatzResearch.WordTrace tailWord_46208 prefixEnd_46208 23726914083060444687499 := by
  unfold tailWord_46208
  simp only [CollatzResearch.WordTrace]
  refine ⟨842672108301891271609639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1123562811069188362146185 842672108301891271609639)
  ·
    refine ⟨1264008162452836907414459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 842672108301891271609639 1264008162452836907414459)
    ·
      refine ⟨1896012243679255361121689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1264008162452836907414459 1896012243679255361121689)
      ·
        refine ⟨1422009182759441520841267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1896012243679255361121689 1422009182759441520841267)
        ·
          refine ⟨2133013774139162281261901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422009182759441520841267 2133013774139162281261901)
          ·
            refine ⟨799880165302185855473213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2133013774139162281261901 799880165302185855473213)
            ·
              refine ⟨299955061988319695802455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 799880165302185855473213 299955061988319695802455)
              ·
                refine ⟨449932592982479543703683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299955061988319695802455 449932592982479543703683)
                ·
                  refine ⟨674898889473719315555525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449932592982479543703683 674898889473719315555525)
                  ·
                    refine ⟨126543541776322371666661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674898889473719315555525 126543541776322371666661)
                    ·
                      refine ⟨23726914083060444687499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 126543541776322371666661 23726914083060444687499)
                      ·
                        rfl

theorem cell23_46208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_46208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46208 prefixEnd_46208 := by exact prefixLift 46208
  have htrace : WordTrace (prefixWord ++ tailWord_46208) baseStart_46208 baseEnd_46208 := by
    simpa [prefixWord, tailWord_46208, baseEnd_46208] using wordTrace_append hprefix tailTrace_46208
  have hstable : (prefixWord ++ tailWord_46208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46208).length < 2 ^ (prefixWord ++ tailWord_46208).sum := by decide
  have hdescent : baseEnd_46208 < baseStart_46208 := by decide
  rcases family_descends (prefixWord ++ tailWord_46208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46212 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_46212 : Nat := 118140960795 + 46212 * 2 ^ 59
def prefixEnd_46212 : Nat := 4983230072969 + 3 ^ 40 * 46212 * 2
def baseEnd_46212 : Nat := 23728968005678429037481

theorem tailTrace_46212 : CollatzResearch.WordTrace tailWord_46212 prefixEnd_46212 23728968005678429037481 := by
  unfold tailWord_46212
  simp only [CollatzResearch.WordTrace]
  refine ⟨842745054294645613182445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1123660072392860817576593 842745054294645613182445)
  ·
    refine ⟨316029395360492104943417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 842745054294645613182445 316029395360492104943417)
    ·
      refine ⟨237022046520369078707563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316029395360492104943417 237022046520369078707563)
      ·
        refine ⟨355533069780553618061345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237022046520369078707563 355533069780553618061345)
        ·
          refine ⟨266649802335415213546009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355533069780553618061345 266649802335415213546009)
          ·
            refine ⟨199987351751561410159507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266649802335415213546009 199987351751561410159507)
            ·
              refine ⟨299981027627342115239261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199987351751561410159507 299981027627342115239261)
              ·
                refine ⟨112492885360253293214723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299981027627342115239261 112492885360253293214723)
                ·
                  refine ⟨168739328040379939822085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112492885360253293214723 168739328040379939822085)
                  ·
                    refine ⟨31638624007571238716641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168739328040379939822085 31638624007571238716641)
                    ·
                      refine ⟨23728968005678429037481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31638624007571238716641 23728968005678429037481)
                      ·
                        rfl

theorem cell23_46212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_46212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46212 prefixEnd_46212 := by exact prefixLift 46212
  have htrace : WordTrace (prefixWord ++ tailWord_46212) baseStart_46212 baseEnd_46212 := by
    simpa [prefixWord, tailWord_46212, baseEnd_46212] using wordTrace_append hprefix tailTrace_46212
  have hstable : (prefixWord ++ tailWord_46212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46212).length < 2 ^ (prefixWord ++ tailWord_46212).sum := by decide
  have hdescent : baseEnd_46212 < baseStart_46212 := by decide
  rcases family_descends (prefixWord ++ tailWord_46212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46245 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 2, 3, 3]
def baseStart_46245 : Nat := 118140960795 + 46245 * 2 ^ 59
def prefixEnd_46245 : Nat := 4983230072969 + 3 ^ 40 * 46245 * 2
def baseEnd_46245 : Nat := 23745912867276799924829

theorem tailTrace_46245 : CollatzResearch.WordTrace tailWord_46245 prefixEnd_46245 23745912867276799924829 := by
  unfold tailWord_46245
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686693717469737862316189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1124462478313158574877459 1686693717469737862316189)
  ·
    refine ⟨632510144051151698368571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1686693717469737862316189 632510144051151698368571)
    ·
      refine ⟨948765216076727547552857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 632510144051151698368571 948765216076727547552857)
      ·
        refine ⟨711573912057545660664643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 948765216076727547552857 711573912057545660664643)
        ·
          refine ⟨1067360868086318490996965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711573912057545660664643 1067360868086318490996965)
          ·
            refine ⟨200130162766184717061931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1067360868086318490996965 200130162766184717061931)
            ·
              refine ⟨300195244149277075592897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200130162766184717061931 300195244149277075592897)
              ·
                refine ⟨225146433111957806694673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300195244149277075592897 225146433111957806694673)
                ·
                  refine ⟨168859824833968355021005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225146433111957806694673 168859824833968355021005)
                  ·
                    refine ⟨63322434312738133132877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168859824833968355021005 63322434312738133132877)
                    ·
                      refine ⟨23745912867276799924829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 63322434312738133132877 23745912867276799924829)
                      ·
                        rfl

theorem cell23_46245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_46245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46245 prefixEnd_46245 := by exact prefixLift 46245
  have htrace : WordTrace (prefixWord ++ tailWord_46245) baseStart_46245 baseEnd_46245 := by
    simpa [prefixWord, tailWord_46245, baseEnd_46245] using wordTrace_append hprefix tailTrace_46245
  have hstable : (prefixWord ++ tailWord_46245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46245).length < 2 ^ (prefixWord ++ tailWord_46245).sum := by decide
  have hdescent : baseEnd_46245 < baseStart_46245 := by decide
  rcases family_descends (prefixWord ++ tailWord_46245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46255 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 1, 7, 2]
def baseStart_46255 : Nat := 118140960795 + 46255 * 2 ^ 59
def prefixEnd_46255 : Nat := 4983230072969 + 3 ^ 40 * 46255 * 2
def baseEnd_46255 : Nat := 23751047673821760799783

theorem tailTrace_46255 : CollatzResearch.WordTrace tailWord_46255 prefixEnd_46255 23751047673821760799783 := by
  unfold tailWord_46255
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687058447433509570180219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1124705631622339713453479 1687058447433509570180219)
  ·
    refine ⟨2530587671150264355270329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1687058447433509570180219 2530587671150264355270329)
    ·
      refine ⟨1897940753362698266452747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2530587671150264355270329 1897940753362698266452747)
      ·
        refine ⟨2846911130044047399679121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897940753362698266452747 2846911130044047399679121)
        ·
          refine ⟨2135183347533035549759341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2846911130044047399679121 2135183347533035549759341)
          ·
            refine ⟨800693755324888331159753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2135183347533035549759341 800693755324888331159753)
            ·
              refine ⟨600520316493666248369815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800693755324888331159753 600520316493666248369815)
              ·
                refine ⟨900780474740499372554723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600520316493666248369815 900780474740499372554723)
                ·
                  refine ⟨1351170712110749058832085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900780474740499372554723 1351170712110749058832085)
                  ·
                    refine ⟨31668063565095681066377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1351170712110749058832085 31668063565095681066377)
                    ·
                      refine ⟨23751047673821760799783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31668063565095681066377 23751047673821760799783)
                      ·
                        rfl

theorem cell23_46255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 7, 2].length) (baseStart_46255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46255 prefixEnd_46255 := by exact prefixLift 46255
  have htrace : WordTrace (prefixWord ++ tailWord_46255) baseStart_46255 baseEnd_46255 := by
    simpa [prefixWord, tailWord_46255, baseEnd_46255] using wordTrace_append hprefix tailTrace_46255
  have hstable : (prefixWord ++ tailWord_46255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46255).length < 2 ^ (prefixWord ++ tailWord_46255).sum := by decide
  have hdescent : baseEnd_46255 < baseStart_46255 := by decide
  rcases family_descends (prefixWord ++ tailWord_46255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46286 : List Nat := [4, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_46286 : Nat := 118140960795 + 46286 * 2 ^ 59
def prefixEnd_46286 : Nat := 4983230072969 + 3 ^ 40 * 46286 * 2
def baseEnd_46286 : Nat := 2640773952679015501349

theorem tailTrace_46286 : CollatzResearch.WordTrace tailWord_46286 prefixEnd_46286 2640773952679015501349 := by
  unfold tailWord_46286
  simp only [CollatzResearch.WordTrace]
  refine ⟨211023638790150233069839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1125459406880801243039141 211023638790150233069839)
  ·
    refine ⟨316535458185225349604759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211023638790150233069839 316535458185225349604759)
    ·
      refine ⟨474803187277838024407139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316535458185225349604759 474803187277838024407139)
      ·
        refine ⟨712204780916757036610709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474803187277838024407139 712204780916757036610709)
        ·
          refine ⟨33384599105472986091127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 712204780916757036610709 33384599105472986091127)
          ·
            refine ⟨50076898658209479136691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33384599105472986091127 50076898658209479136691)
            ·
              refine ⟨75115347987314218705037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50076898658209479136691 75115347987314218705037)
              ·
                refine ⟨28168255495242832014389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75115347987314218705037 28168255495242832014389)
                ·
                  refine ⟨2640773952679015501349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28168255495242832014389 2640773952679015501349)
                  ·
                    rfl

theorem cell23_46286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_46286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46286 prefixEnd_46286 := by exact prefixLift 46286
  have htrace : WordTrace (prefixWord ++ tailWord_46286) baseStart_46286 baseEnd_46286 := by
    simpa [prefixWord, tailWord_46286, baseEnd_46286] using wordTrace_append hprefix tailTrace_46286
  have hstable : (prefixWord ++ tailWord_46286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46286).length < 2 ^ (prefixWord ++ tailWord_46286).sum := by decide
  have hdescent : baseEnd_46286 < baseStart_46286 := by decide
  rcases family_descends (prefixWord ++ tailWord_46286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46295 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 5, 4]
def baseStart_46295 : Nat := 118140960795 + 46295 * 2 ^ 59
def prefixEnd_46295 : Nat := 4983230072969 + 3 ^ 40 * 46295 * 2
def baseEnd_46295 : Nat := 7923862300000534766533

theorem tailTrace_46295 : CollatzResearch.WordTrace tailWord_46295 prefixEnd_46295 7923862300000534766533 := by
  unfold tailWord_46295
  simp only [CollatzResearch.WordTrace]
  refine ⟨1688517367288596401636339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1125678244859064267757559 1688517367288596401636339)
  ·
    refine ⟨2532776050932894602454509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1688517367288596401636339 2532776050932894602454509)
    ·
      refine ⟨949791019099835475920441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2532776050932894602454509 949791019099835475920441)
      ·
        refine ⟨712343264324876606940331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 949791019099835475920441 712343264324876606940331)
        ·
          refine ⟨1068514896487314910410497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712343264324876606940331 1068514896487314910410497)
          ·
            refine ⟨801386172365486182807873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068514896487314910410497 801386172365486182807873)
            ·
              refine ⟨601039629274114637105905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801386172365486182807873 601039629274114637105905)
              ·
                refine ⟨450779721955585977829429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601039629274114637105905 450779721955585977829429)
                ·
                  refine ⟨42260598933336185421509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 450779721955585977829429 42260598933336185421509)
                  ·
                    refine ⟨7923862300000534766533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42260598933336185421509 7923862300000534766533)
                    ·
                      rfl

theorem cell23_46295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_46295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46295 prefixEnd_46295 := by exact prefixLift 46295
  have htrace : WordTrace (prefixWord ++ tailWord_46295) baseStart_46295 baseEnd_46295 := by
    simpa [prefixWord, tailWord_46295, baseEnd_46295] using wordTrace_append hprefix tailTrace_46295
  have hstable : (prefixWord ++ tailWord_46295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46295).length < 2 ^ (prefixWord ++ tailWord_46295).sum := by decide
  have hdescent : baseEnd_46295 < baseStart_46295 := by decide
  rcases family_descends (prefixWord ++ tailWord_46295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46390 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_46390 : Nat := 118140960795 + 46390 * 2 ^ 59
def prefixEnd_46390 : Nat := 4983230072969 + 3 ^ 40 * 46390 * 2
def baseEnd_46390 : Nat := 23820367562178732611663

theorem tailTrace_46390 : CollatzResearch.WordTrace tailWord_46390 prefixEnd_46390 23820367562178732611663 := by
  unfold tailWord_46390
  simp only [CollatzResearch.WordTrace]
  refine ⟨105748893871526726646539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1127988201296285084229749 105748893871526726646539)
  ·
    refine ⟨158623340807290089969809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105748893871526726646539 158623340807290089969809)
    ·
      refine ⟨118967505605467567477357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158623340807290089969809 118967505605467567477357)
      ·
        refine ⟨44612814602050337804009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118967505605467567477357 44612814602050337804009)
        ·
          refine ⟨33459610951537753353007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44612814602050337804009 33459610951537753353007)
          ·
            refine ⟨50189416427306630029511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33459610951537753353007 50189416427306630029511)
            ·
              refine ⟨75284124640959945044267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50189416427306630029511 75284124640959945044267)
              ·
                refine ⟨112926186961439917566401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75284124640959945044267 112926186961439917566401)
                ·
                  refine ⟨84694640221079938174801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112926186961439917566401 84694640221079938174801)
                  ·
                    refine ⟨63520980165809953631101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84694640221079938174801 63520980165809953631101)
                    ·
                      refine ⟨23820367562178732611663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 63520980165809953631101 23820367562178732611663)
                      ·
                        rfl

theorem cell23_46390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_46390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46390 prefixEnd_46390 := by exact prefixLift 46390
  have htrace : WordTrace (prefixWord ++ tailWord_46390) baseStart_46390 baseEnd_46390 := by
    simpa [prefixWord, tailWord_46390, baseEnd_46390] using wordTrace_append hprefix tailTrace_46390
  have hstable : (prefixWord ++ tailWord_46390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46390).length < 2 ^ (prefixWord ++ tailWord_46390).sum := by decide
  have hdescent : baseEnd_46390 < baseStart_46390 := by decide
  rcases family_descends (prefixWord ++ tailWord_46390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46392 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 1, 1, 4]
def baseStart_46392 : Nat := 118140960795 + 46392 * 2 ^ 59
def prefixEnd_46392 : Nat := 4983230072969 + 3 ^ 40 * 46392 * 2
def baseEnd_46392 : Nat := 23821394523487724786653

theorem tailTrace_46392 : CollatzResearch.WordTrace tailWord_46392 prefixEnd_46392 23821394523487724786653 := by
  unfold tailWord_46392
  simp only [CollatzResearch.WordTrace]
  refine ⟨846027623968590983958715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1128036831958121311944953 846027623968590983958715)
  ·
    refine ⟨1269041435952886475938073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 846027623968590983958715 1269041435952886475938073)
    ·
      refine ⟨951781076964664856953555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1269041435952886475938073 951781076964664856953555)
      ·
        refine ⟨1427671615446997285430333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951781076964664856953555 1427671615446997285430333)
        ·
          refine ⟨535376855792623982036375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1427671615446997285430333 535376855792623982036375)
          ·
            refine ⟨803065283688935973054563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535376855792623982036375 803065283688935973054563)
            ·
              refine ⟨1204597925533403959581845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803065283688935973054563 1204597925533403959581845)
              ·
                refine ⟨56465527759378310605399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1204597925533403959581845 56465527759378310605399)
                ·
                  refine ⟨84698291639067465908099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56465527759378310605399 84698291639067465908099)
                  ·
                    refine ⟨127047437458601198862149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84698291639067465908099 127047437458601198862149)
                    ·
                      refine ⟨23821394523487724786653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 127047437458601198862149 23821394523487724786653)
                      ·
                        rfl

theorem cell23_46392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_46392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46392 prefixEnd_46392 := by exact prefixLift 46392
  have htrace : WordTrace (prefixWord ++ tailWord_46392) baseStart_46392 baseEnd_46392 := by
    simpa [prefixWord, tailWord_46392, baseEnd_46392] using wordTrace_append hprefix tailTrace_46392
  have hstable : (prefixWord ++ tailWord_46392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46392).length < 2 ^ (prefixWord ++ tailWord_46392).sum := by decide
  have hdescent : baseEnd_46392 < baseStart_46392 := by decide
  rcases family_descends (prefixWord ++ tailWord_46392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46396 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 2, 3, 2]
def baseStart_46396 : Nat := 118140960795 + 46396 * 2 ^ 59
def prefixEnd_46396 : Nat := 4983230072969 + 3 ^ 40 * 46396 * 2
def baseEnd_46396 : Nat := 23823448446105709136635

theorem tailTrace_46396 : CollatzResearch.WordTrace tailWord_46396 prefixEnd_46396 23823448446105709136635 := by
  unfold tailWord_46396
  simp only [CollatzResearch.WordTrace]
  refine ⟨846100569961345325531521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1128134093281793767375361 846100569961345325531521)
  ·
    refine ⟨634575427471008994148641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 846100569961345325531521 634575427471008994148641)
    ·
      refine ⟨475931570603256745611481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 634575427471008994148641 475931570603256745611481)
      ·
        refine ⟨356948677952442559208611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475931570603256745611481 356948677952442559208611)
        ·
          refine ⟨535423016928663838812917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356948677952442559208611 535423016928663838812917)
          ·
            refine ⟨50195907837062234888711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 535423016928663838812917 50195907837062234888711)
            ·
              refine ⟨75293861755593352333067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50195907837062234888711 75293861755593352333067)
              ·
                refine ⟨112940792633390028499601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75293861755593352333067 112940792633390028499601)
                ·
                  refine ⟨84705594475042521374701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112940792633390028499601 84705594475042521374701)
                  ·
                    refine ⟨31764597928140945515513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84705594475042521374701 31764597928140945515513)
                    ·
                      refine ⟨23823448446105709136635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31764597928140945515513 23823448446105709136635)
                      ·
                        rfl

theorem cell23_46396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_46396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46396 prefixEnd_46396 := by exact prefixLift 46396
  have htrace : WordTrace (prefixWord ++ tailWord_46396) baseStart_46396 baseEnd_46396 := by
    simpa [prefixWord, tailWord_46396, baseEnd_46396] using wordTrace_append hprefix tailTrace_46396
  have hstable : (prefixWord ++ tailWord_46396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46396).length < 2 ^ (prefixWord ++ tailWord_46396).sum := by decide
  have hdescent : baseEnd_46396 < baseStart_46396 := by decide
  rcases family_descends (prefixWord ++ tailWord_46396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46409 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 1, 1, 4]
def baseStart_46409 : Nat := 118140960795 + 46409 * 2 ^ 59
def prefixEnd_46409 : Nat := 4983230072969 + 3 ^ 40 * 46409 * 2
def baseEnd_46409 : Nat := 23830123694614158274075

theorem tailTrace_46409 : CollatzResearch.WordTrace tailWord_46409 prefixEnd_46409 23830123694614158274075 := by
  unfold tailWord_46409
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692675288875593871286281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1128450192583729247524187 1692675288875593871286281)
  ·
    refine ⟨1269506466656695403464711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1692675288875593871286281 1269506466656695403464711)
    ·
      refine ⟨1904259699985043105197067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1269506466656695403464711 1904259699985043105197067)
      ·
        refine ⟨2856389549977564657795601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1904259699985043105197067 2856389549977564657795601)
        ·
          refine ⟨2142292162483173493346701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2856389549977564657795601 2142292162483173493346701)
          ·
            refine ⟨803359560931190060005013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2142292162483173493346701 803359560931190060005013)
            ·
              refine ⟨37657479418649534062735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 803359560931190060005013 37657479418649534062735)
              ·
                refine ⟨56486219127974301094103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37657479418649534062735 56486219127974301094103)
                ·
                  refine ⟨84729328691961451641155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56486219127974301094103 84729328691961451641155)
                  ·
                    refine ⟨127093993037942177461733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84729328691961451641155 127093993037942177461733)
                    ·
                      refine ⟨23830123694614158274075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 127093993037942177461733 23830123694614158274075)
                      ·
                        rfl

theorem cell23_46409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 1, 4].length) (baseStart_46409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46409 prefixEnd_46409 := by exact prefixLift 46409
  have htrace : WordTrace (prefixWord ++ tailWord_46409) baseStart_46409 baseEnd_46409 := by
    simpa [prefixWord, tailWord_46409, baseEnd_46409] using wordTrace_append hprefix tailTrace_46409
  have hstable : (prefixWord ++ tailWord_46409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46409).length < 2 ^ (prefixWord ++ tailWord_46409).sum := by decide
  have hdescent : baseEnd_46409 < baseStart_46409 := by decide
  rcases family_descends (prefixWord ++ tailWord_46409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46436 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_46436 : Nat := 118140960795 + 46436 * 2 ^ 59
def prefixEnd_46436 : Nat := 4983230072969 + 3 ^ 40 * 46436 * 2
def baseEnd_46436 : Nat := 7947995890761850878817

theorem tailTrace_46436 : CollatzResearch.WordTrace tailWord_46436 prefixEnd_46436 7947995890761850878817 := by
  unfold tailWord_46436
  simp only [CollatzResearch.WordTrace]
  refine ⟨846830029888888741259581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1129106706518518321679441 846830029888888741259581)
  ·
    refine ⟨317561261208333277972343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 846830029888888741259581 317561261208333277972343)
    ·
      refine ⟨476341891812499916958515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317561261208333277972343 476341891812499916958515)
      ·
        refine ⟨714512837718749875437773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476341891812499916958515 714512837718749875437773)
        ·
          refine ⟨267942314144531203289165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 714512837718749875437773 267942314144531203289165)
          ·
            refine ⟨100478367804199201233437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267942314144531203289165 100478367804199201233437)
            ·
              refine ⟨37679387926574700462539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100478367804199201233437 37679387926574700462539)
              ·
                refine ⟨56519081889862050693809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37679387926574700462539 56519081889862050693809)
                ·
                  refine ⟨42389311417396538020357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56519081889862050693809 42389311417396538020357)
                  ·
                    refine ⟨7947995890761850878817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42389311417396538020357 7947995890761850878817)
                    ·
                      rfl

theorem cell23_46436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_46436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46436 prefixEnd_46436 := by exact prefixLift 46436
  have htrace : WordTrace (prefixWord ++ tailWord_46436) baseStart_46436 baseEnd_46436 := by
    simpa [prefixWord, tailWord_46436, baseEnd_46436] using wordTrace_append hprefix tailTrace_46436
  have hstable : (prefixWord ++ tailWord_46436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46436).length < 2 ^ (prefixWord ++ tailWord_46436).sum := by decide
  have hdescent : baseEnd_46436 < baseStart_46436 := by decide
  rcases family_descends (prefixWord ++ tailWord_46436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46455 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_46455 : Nat := 118140960795 + 46455 * 2 ^ 59
def prefixEnd_46455 : Nat := 4983230072969 + 3 ^ 40 * 46455 * 2
def baseEnd_46455 : Nat := 23853743804720978298863

theorem tailTrace_46455 : CollatzResearch.WordTrace tailWord_46455 prefixEnd_46455 23853743804720978298863 := by
  unfold tailWord_46455
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694353046708943727460819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1129568697805962484973879 1694353046708943727460819)
  ·
    refine ⟨2541529570063415591191229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1694353046708943727460819 2541529570063415591191229)
    ·
      refine ⟨953073588773780846696711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2541529570063415591191229 953073588773780846696711)
      ·
        refine ⟨1429610383160671270045067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953073588773780846696711 1429610383160671270045067)
        ·
          refine ⟨2144415574741006905067601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429610383160671270045067 2144415574741006905067601)
          ·
            refine ⟨1608311681055755178800701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2144415574741006905067601 1608311681055755178800701)
            ·
              refine ⟨603116880395908192050263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1608311681055755178800701 603116880395908192050263)
              ·
                refine ⟨904675320593862288075395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603116880395908192050263 904675320593862288075395)
                ·
                  refine ⟨1357012980890793432113093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904675320593862288075395 1357012980890793432113093)
                  ·
                    refine ⟨254439933917023768521205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1357012980890793432113093 254439933917023768521205)
                    ·
                      refine ⟨23853743804720978298863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 254439933917023768521205 23853743804720978298863)
                      ·
                        rfl

theorem cell23_46455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_46455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46455 prefixEnd_46455 := by exact prefixLift 46455
  have htrace : WordTrace (prefixWord ++ tailWord_46455) baseStart_46455 baseEnd_46455 := by
    simpa [prefixWord, tailWord_46455, baseEnd_46455] using wordTrace_append hprefix tailTrace_46455
  have hstable : (prefixWord ++ tailWord_46455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46455).length < 2 ^ (prefixWord ++ tailWord_46455).sum := by decide
  have hdescent : baseEnd_46455 < baseStart_46455 := by decide
  rcases family_descends (prefixWord ++ tailWord_46455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46493 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_46493 : Nat := 118140960795 + 46493 * 2 ^ 59
def prefixEnd_46493 : Nat := 4983230072969 + 3 ^ 40 * 46493 * 2
def baseEnd_46493 : Nat := 23873256069591829623689

theorem tailTrace_46493 : CollatzResearch.WordTrace tailWord_46493 prefixEnd_46493 23873256069591829623689 := by
  unfold tailWord_46493
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695739020571276217344133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1130492680380850811562755 1695739020571276217344133)
  ·
    refine ⟨317951066357114290752025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1695739020571276217344133 317951066357114290752025)
    ·
      refine ⟨238463299767835718064019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317951066357114290752025 238463299767835718064019)
      ·
        refine ⟨357694949651753577096029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238463299767835718064019 357694949651753577096029)
        ·
          refine ⟨134135606119407591411011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357694949651753577096029 134135606119407591411011)
          ·
            refine ⟨201203409179111387116517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134135606119407591411011 201203409179111387116517)
            ·
              refine ⟨37725639221083385084347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201203409179111387116517 37725639221083385084347)
              ·
                refine ⟨56588458831625077626521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37725639221083385084347 56588458831625077626521)
                ·
                  refine ⟨42441344123718808219891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56588458831625077626521 42441344123718808219891)
                  ·
                    refine ⟨63662016185578212329837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42441344123718808219891 63662016185578212329837)
                    ·
                      refine ⟨23873256069591829623689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 63662016185578212329837 23873256069591829623689)
                      ·
                        rfl

theorem cell23_46493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_46493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46493 prefixEnd_46493 := by exact prefixLift 46493
  have htrace : WordTrace (prefixWord ++ tailWord_46493) baseStart_46493 baseEnd_46493 := by
    simpa [prefixWord, tailWord_46493, baseEnd_46493] using wordTrace_append hprefix tailTrace_46493
  have hstable : (prefixWord ++ tailWord_46493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46493).length < 2 ^ (prefixWord ++ tailWord_46493).sum := by decide
  have hdescent : baseEnd_46493 < baseStart_46493 := by decide
  rcases family_descends (prefixWord ++ tailWord_46493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46499 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 1, 4, 2]
def baseStart_46499 : Nat := 118140960795 + 46499 * 2 ^ 59
def prefixEnd_46499 : Nat := 4983230072969 + 3 ^ 40 * 46499 * 2
def baseEnd_46499 : Nat := 23876336953518806148661

theorem tailTrace_46499 : CollatzResearch.WordTrace tailWord_46499 prefixEnd_46499 23876336953518806148661 := by
  unfold tailWord_46499
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695957858549539242062551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1130638572366359494708367 1695957858549539242062551)
  ·
    refine ⟨2543936787824308863093827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1695957858549539242062551 2543936787824308863093827)
    ·
      refine ⟨3815905181736463294640741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2543936787824308863093827 3815905181736463294640741)
      ·
        refine ⟨715482221575586867745139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3815905181736463294640741 715482221575586867745139)
        ·
          refine ⟨1073223332363380301617709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715482221575586867745139 1073223332363380301617709)
          ·
            refine ⟨402458749636267613106641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1073223332363380301617709 402458749636267613106641)
            ·
              refine ⟨301844062227200709829981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402458749636267613106641 301844062227200709829981)
              ·
                refine ⟨113191523335200266186243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301844062227200709829981 113191523335200266186243)
                ·
                  refine ⟨169787285002800399279365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113191523335200266186243 169787285002800399279365)
                  ·
                    refine ⟨31835115938025074864881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169787285002800399279365 31835115938025074864881)
                    ·
                      refine ⟨23876336953518806148661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31835115938025074864881 23876336953518806148661)
                      ·
                        rfl

theorem cell23_46499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_46499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46499 prefixEnd_46499 := by exact prefixLift 46499
  have htrace : WordTrace (prefixWord ++ tailWord_46499) baseStart_46499 baseEnd_46499 := by
    simpa [prefixWord, tailWord_46499, baseEnd_46499] using wordTrace_append hprefix tailTrace_46499
  have hstable : (prefixWord ++ tailWord_46499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46499).length < 2 ^ (prefixWord ++ tailWord_46499).sum := by decide
  have hdescent : baseEnd_46499 < baseStart_46499 := by decide
  rcases family_descends (prefixWord ++ tailWord_46499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46549 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_46549 : Nat := 118140960795 + 46549 * 2 ^ 59
def prefixEnd_46549 : Nat := 4983230072969 + 3 ^ 40 * 46549 * 2
def baseEnd_46549 : Nat := 23902010986243610523431

theorem tailTrace_46549 : CollatzResearch.WordTrace tailWord_46549 prefixEnd_46549 23902010986243610523431 := by
  unfold tailWord_46549
  simp only [CollatzResearch.WordTrace]
  refine ⟨1697781508368397781382701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1131854338912265187588467 1697781508368397781382701)
  ·
    refine ⟨636668065638149168018513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1697781508368397781382701 636668065638149168018513)
    ·
      refine ⟨477501049228611876013885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 636668065638149168018513 477501049228611876013885)
      ·
        refine ⟨179062893460729453505207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477501049228611876013885 179062893460729453505207)
        ·
          refine ⟨268594340191094180257811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179062893460729453505207 268594340191094180257811)
          ·
            refine ⟨402891510286641270386717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268594340191094180257811 402891510286641270386717)
            ·
              refine ⟨151084316357490476395019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 402891510286641270386717 151084316357490476395019)
              ·
                refine ⟨226626474536235714592529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151084316357490476395019 226626474536235714592529)
                ·
                  refine ⟨169969855902176785944397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226626474536235714592529 169969855902176785944397)
                  ·
                    refine ⟨63738695963316294729149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169969855902176785944397 63738695963316294729149)
                    ·
                      refine ⟨23902010986243610523431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 63738695963316294729149 23902010986243610523431)
                      ·
                        rfl

theorem cell23_46549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_46549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46549 prefixEnd_46549 := by exact prefixLift 46549
  have htrace : WordTrace (prefixWord ++ tailWord_46549) baseStart_46549 baseEnd_46549 := by
    simpa [prefixWord, tailWord_46549, baseEnd_46549] using wordTrace_append hprefix tailTrace_46549
  have hstable : (prefixWord ++ tailWord_46549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46549).length < 2 ^ (prefixWord ++ tailWord_46549).sum := by decide
  have hdescent : baseEnd_46549 < baseStart_46549 := by decide
  rcases family_descends (prefixWord ++ tailWord_46549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46550 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_46550 : Nat := 118140960795 + 46550 * 2 ^ 59
def prefixEnd_46550 : Nat := 4983230072969 + 3 ^ 40 * 46550 * 2
def baseEnd_46550 : Nat := 23902524466898106610927

theorem tailTrace_46550 : CollatzResearch.WordTrace tailWord_46550 prefixEnd_46550 23902524466898106610927 := by
  unfold tailWord_46550
  simp only [CollatzResearch.WordTrace]
  refine ⟨106113623835298434510569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1131878654243183301446069 106113623835298434510569)
  ·
    refine ⟨79585217876473825882927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106113623835298434510569 79585217876473825882927)
    ·
      refine ⟨119377826814710738824391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79585217876473825882927 119377826814710738824391)
      ·
        refine ⟨179066740222066108236587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119377826814710738824391 179066740222066108236587)
        ·
          refine ⟨268600110333099162354881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179066740222066108236587 268600110333099162354881)
          ·
            refine ⟨201450082749824371766161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268600110333099162354881 201450082749824371766161)
            ·
              refine ⟨151087562062368278824621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201450082749824371766161 151087562062368278824621)
              ·
                refine ⟨56657835773388104559233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151087562062368278824621 56657835773388104559233)
                ·
                  refine ⟨42493376830041078419425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56657835773388104559233 42493376830041078419425)
                  ·
                    refine ⟨31870032622530808814569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42493376830041078419425 31870032622530808814569)
                    ·
                      refine ⟨23902524466898106610927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31870032622530808814569 23902524466898106610927)
                      ·
                        rfl

theorem cell23_46550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_46550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46550 prefixEnd_46550 := by exact prefixLift 46550
  have htrace : WordTrace (prefixWord ++ tailWord_46550) baseStart_46550 baseEnd_46550 := by
    simpa [prefixWord, tailWord_46550, baseEnd_46550] using wordTrace_append hprefix tailTrace_46550
  have hstable : (prefixWord ++ tailWord_46550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46550).length < 2 ^ (prefixWord ++ tailWord_46550).sum := by decide
  have hdescent : baseEnd_46550 < baseStart_46550 := by decide
  rcases family_descends (prefixWord ++ tailWord_46550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46552 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 4, 5]
def baseStart_46552 : Nat := 118140960795 + 46552 * 2 ^ 59
def prefixEnd_46552 : Nat := 4983230072969 + 3 ^ 40 * 46552 * 2
def baseEnd_46552 : Nat := 7967850476069032928639

theorem tailTrace_46552 : CollatzResearch.WordTrace tailWord_46552 prefixEnd_46552 7967850476069032928639 := by
  unfold tailWord_46552
  simp only [CollatzResearch.WordTrace]
  refine ⟨848945463678764646870955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1131927284905019529161273 848945463678764646870955)
  ·
    refine ⟨1273418195518146970306433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 848945463678764646870955 1273418195518146970306433)
    ·
      refine ⟨955063646638610227729825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1273418195518146970306433 955063646638610227729825)
      ·
        refine ⟨716297734978957670797369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 955063646638610227729825 716297734978957670797369)
        ·
          refine ⟨537223301234218253098027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716297734978957670797369 537223301234218253098027)
          ·
            refine ⟨805834951851327379647041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537223301234218253098027 805834951851327379647041)
            ·
              refine ⟨604376213888495534735281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805834951851327379647041 604376213888495534735281)
              ·
                refine ⟨453282160416371651051461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604376213888495534735281 453282160416371651051461)
                ·
                  refine ⟨84990405078069684572149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453282160416371651051461 84990405078069684572149)
                  ·
                    refine ⟨7967850476069032928639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84990405078069684572149 7967850476069032928639)
                    ·
                      rfl

theorem cell23_46552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_46552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46552 prefixEnd_46552 := by exact prefixLift 46552
  have htrace : WordTrace (prefixWord ++ tailWord_46552) baseStart_46552 baseEnd_46552 := by
    simpa [prefixWord, tailWord_46552, baseEnd_46552] using wordTrace_append hprefix tailTrace_46552
  have hstable : (prefixWord ++ tailWord_46552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46552).length < 2 ^ (prefixWord ++ tailWord_46552).sum := by decide
  have hdescent : baseEnd_46552 < baseStart_46552 := by decide
  rcases family_descends (prefixWord ++ tailWord_46552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46559 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 2, 5, 2]
def baseStart_46559 : Nat := 118140960795 + 46559 * 2 ^ 59
def prefixEnd_46559 : Nat := 4983230072969 + 3 ^ 40 * 46559 * 2
def baseEnd_46559 : Nat := 23907145792788571398385

theorem tailTrace_46559 : CollatzResearch.WordTrace tailWord_46559 prefixEnd_46559 23907145792788571398385 := by
  unfold tailWord_46559
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698146238332169489246731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1132097492221446326164487 1698146238332169489246731)
  ·
    refine ⟨2547219357498254233870097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1698146238332169489246731 2547219357498254233870097)
    ·
      refine ⟨1910414518123690675402573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2547219357498254233870097 1910414518123690675402573)
      ·
        refine ⟨716405444296384003275965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1910414518123690675402573 716405444296384003275965)
        ·
          refine ⟨268652041611144001228487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 716405444296384003275965 268652041611144001228487)
          ·
            refine ⟨402978062416716001842731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268652041611144001228487 402978062416716001842731)
            ·
              refine ⟨604467093625074002764097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402978062416716001842731 604467093625074002764097)
              ·
                refine ⟨453350320218805502073073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604467093625074002764097 453350320218805502073073)
                ·
                  refine ⟨340012740164104126554805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453350320218805502073073 340012740164104126554805)
                  ·
                    refine ⟨31876194390384761864513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 340012740164104126554805 31876194390384761864513)
                    ·
                      refine ⟨23907145792788571398385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31876194390384761864513 23907145792788571398385)
                      ·
                        rfl

theorem cell23_46559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_46559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46559 prefixEnd_46559 := by exact prefixLift 46559
  have htrace : WordTrace (prefixWord ++ tailWord_46559) baseStart_46559 baseEnd_46559 := by
    simpa [prefixWord, tailWord_46559, baseEnd_46559] using wordTrace_append hprefix tailTrace_46559
  have hstable : (prefixWord ++ tailWord_46559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46559).length < 2 ^ (prefixWord ++ tailWord_46559).sum := by decide
  have hdescent : baseEnd_46559 < baseStart_46559 := by decide
  rcases family_descends (prefixWord ++ tailWord_46559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46573 : List Nat := [1, 5, 1, 3, 2, 1, 2, 3, 5]
def baseStart_46573 : Nat := 118140960795 + 46573 * 2 ^ 59
def prefixEnd_46573 : Nat := 4983230072969 + 3 ^ 40 * 46573 * 2
def baseEnd_46573 : Nat := 2657148280216835180369

theorem tailTrace_46573 : CollatzResearch.WordTrace tailWord_46573 prefixEnd_46573 2657148280216835180369 := by
  unfold tailWord_46573
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698656860281449880256373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1132437906854299920170915 1698656860281449880256373)
  ·
    refine ⟨159249080651385926274035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1698656860281449880256373 159249080651385926274035)
    ·
      refine ⟨238873620977078889411053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159249080651385926274035 238873620977078889411053)
      ·
        refine ⟨89577607866404583529145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238873620977078889411053 89577607866404583529145)
        ·
          refine ⟨67183205899803437646859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89577607866404583529145 67183205899803437646859)
          ·
            refine ⟨100774808849705156470289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67183205899803437646859 100774808849705156470289)
            ·
              refine ⟨75581106637278867352717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100774808849705156470289 75581106637278867352717)
              ·
                refine ⟨28342914988979575257269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75581106637278867352717 28342914988979575257269)
                ·
                  refine ⟨2657148280216835180369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28342914988979575257269 2657148280216835180369)
                  ·
                    rfl

theorem cell23_46573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_46573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46573 prefixEnd_46573 := by exact prefixLift 46573
  have htrace : WordTrace (prefixWord ++ tailWord_46573) baseStart_46573 baseEnd_46573 := by
    simpa [prefixWord, tailWord_46573, baseEnd_46573] using wordTrace_append hprefix tailTrace_46573
  have hstable : (prefixWord ++ tailWord_46573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46573).length < 2 ^ (prefixWord ++ tailWord_46573).sum := by decide
  have hdescent : baseEnd_46573 < baseStart_46573 := by decide
  rcases family_descends (prefixWord ++ tailWord_46573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46663 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 6]
def baseStart_46663 : Nat := 118140960795 + 46663 * 2 ^ 59
def prefixEnd_46663 : Nat := 4983230072969 + 3 ^ 40 * 46663 * 2
def baseEnd_46663 : Nat := 2662283086761796055323

theorem tailTrace_46663 : CollatzResearch.WordTrace tailWord_46663 prefixEnd_46663 2662283086761796055323 := by
  unfold tailWord_46663
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701939429955395251032643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1134626286636930167355095 1701939429955395251032643)
  ·
    refine ⟨2552909144933092876548965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1701939429955395251032643 2552909144933092876548965)
    ·
      refine ⟨478670464674954914352931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2552909144933092876548965 478670464674954914352931)
      ·
        refine ⟨718005697012432371529397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478670464674954914352931 718005697012432371529397)
        ·
          refine ⟨67313034094915534830881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 718005697012432371529397 67313034094915534830881)
          ·
            refine ⟨50484775571186651123161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67313034094915534830881 50484775571186651123161)
            ·
              refine ⟨37863581678389988342371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50484775571186651123161 37863581678389988342371)
              ·
                refine ⟨56795372517584982513557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37863581678389988342371 56795372517584982513557)
                ·
                  refine ⟨2662283086761796055323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56795372517584982513557 2662283086761796055323)
                  ·
                    rfl

theorem cell23_46663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 6].length) (baseStart_46663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46663 prefixEnd_46663 := by exact prefixLift 46663
  have htrace : WordTrace (prefixWord ++ tailWord_46663) baseStart_46663 baseEnd_46663 := by
    simpa [prefixWord, tailWord_46663, baseEnd_46663] using wordTrace_append hprefix tailTrace_46663
  have hstable : (prefixWord ++ tailWord_46663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46663).length < 2 ^ (prefixWord ++ tailWord_46663).sum := by decide
  have hdescent : baseEnd_46663 < baseStart_46663 := by decide
  rcases family_descends (prefixWord ++ tailWord_46663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46666 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2]
def baseStart_46666 : Nat := 118140960795 + 46666 * 2 ^ 59
def prefixEnd_46666 : Nat := 4983230072969 + 3 ^ 40 * 46666 * 2
def baseEnd_46666 : Nat := 23962088222819652760393

theorem tailTrace_46666 : CollatzResearch.WordTrace tailWord_46666 prefixEnd_46666 23962088222819652760393 := by
  unfold tailWord_46666
  simp only [CollatzResearch.WordTrace]
  refine ⟨425512212236131690847963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1134699232629684508927901 425512212236131690847963)
  ·
    refine ⟨638268318354197536271945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425512212236131690847963 638268318354197536271945)
    ·
      refine ⟨478701238765648152203959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 638268318354197536271945 478701238765648152203959)
      ·
        refine ⟨718051858148472228305939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478701238765648152203959 718051858148472228305939)
        ·
          refine ⟨1077077787222708342458909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718051858148472228305939 1077077787222708342458909)
          ·
            refine ⟨403904170208515628422091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1077077787222708342458909 403904170208515628422091)
            ·
              refine ⟨605856255312773442633137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403904170208515628422091 605856255312773442633137)
              ·
                refine ⟨454392191484580081974853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605856255312773442633137 454392191484580081974853)
                ·
                  refine ⟨85198535903358765370285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454392191484580081974853 85198535903358765370285)
                  ·
                    refine ⟨31949450963759537013857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85198535903358765370285 31949450963759537013857)
                    ·
                      refine ⟨23962088222819652760393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31949450963759537013857 23962088222819652760393)
                      ·
                        rfl

theorem cell23_46666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_46666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46666 prefixEnd_46666 := by exact prefixLift 46666
  have htrace : WordTrace (prefixWord ++ tailWord_46666) baseStart_46666 baseEnd_46666 := by
    simpa [prefixWord, tailWord_46666, baseEnd_46666] using wordTrace_append hprefix tailTrace_46666
  have hstable : (prefixWord ++ tailWord_46666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46666).length < 2 ^ (prefixWord ++ tailWord_46666).sum := by decide
  have hdescent : baseEnd_46666 < baseStart_46666 := by decide
  rcases family_descends (prefixWord ++ tailWord_46666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46689 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 1, 6]
def baseStart_46689 : Nat := 118140960795 + 46689 * 2 ^ 59
def prefixEnd_46689 : Nat := 4983230072969 + 3 ^ 40 * 46689 * 2
def baseEnd_46689 : Nat := 7991299425957687590929

theorem tailTrace_46689 : CollatzResearch.WordTrace tailWord_46689 prefixEnd_46689 7991299425957687590929 := by
  unfold tailWord_46689
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702887727861201691479121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1135258485240801127652747 1702887727861201691479121)
  ·
    refine ⟨1277165795895901268609341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1702887727861201691479121 1277165795895901268609341)
    ·
      refine ⟨478937173460962975728503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1277165795895901268609341 478937173460962975728503)
      ·
        refine ⟨718405760191444463592755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478937173460962975728503 718405760191444463592755)
        ·
          refine ⟨1077608640287166695389133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718405760191444463592755 1077608640287166695389133)
          ·
            refine ⟨404103240107687510770925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1077608640287166695389133 404103240107687510770925)
            ·
              refine ⟨151538715040382816539097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404103240107687510770925 151538715040382816539097)
              ·
                refine ⟨113654036280287112404323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151538715040382816539097 113654036280287112404323)
                ·
                  refine ⟨170481054420430668606485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113654036280287112404323 170481054420430668606485)
                  ·
                    refine ⟨7991299425957687590929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 170481054420430668606485 7991299425957687590929)
                    ·
                      rfl

theorem cell23_46689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_46689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46689 prefixEnd_46689 := by exact prefixLift 46689
  have htrace : WordTrace (prefixWord ++ tailWord_46689) baseStart_46689 baseEnd_46689 := by
    simpa [prefixWord, tailWord_46689, baseEnd_46689] using wordTrace_append hprefix tailTrace_46689
  have hstable : (prefixWord ++ tailWord_46689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46689).length < 2 ^ (prefixWord ++ tailWord_46689).sum := by decide
  have hdescent : baseEnd_46689 < baseStart_46689 := by decide
  rcases family_descends (prefixWord ++ tailWord_46689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46693 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 1, 5]
def baseStart_46693 : Nat := 118140960795 + 46693 * 2 ^ 59
def prefixEnd_46693 : Nat := 4983230072969 + 3 ^ 40 * 46693 * 2
def baseEnd_46693 : Nat := 7991984066830349040923

theorem tailTrace_46693 : CollatzResearch.WordTrace tailWord_46693 prefixEnd_46693 7991984066830349040923 := by
  unfold tailWord_46693
  simp only [CollatzResearch.WordTrace]
  refine ⟨1703033619846710374624733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1135355746564473583083155 1703033619846710374624733)
  ·
    refine ⟨638637607442516390484275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1703033619846710374624733 638637607442516390484275)
    ·
      refine ⟨957956411163774585726413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638637607442516390484275 957956411163774585726413)
      ·
        refine ⟨359233654186415469647405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 957956411163774585726413 359233654186415469647405)
        ·
          refine ⟨134712620319905801117777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359233654186415469647405 134712620319905801117777)
          ·
            refine ⟨101034465239929350838333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134712620319905801117777 101034465239929350838333)
            ·
              refine ⟨37887924464973506564375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101034465239929350838333 37887924464973506564375)
              ·
                refine ⟨56831886697460259846563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37887924464973506564375 56831886697460259846563)
                ·
                  refine ⟨85247830046190389769845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56831886697460259846563 85247830046190389769845)
                  ·
                    refine ⟨7991984066830349040923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85247830046190389769845 7991984066830349040923)
                    ·
                      rfl

theorem cell23_46693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_46693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46693 prefixEnd_46693 := by exact prefixLift 46693
  have htrace : WordTrace (prefixWord ++ tailWord_46693) baseStart_46693 baseEnd_46693 := by
    simpa [prefixWord, tailWord_46693, baseEnd_46693] using wordTrace_append hprefix tailTrace_46693
  have hstable : (prefixWord ++ tailWord_46693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46693).length < 2 ^ (prefixWord ++ tailWord_46693).sum := by decide
  have hdescent : baseEnd_46693 < baseStart_46693 := by decide
  rcases family_descends (prefixWord ++ tailWord_46693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46713 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 3, 2, 2]
def baseStart_46713 : Nat := 118140960795 + 46713 * 2 ^ 59
def prefixEnd_46713 : Nat := 4983230072969 + 3 ^ 40 * 46713 * 2
def baseEnd_46713 : Nat := 23986221813580968872677

theorem tailTrace_46713 : CollatzResearch.WordTrace tailWord_46713 prefixEnd_46713 23986221813580968872677 := by
  unfold tailWord_46713
  simp only [CollatzResearch.WordTrace]
  refine ⟨1703763079774253790352793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1135842053182835860235195 1703763079774253790352793)
  ·
    refine ⟨1277822309830690342764595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1703763079774253790352793 1277822309830690342764595)
    ·
      refine ⟨1916733464746035514146893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1277822309830690342764595 1916733464746035514146893)
      ·
        refine ⟨718775049279763317805085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1916733464746035514146893 718775049279763317805085)
        ·
          refine ⟨269540643479911244176907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 718775049279763317805085 269540643479911244176907)
          ·
            refine ⟨404310965219866866265361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269540643479911244176907 404310965219866866265361)
            ·
              refine ⟨303233223914900149699021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404310965219866866265361 303233223914900149699021)
              ·
                refine ⟨113712458968087556137133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303233223914900149699021 113712458968087556137133)
                ·
                  refine ⟨42642172113032833551425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113712458968087556137133 42642172113032833551425)
                  ·
                    refine ⟨31981629084774625163569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42642172113032833551425 31981629084774625163569)
                    ·
                      refine ⟨23986221813580968872677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 31981629084774625163569 23986221813580968872677)
                      ·
                        rfl

theorem cell23_46713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_46713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_46713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_46713 prefixEnd_46713 := by exact prefixLift 46713
  have htrace : WordTrace (prefixWord ++ tailWord_46713) baseStart_46713 baseEnd_46713 := by
    simpa [prefixWord, tailWord_46713, baseEnd_46713] using wordTrace_append hprefix tailTrace_46713
  have hstable : (prefixWord ++ tailWord_46713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46713).length < 2 ^ (prefixWord ++ tailWord_46713).sum := by decide
  have hdescent : baseEnd_46713 < baseStart_46713 := by decide
  rcases family_descends (prefixWord ++ tailWord_46713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
