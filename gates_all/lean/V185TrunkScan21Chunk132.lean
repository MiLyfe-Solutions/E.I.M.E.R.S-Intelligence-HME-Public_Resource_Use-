import V185TrunkScan21Chunk131

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1607661 : List Nat := [1, 5, 1, 4, 2, 1, 1, 3, 3]
def baseStart_1607661 : Nat := 118140960795 + 1607661 * 2 ^ 59
def prefixEnd_1607661 : Nat := 4983230072969 + 3 ^ 40 * 1607661 * 2
def baseEnd_1607661 : Nat := 366890143327973223397337

theorem tailTrace_1607661 : CollatzResearch.WordTrace tailWord_1607661 prefixEnd_1607661 366890143327973223397337 := by
  unfold tailWord_1607661
  simp only [CollatzResearch.WordTrace]
  refine ⟨58636213828726238484542837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39090809219150825656361891 58636213828726238484542837)
  ·
    refine ⟨5497145046443084857925891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58636213828726238484542837 5497145046443084857925891)
    ·
      refine ⟨8245717569664627286888837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5497145046443084857925891 8245717569664627286888837)
      ·
        refine ⟨1546072044312117616291657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8245717569664627286888837 1546072044312117616291657)
        ·
          refine ⟨1159554033234088212218743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1546072044312117616291657 1159554033234088212218743)
          ·
            refine ⟨1739331049851132318328115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159554033234088212218743 1739331049851132318328115)
            ·
              refine ⟨2608996574776698477492173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739331049851132318328115 2608996574776698477492173)
              ·
                refine ⟨978373715541261929059565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2608996574776698477492173 978373715541261929059565)
                ·
                  refine ⟨366890143327973223397337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978373715541261929059565 366890143327973223397337)
                  ·
                    rfl

theorem cell21_1607661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_1607661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607661 prefixEnd_1607661 := by exact prefixLift 1607661
  have htrace : WordTrace (prefixWord ++ tailWord_1607661) baseStart_1607661 baseEnd_1607661 := by
    simpa [prefixWord, tailWord_1607661, baseEnd_1607661] using wordTrace_append hprefix tailTrace_1607661
  have hstable : (prefixWord ++ tailWord_1607661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607661).length < 2 ^ (prefixWord ++ tailWord_1607661).sum := by decide
  have hdescent : baseEnd_1607661 < baseStart_1607661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607804 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_1607804 : Nat := 118140960795 + 1607804 * 2 ^ 59
def prefixEnd_1607804 : Nat := 4983230072969 + 3 ^ 40 * 1607804 * 2
def baseEnd_1607804 : Nat := 366922777876236752513711

theorem tailTrace_1607804 : CollatzResearch.WordTrace tailWord_1607804 prefixEnd_1607804 366922777876236752513711 := by
  unfold tailWord_1607804
  simp only [CollatzResearch.WordTrace]
  refine ⟨29320714733604086953499233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39094286311472115937998977 29320714733604086953499233)
  ·
    refine ⟨21990536050203065215124425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29320714733604086953499233 21990536050203065215124425)
    ·
      refine ⟨16492902037652298911343319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21990536050203065215124425 16492902037652298911343319)
      ·
        refine ⟨24739353056478448367014979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16492902037652298911343319 24739353056478448367014979)
        ·
          refine ⟨37109029584717672550522469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24739353056478448367014979 37109029584717672550522469)
          ·
            refine ⟨6957943047134563603222963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37109029584717672550522469 6957943047134563603222963)
            ·
              refine ⟨10436914570701845404834445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957943047134563603222963 10436914570701845404834445)
              ·
                refine ⟨3913842964013192026812917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10436914570701845404834445 3913842964013192026812917)
                ·
                  refine ⟨366922777876236752513711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3913842964013192026812917 366922777876236752513711)
                  ·
                    rfl

theorem cell21_1607804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_1607804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607804 prefixEnd_1607804 := by exact prefixLift 1607804
  have htrace : WordTrace (prefixWord ++ tailWord_1607804) baseStart_1607804 baseEnd_1607804 := by
    simpa [prefixWord, tailWord_1607804, baseEnd_1607804] using wordTrace_append hprefix tailTrace_1607804
  have hstable : (prefixWord ++ tailWord_1607804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607804).length < 2 ^ (prefixWord ++ tailWord_1607804).sum := by decide
  have hdescent : baseEnd_1607804 < baseStart_1607804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607906 : List Nat := [3, 3, 4, 1, 1, 2, 2, 2, 3]
def baseStart_1607906 : Nat := 118140960795 + 1607906 * 2 ^ 59
def prefixEnd_1607906 : Nat := 4983230072969 + 3 ^ 40 * 1607906 * 2
def baseEnd_1607906 : Nat := 366946055665907241813503

theorem tailTrace_1607906 : CollatzResearch.WordTrace tailWord_1607906 prefixEnd_1607906 366946055665907241813503 := by
  unfold tailWord_1607906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661287428209661331802893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39096766475225763551474381 14661287428209661331802893)
  ·
    refine ⟨5497982785578622999426085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14661287428209661331802893 5497982785578622999426085)
    ·
      refine ⟨1030871772295991812392391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5497982785578622999426085 1030871772295991812392391)
      ·
        refine ⟨1546307658443987718588587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030871772295991812392391 1546307658443987718588587)
        ·
          refine ⟨2319461487665981577882881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546307658443987718588587 2319461487665981577882881)
          ·
            refine ⟨1739596115749486183412161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2319461487665981577882881 1739596115749486183412161)
            ·
              refine ⟨1304697086812114637559121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1739596115749486183412161 1304697086812114637559121)
              ·
                refine ⟨978522815109085978169341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304697086812114637559121 978522815109085978169341)
                ·
                  refine ⟨366946055665907241813503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978522815109085978169341 366946055665907241813503)
                  ·
                    rfl

theorem cell21_1607906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_1607906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607906 prefixEnd_1607906 := by exact prefixLift 1607906
  have htrace : WordTrace (prefixWord ++ tailWord_1607906) baseStart_1607906 baseEnd_1607906 := by
    simpa [prefixWord, tailWord_1607906, baseEnd_1607906] using wordTrace_append hprefix tailTrace_1607906
  have hstable : (prefixWord ++ tailWord_1607906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607906).length < 2 ^ (prefixWord ++ tailWord_1607906).sum := by decide
  have hdescent : baseEnd_1607906 < baseStart_1607906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607973 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 5]
def baseStart_1607973 : Nat := 118140960795 + 1607973 * 2 ^ 59
def prefixEnd_1607973 : Nat := 4983230072969 + 3 ^ 40 * 1607973 * 2
def baseEnd_1607973 : Nat := 366961345978730014196699

theorem tailTrace_1607973 : CollatzResearch.WordTrace tailWord_1607973 prefixEnd_1607973 366961345978730014196699 := by
  unfold tailWord_1607973
  simp only [CollatzResearch.WordTrace]
  refine ⟨58647593403595915769900573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39098395602397277179933715 58647593403595915769900573)
  ·
    refine ⟨21992847526348468413712715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58647593403595915769900573 21992847526348468413712715)
    ·
      refine ⟨32989271289522702620569073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21992847526348468413712715 32989271289522702620569073)
      ·
        refine ⟨24741953467142026965426805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32989271289522702620569073 24741953467142026965426805)
        ·
          refine ⟨2319558137544565028008763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24741953467142026965426805 2319558137544565028008763)
          ·
            refine ⟨3479337206316847542013145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319558137544565028008763 3479337206316847542013145)
            ·
              refine ⟨2609502904737635656509859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3479337206316847542013145 2609502904737635656509859)
              ·
                refine ⟨3914254357106453484764789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2609502904737635656509859 3914254357106453484764789)
                ·
                  refine ⟨366961345978730014196699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3914254357106453484764789 366961345978730014196699)
                  ·
                    rfl

theorem cell21_1607973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_1607973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1607973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1607973 prefixEnd_1607973 := by exact prefixLift 1607973
  have htrace : WordTrace (prefixWord ++ tailWord_1607973) baseStart_1607973 baseEnd_1607973 := by
    simpa [prefixWord, tailWord_1607973, baseEnd_1607973] using wordTrace_append hprefix tailTrace_1607973
  have hstable : (prefixWord ++ tailWord_1607973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607973).length < 2 ^ (prefixWord ++ tailWord_1607973).sum := by decide
  have hdescent : baseEnd_1607973 < baseStart_1607973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608086 : List Nat := [5, 3, 1, 2, 2, 1, 1, 6]
def baseStart_1608086 : Nat := 118140960795 + 1608086 * 2 ^ 59
def prefixEnd_1608086 : Nat := 4983230072969 + 3 ^ 40 * 1608086 * 2
def baseEnd_1608086 : Nat := 122329044706088976271045

theorem tailTrace_1608086 : CollatzResearch.WordTrace tailWord_1608086 prefixEnd_1608086 122329044706088976271045 := by
  unfold tailWord_1608086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3665732178261658504297757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39101143234791024045842741 3665732178261658504297757)
  ·
    refine ⟨1374649566848121939111659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3665732178261658504297757 1374649566848121939111659)
    ·
      refine ⟨2061974350272182908667489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1374649566848121939111659 2061974350272182908667489)
      ·
        refine ⟨1546480762704137181500617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2061974350272182908667489 1546480762704137181500617)
        ·
          refine ⟨1159860572028102886125463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1546480762704137181500617 1159860572028102886125463)
          ·
            refine ⟨1739790858042154329188195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159860572028102886125463 1739790858042154329188195)
            ·
              refine ⟨2609686287063231493782293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739790858042154329188195 2609686287063231493782293)
              ·
                refine ⟨122329044706088976271045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2609686287063231493782293 122329044706088976271045)
                ·
                  rfl

theorem cell21_1608086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_1608086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608086 prefixEnd_1608086 := by exact prefixLift 1608086
  have htrace : WordTrace (prefixWord ++ tailWord_1608086) baseStart_1608086 baseEnd_1608086 := by
    simpa [prefixWord, tailWord_1608086, baseEnd_1608086] using wordTrace_append hprefix tailTrace_1608086
  have hstable : (prefixWord ++ tailWord_1608086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608086).length < 2 ^ (prefixWord ++ tailWord_1608086).sum := by decide
  have hdescent : baseEnd_1608086 < baseStart_1608086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608125 : List Nat := [1, 4, 1, 2, 2, 2, 1, 5, 3]
def baseStart_1608125 : Nat := 118140960795 + 1608125 * 2 ^ 59
def prefixEnd_1608125 : Nat := 4983230072969 + 3 ^ 40 * 1608125 * 2
def baseEnd_1608125 : Nat := 366996034449611527663055

theorem tailTrace_1608125 : CollatzResearch.WordTrace tailWord_1608125 prefixEnd_1608125 366996034449611527663055 := by
  unfold tailWord_1608125
  simp only [CollatzResearch.WordTrace]
  refine ⟨58653137299045245729433829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39102091532696830486289219 58653137299045245729433829)
  ·
    refine ⟨10997463243570983574268843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58653137299045245729433829 10997463243570983574268843)
    ·
      refine ⟨16496194865356475361403265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10997463243570983574268843 16496194865356475361403265)
      ·
        refine ⟨12372146149017356521052449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16496194865356475361403265 12372146149017356521052449)
        ·
          refine ⟨9279109611763017390789337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12372146149017356521052449 9279109611763017390789337)
          ·
            refine ⟨6959332208822263043092003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9279109611763017390789337 6959332208822263043092003)
            ·
              refine ⟨10438998313233394564638005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6959332208822263043092003 10438998313233394564638005)
              ·
                refine ⟨978656091865630740434813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10438998313233394564638005 978656091865630740434813)
                ·
                  refine ⟨366996034449611527663055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978656091865630740434813 366996034449611527663055)
                  ·
                    rfl

theorem cell21_1608125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_1608125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608125 prefixEnd_1608125 := by exact prefixLift 1608125
  have htrace : WordTrace (prefixWord ++ tailWord_1608125) baseStart_1608125 baseEnd_1608125 := by
    simpa [prefixWord, tailWord_1608125, baseEnd_1608125] using wordTrace_append hprefix tailTrace_1608125
  have hstable : (prefixWord ++ tailWord_1608125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608125).length < 2 ^ (prefixWord ++ tailWord_1608125).sum := by decide
  have hdescent : baseEnd_1608125 < baseStart_1608125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608170 : List Nat := [3, 1, 3, 1, 3, 1, 4, 5]
def baseStart_1608170 : Nat := 118140960795 + 1608170 * 2 ^ 59
def prefixEnd_1608170 : Nat := 4983230072969 + 3 ^ 40 * 1608170 * 2
def baseEnd_1608170 : Nat := 122335434687567149804321

theorem tailTrace_1608170 : CollatzResearch.WordTrace tailWord_1608170 prefixEnd_1608170 122335434687567149804321 := by
  unfold tailWord_1608170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14663694645970554603705491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39103185722588145609881309 14663694645970554603705491)
  ·
    refine ⟨21995541968955831905558237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14663694645970554603705491 21995541968955831905558237)
    ·
      refine ⟨8248328238358436964584339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21995541968955831905558237 8248328238358436964584339)
      ·
        refine ⟨12372492357537655446876509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8248328238358436964584339 12372492357537655446876509)
        ·
          refine ⟨4639684634076620792578691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12372492357537655446876509 4639684634076620792578691)
          ·
            refine ⟨6959526951114931188868037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639684634076620792578691 6959526951114931188868037)
            ·
              refine ⟨1304911303334049597912757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6959526951114931188868037 1304911303334049597912757)
              ·
                refine ⟨122335434687567149804321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1304911303334049597912757 122335434687567149804321)
                ·
                  rfl

theorem cell21_1608170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_1608170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608170 prefixEnd_1608170 := by exact prefixLift 1608170
  have htrace : WordTrace (prefixWord ++ tailWord_1608170) baseStart_1608170 baseEnd_1608170 := by
    simpa [prefixWord, tailWord_1608170, baseEnd_1608170] using wordTrace_append hprefix tailTrace_1608170
  have hstable : (prefixWord ++ tailWord_1608170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608170).length < 2 ^ (prefixWord ++ tailWord_1608170).sum := by decide
  have hdescent : baseEnd_1608170 < baseStart_1608170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608288 : List Nat := [2, 1, 1, 3, 2, 1, 2, 9]
def baseStart_1608288 : Nat := 118140960795 + 1608288 * 2 ^ 59
def prefixEnd_1608288 : Nat := 4983230072969 + 3 ^ 40 * 1608288 * 2
def baseEnd_1608288 : Nat := 122344411090119822148685

theorem tailTrace_1608288 : CollatzResearch.WordTrace tailWord_1608288 prefixEnd_1608288 122344411090119822148685 := by
  unfold tailWord_1608288
  simp only [CollatzResearch.WordTrace]
  refine ⟨29329541198727362283808759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39106054931636483045078345 29329541198727362283808759)
  ·
    refine ⟨43994311798091043425713139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29329541198727362283808759 43994311798091043425713139)
    ·
      refine ⟨65991467697136565138569709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43994311798091043425713139 65991467697136565138569709)
      ·
        refine ⟨24746800386426211926963641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65991467697136565138569709 24746800386426211926963641)
        ·
          refine ⟨18560100289819658945222731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24746800386426211926963641 18560100289819658945222731)
          ·
            refine ⟨27840150434729488417834097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18560100289819658945222731 27840150434729488417834097)
            ·
              refine ⟨20880112826047116313375573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27840150434729488417834097 20880112826047116313375573)
              ·
                refine ⟨122344411090119822148685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20880112826047116313375573 122344411090119822148685)
                ·
                  rfl

theorem cell21_1608288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_1608288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608288 prefixEnd_1608288 := by exact prefixLift 1608288
  have htrace : WordTrace (prefixWord ++ tailWord_1608288) baseStart_1608288 baseEnd_1608288 := by
    simpa [prefixWord, tailWord_1608288, baseEnd_1608288] using wordTrace_append hprefix tailTrace_1608288
  have hstable : (prefixWord ++ tailWord_1608288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608288).length < 2 ^ (prefixWord ++ tailWord_1608288).sum := by decide
  have hdescent : baseEnd_1608288 < baseStart_1608288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608381 : List Nat := [1, 4, 1, 2, 1, 4, 2, 6]
def baseStart_1608381 : Nat := 118140960795 + 1608381 * 2 ^ 59
def prefixEnd_1608381 : Nat := 4983230072969 + 3 ^ 40 * 1608381 * 2
def baseEnd_1608381 : Nat := 122351485712470657131955

theorem tailTrace_1608381 : CollatzResearch.WordTrace tailWord_1608381 prefixEnd_1608381 122351485712470657131955 := by
  unfold tailWord_1608381
  simp only [CollatzResearch.WordTrace]
  refine ⟨58662474386117801450752997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39108316257411867633835331 58662474386117801450752997)
  ·
    refine ⟨10999213947397087772016187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58662474386117801450752997 10999213947397087772016187)
    ·
      refine ⟨16498820921095631658024281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10999213947397087772016187 16498820921095631658024281)
      ·
        refine ⟨12374115690821723743518211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16498820921095631658024281 12374115690821723743518211)
        ·
          refine ⟨18561173536232585615277317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12374115690821723743518211 18561173536232585615277317)
          ·
            refine ⟨3480220038043609802864497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18561173536232585615277317 3480220038043609802864497)
            ·
              refine ⟨2610165028532707352148373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480220038043609802864497 2610165028532707352148373)
              ·
                refine ⟨122351485712470657131955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2610165028532707352148373 122351485712470657131955)
                ·
                  rfl

theorem cell21_1608381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 6].length) (baseStart_1608381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608381 prefixEnd_1608381 := by exact prefixLift 1608381
  have htrace : WordTrace (prefixWord ++ tailWord_1608381) baseStart_1608381 baseEnd_1608381 := by
    simpa [prefixWord, tailWord_1608381, baseEnd_1608381] using wordTrace_append hprefix tailTrace_1608381
  have hstable : (prefixWord ++ tailWord_1608381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608381).length < 2 ^ (prefixWord ++ tailWord_1608381).sum := by decide
  have hdescent : baseEnd_1608381 < baseStart_1608381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608384 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 4]
def baseStart_1608384 : Nat := 118140960795 + 1608384 * 2 ^ 59
def prefixEnd_1608384 : Nat := 4983230072969 + 3 ^ 40 * 1608384 * 2
def baseEnd_1608384 : Nat := 367055141778284632845859

theorem tailTrace_1608384 : CollatzResearch.WordTrace tailWord_1608384 prefixEnd_1608384 367055141778284632845859 := by
  unfold tailWord_1608384
  simp only [CollatzResearch.WordTrace]
  refine ⟨29331291902553466481556103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39108389203404621975408137 29331291902553466481556103)
  ·
    refine ⟨43996937853830199722334155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29331291902553466481556103 43996937853830199722334155)
    ·
      refine ⟨65995406780745299583501233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43996937853830199722334155 65995406780745299583501233)
      ·
        refine ⟨49496555085558974687625925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65995406780745299583501233 49496555085558974687625925)
        ·
          refine ⟨9280604078542307753929861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49496555085558974687625925 9280604078542307753929861)
          ·
            refine ⟨1740113264726682703861849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9280604078542307753929861 1740113264726682703861849)
            ·
              refine ⟨1305084948545012027896387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740113264726682703861849 1305084948545012027896387)
              ·
                refine ⟨1957627422817518041844581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305084948545012027896387 1957627422817518041844581)
                ·
                  refine ⟨367055141778284632845859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957627422817518041844581 367055141778284632845859)
                  ·
                    rfl

theorem cell21_1608384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_1608384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608384 prefixEnd_1608384 := by exact prefixLift 1608384
  have htrace : WordTrace (prefixWord ++ tailWord_1608384) baseStart_1608384 baseEnd_1608384 := by
    simpa [prefixWord, tailWord_1608384, baseEnd_1608384] using wordTrace_append hprefix tailTrace_1608384
  have hstable : (prefixWord ++ tailWord_1608384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608384).length < 2 ^ (prefixWord ++ tailWord_1608384).sum := by decide
  have hdescent : baseEnd_1608384 < baseStart_1608384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608429 : List Nat := [1, 5, 1, 2, 1, 1, 3, 4, 3]
def baseStart_1608429 : Nat := 118140960795 + 1608429 * 2 ^ 59
def prefixEnd_1608429 : Nat := 4983230072969 + 3 ^ 40 * 1608429 * 2
def baseEnd_1608429 : Nat := 367065411391374554595767

theorem tailTrace_1608429 : CollatzResearch.WordTrace tailWord_1608429 prefixEnd_1608429 367065411391374554595767 := by
  unfold tailWord_1608429
  simp only [CollatzResearch.WordTrace]
  refine ⟨58664225089943905648500341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39109483393295937099000227 58664225089943905648500341)
  ·
    refine ⟨5499771102182241154546907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58664225089943905648500341 5499771102182241154546907)
    ·
      refine ⟨8249656653273361731820361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499771102182241154546907 8249656653273361731820361)
      ·
        refine ⟨6187242489955021298865271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8249656653273361731820361 6187242489955021298865271)
        ·
          refine ⟨9280863734932531948297907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6187242489955021298865271 9280863734932531948297907)
          ·
            refine ⟨13921295602398797922446861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9280863734932531948297907 13921295602398797922446861)
            ·
              refine ⟨5220485850899549220917573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13921295602398797922446861 5220485850899549220917573)
              ·
                refine ⟨978841097043665478922045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5220485850899549220917573 978841097043665478922045)
                ·
                  refine ⟨367065411391374554595767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978841097043665478922045 367065411391374554595767)
                  ·
                    rfl

theorem cell21_1608429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_1608429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608429 prefixEnd_1608429 := by exact prefixLift 1608429
  have htrace : WordTrace (prefixWord ++ tailWord_1608429) baseStart_1608429 baseEnd_1608429 := by
    simpa [prefixWord, tailWord_1608429, baseEnd_1608429] using wordTrace_append hprefix tailTrace_1608429
  have hstable : (prefixWord ++ tailWord_1608429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608429).length < 2 ^ (prefixWord ++ tailWord_1608429).sum := by decide
  have hdescent : baseEnd_1608429 < baseStart_1608429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608477 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 4]
def baseStart_1608477 : Nat := 118140960795 + 1608477 * 2 ^ 59
def prefixEnd_1608477 : Nat := 4983230072969 + 3 ^ 40 * 1608477 * 2
def baseEnd_1608477 : Nat := 367076365645337137795669

theorem tailTrace_1608477 : CollatzResearch.WordTrace tailWord_1608477 prefixEnd_1608477 367076365645337137795669 := by
  unfold tailWord_1608477
  simp only [CollatzResearch.WordTrace]
  refine ⟨58665975793770009846247685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39110650529180006564165123 58665975793770009846247685)
  ·
    refine ⟨10999870461331876846171441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58665975793770009846247685 10999870461331876846171441)
    ·
      refine ⟨8249902845998907634628581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10999870461331876846171441 8249902845998907634628581)
      ·
        refine ⟨1546856783624795181492859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8249902845998907634628581 1546856783624795181492859)
        ·
          refine ⟨2320285175437192772239289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546856783624795181492859 2320285175437192772239289)
          ·
            refine ⟨1740213881577894579179467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2320285175437192772239289 1740213881577894579179467)
            ·
              refine ⟨2610320822366841868769201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740213881577894579179467 2610320822366841868769201)
              ·
                refine ⟨1957740616775131401576901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2610320822366841868769201 1957740616775131401576901)
                ·
                  refine ⟨367076365645337137795669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957740616775131401576901 367076365645337137795669)
                  ·
                    rfl

theorem cell21_1608477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_1608477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608477 prefixEnd_1608477 := by exact prefixLift 1608477
  have htrace : WordTrace (prefixWord ++ tailWord_1608477) baseStart_1608477 baseEnd_1608477 := by
    simpa [prefixWord, tailWord_1608477, baseEnd_1608477] using wordTrace_append hprefix tailTrace_1608477
  have hstable : (prefixWord ++ tailWord_1608477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608477).length < 2 ^ (prefixWord ++ tailWord_1608477).sum := by decide
  have hdescent : baseEnd_1608477 < baseStart_1608477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608488 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_1608488 : Nat := 118140960795 + 1608488 * 2 ^ 59
def prefixEnd_1608488 : Nat := 4983230072969 + 3 ^ 40 * 1608488 * 2
def baseEnd_1608488 : Nat := 367078875995203563112313

theorem tailTrace_1608488 : CollatzResearch.WordTrace tailWord_1608488 prefixEnd_1608488 367078875995203563112313 := by
  unfold tailWord_1608488
  simp only [CollatzResearch.WordTrace]
  refine ⟨29333188498365079362449059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39110917997820105816598745 29333188498365079362449059)
  ·
    refine ⟨43999782747547619043673589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29333188498365079362449059 43999782747547619043673589)
    ·
      refine ⟨4124979632582589285344399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43999782747547619043673589 4124979632582589285344399)
      ·
        refine ⟨6187469448873883928016599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4124979632582589285344399 6187469448873883928016599)
        ·
          refine ⟨9281204173310825892024899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6187469448873883928016599 9281204173310825892024899)
          ·
            refine ⟨13921806259966238838037349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9281204173310825892024899 13921806259966238838037349)
            ·
              refine ⟨2610338673743669782132003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13921806259966238838037349 2610338673743669782132003)
              ·
                refine ⟨3915508010615504673198005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610338673743669782132003 3915508010615504673198005)
                ·
                  refine ⟨367078875995203563112313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3915508010615504673198005 367078875995203563112313)
                  ·
                    rfl

theorem cell21_1608488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_1608488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608488 prefixEnd_1608488 := by exact prefixLift 1608488
  have htrace : WordTrace (prefixWord ++ tailWord_1608488) baseStart_1608488 baseEnd_1608488 := by
    simpa [prefixWord, tailWord_1608488, baseEnd_1608488] using wordTrace_append hprefix tailTrace_1608488
  have hstable : (prefixWord ++ tailWord_1608488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608488).length < 2 ^ (prefixWord ++ tailWord_1608488).sum := by decide
  have hdescent : baseEnd_1608488 < baseStart_1608488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608609 : List Nat := [1, 2, 3, 4, 1, 1, 3, 6]
def baseStart_1608609 : Nat := 118140960795 + 1608609 * 2 ^ 59
def prefixEnd_1608609 : Nat := 4983230072969 + 3 ^ 40 * 1608609 * 2
def baseEnd_1608609 : Nat := 122368829947911413865133

theorem tailTrace_1608609 : CollatzResearch.WordTrace tailWord_1608609 prefixEnd_1608609 122368829947911413865133 := by
  unfold tailWord_1608609
  simp only [CollatzResearch.WordTrace]
  refine ⟨58670790229291796390052881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39113860152861197593368587 58670790229291796390052881)
  ·
    refine ⟨44003092671968847292539661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58670790229291796390052881 44003092671968847292539661)
    ·
      refine ⟨16501159751988317734702373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44003092671968847292539661 16501159751988317734702373)
      ·
        refine ⟨3093967453497809575256695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16501159751988317734702373 3093967453497809575256695)
        ·
          refine ⟨4640951180246714362885043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3093967453497809575256695 4640951180246714362885043)
          ·
            refine ⟨6961426770370071544327565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640951180246714362885043 6961426770370071544327565)
            ·
              refine ⟨2610535038888776829122837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6961426770370071544327565 2610535038888776829122837)
              ·
                refine ⟨122368829947911413865133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2610535038888776829122837 122368829947911413865133)
                ·
                  rfl

theorem cell21_1608609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 6].length) (baseStart_1608609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608609 prefixEnd_1608609 := by exact prefixLift 1608609
  have htrace : WordTrace (prefixWord ++ tailWord_1608609) baseStart_1608609 baseEnd_1608609 := by
    simpa [prefixWord, tailWord_1608609, baseEnd_1608609] using wordTrace_append hprefix tailTrace_1608609
  have hstable : (prefixWord ++ tailWord_1608609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608609).length < 2 ^ (prefixWord ++ tailWord_1608609).sum := by decide
  have hdescent : baseEnd_1608609 < baseStart_1608609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608640 : List Nat := [2, 1, 1, 2, 3, 3, 1, 5, 3]
def baseStart_1608640 : Nat := 118140960795 + 1608640 * 2 ^ 59
def prefixEnd_1608640 : Nat := 4983230072969 + 3 ^ 40 * 1608640 * 2
def baseEnd_1608640 : Nat := 367113564466085076578669

theorem tailTrace_1608640 : CollatzResearch.WordTrace tailWord_1608640 prefixEnd_1608640 367113564466085076578669 := by
  unfold tailWord_1608640
  simp only [CollatzResearch.WordTrace]
  refine ⟨29335960446089744342215687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39114613928119659122954249 29335960446089744342215687)
  ·
    refine ⟨44003940669134616513323531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29335960446089744342215687 44003940669134616513323531)
    ·
      refine ⟨66005911003701924769985297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44003940669134616513323531 66005911003701924769985297)
      ·
        refine ⟨49504433252776443577488973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66005911003701924769985297 49504433252776443577488973)
        ·
          refine ⟨18564162469791166341558365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49504433252776443577488973 18564162469791166341558365)
          ·
            refine ⟨6961560926171687378084387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18564162469791166341558365 6961560926171687378084387)
            ·
              refine ⟨10442341389257531067126581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6961560926171687378084387 10442341389257531067126581)
              ·
                refine ⟨978969505242893537543117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10442341389257531067126581 978969505242893537543117)
                ·
                  refine ⟨367113564466085076578669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978969505242893537543117 367113564466085076578669)
                  ·
                    rfl

theorem cell21_1608640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 3].length) (baseStart_1608640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608640 prefixEnd_1608640 := by exact prefixLift 1608640
  have htrace : WordTrace (prefixWord ++ tailWord_1608640) baseStart_1608640 baseEnd_1608640 := by
    simpa [prefixWord, tailWord_1608640, baseEnd_1608640] using wordTrace_append hprefix tailTrace_1608640
  have hstable : (prefixWord ++ tailWord_1608640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608640).length < 2 ^ (prefixWord ++ tailWord_1608640).sum := by decide
  have hdescent : baseEnd_1608640 < baseStart_1608640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608646 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1608646 : Nat := 118140960795 + 1608646 * 2 ^ 59
def prefixEnd_1608646 : Nat := 4983230072969 + 3 ^ 40 * 1608646 * 2
def baseEnd_1608646 : Nat := 367114933747830399478657

theorem tailTrace_1608646 : CollatzResearch.WordTrace tailWord_1608646 prefixEnd_1608646 367114933747830399478657 := by
  unfold tailWord_1608646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1833504366567429740910931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39114759820105167806099861 1833504366567429740910931)
  ·
    refine ⟨2750256549851144611366397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1833504366567429740910931 2750256549851144611366397)
    ·
      refine ⟨1031346206194179229262399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2750256549851144611366397 1031346206194179229262399)
      ·
        refine ⟨1547019309291268843893599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031346206194179229262399 1547019309291268843893599)
        ·
          refine ⟨2320528963936903265840399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547019309291268843893599 2320528963936903265840399)
          ·
            refine ⟨3480793445905354898760599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320528963936903265840399 3480793445905354898760599)
            ·
              refine ⟨5221190168858032348140899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480793445905354898760599 5221190168858032348140899)
              ·
                refine ⟨7831785253287048522211349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221190168858032348140899 7831785253287048522211349)
                ·
                  refine ⟨367114933747830399478657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7831785253287048522211349 367114933747830399478657)
                  ·
                    rfl

theorem cell21_1608646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1608646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608646 prefixEnd_1608646 := by exact prefixLift 1608646
  have htrace : WordTrace (prefixWord ++ tailWord_1608646) baseStart_1608646 baseEnd_1608646 := by
    simpa [prefixWord, tailWord_1608646, baseEnd_1608646] using wordTrace_append hprefix tailTrace_1608646
  have hstable : (prefixWord ++ tailWord_1608646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608646).length < 2 ^ (prefixWord ++ tailWord_1608646).sum := by decide
  have hdescent : baseEnd_1608646 < baseStart_1608646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608654 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_1608654 : Nat := 118140960795 + 1608654 * 2 ^ 59
def prefixEnd_1608654 : Nat := 4983230072969 + 3 ^ 40 * 1608654 * 2
def baseEnd_1608654 : Nat := 367116759456824163345307

theorem tailTrace_1608654 : CollatzResearch.WordTrace tailWord_1608654 prefixEnd_1608654 367116759456824163345307 := by
  unfold tailWord_1608654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334053939266096134430127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39114954342752512716960677 7334053939266096134430127)
  ·
    refine ⟨11001080908899144201645191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7334053939266096134430127 11001080908899144201645191)
    ·
      refine ⟨16501621363348716302467787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11001080908899144201645191 16501621363348716302467787)
      ·
        refine ⟨24752432045023074453701681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16501621363348716302467787 24752432045023074453701681)
        ·
          refine ⟨18564324033767305840276261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24752432045023074453701681 18564324033767305840276261)
          ·
            refine ⟨3480810756331369845051799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18564324033767305840276261 3480810756331369845051799)
            ·
              refine ⟨5221216134497054767577699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480810756331369845051799 5221216134497054767577699)
              ·
                refine ⟨7831824201745582151366549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221216134497054767577699 7831824201745582151366549)
                ·
                  refine ⟨367116759456824163345307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7831824201745582151366549 367116759456824163345307)
                  ·
                    rfl

theorem cell21_1608654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_1608654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608654 prefixEnd_1608654 := by exact prefixLift 1608654
  have htrace : WordTrace (prefixWord ++ tailWord_1608654) baseStart_1608654 baseEnd_1608654 := by
    simpa [prefixWord, tailWord_1608654, baseEnd_1608654] using wordTrace_append hprefix tailTrace_1608654
  have hstable : (prefixWord ++ tailWord_1608654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608654).length < 2 ^ (prefixWord ++ tailWord_1608654).sum := by decide
  have hdescent : baseEnd_1608654 < baseStart_1608654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608702 : List Nat := [4, 2, 2, 2, 2, 2, 7]
def baseStart_1608702 : Nat := 118140960795 + 1608702 * 2 ^ 59
def prefixEnd_1608702 : Nat := 4983230072969 + 3 ^ 40 * 1608702 * 2
def baseEnd_1608702 : Nat := 40791968190087416282801

theorem tailTrace_1608702 : CollatzResearch.WordTrace tailWord_1608702 prefixEnd_1608702 40791968190087416282801 := by
  unfold tailWord_1608702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334272777244359159148545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39116121478636582182125573 7334272777244359159148545)
  ·
    refine ⟨5500704582933269369361409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7334272777244359159148545 5500704582933269369361409)
    ·
      refine ⟨4125528437199952027021057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5500704582933269369361409 4125528437199952027021057)
      ·
        refine ⟨3094146327899964020265793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4125528437199952027021057 3094146327899964020265793)
        ·
          refine ⟨2320609745924973015199345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3094146327899964020265793 2320609745924973015199345)
          ·
            refine ⟨1740457309443729761399509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2320609745924973015199345 1740457309443729761399509)
            ·
              refine ⟨40791968190087416282801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1740457309443729761399509 40791968190087416282801)
              ·
                rfl

theorem cell21_1608702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 7].length) (baseStart_1608702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608702 prefixEnd_1608702 := by exact prefixLift 1608702
  have htrace : WordTrace (prefixWord ++ tailWord_1608702) baseStart_1608702 baseEnd_1608702 := by
    simpa [prefixWord, tailWord_1608702, baseEnd_1608702] using wordTrace_append hprefix tailTrace_1608702
  have hstable : (prefixWord ++ tailWord_1608702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608702).length < 2 ^ (prefixWord ++ tailWord_1608702).sum := by decide
  have hdescent : baseEnd_1608702 < baseStart_1608702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608716 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 5]
def baseStart_1608716 : Nat := 118140960795 + 1608716 * 2 ^ 59
def prefixEnd_1608716 : Nat := 4983230072969 + 3 ^ 40 * 1608716 * 2
def baseEnd_1608716 : Nat := 367130908701525833311847

theorem tailTrace_1608716 : CollatzResearch.WordTrace tailWord_1608716 prefixEnd_1608716 367130908701525833311847 := by
  unfold tailWord_1608716
  simp only [CollatzResearch.WordTrace]
  refine ⟨29337346419952076832099001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39116461893269435776132001 29337346419952076832099001)
  ·
    refine ⟨22003009814964057624074251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29337346419952076832099001 22003009814964057624074251)
    ·
      refine ⟨33004514722446086436111377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22003009814964057624074251 33004514722446086436111377)
      ·
        refine ⟨24753386041834564827083533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33004514722446086436111377 24753386041834564827083533)
        ·
          refine ⟨9282519765687961810156325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24753386041834564827083533 9282519765687961810156325)
          ·
            refine ⟨1740472456066492839404311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9282519765687961810156325 1740472456066492839404311)
            ·
              refine ⟨2610708684099739259106467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740472456066492839404311 2610708684099739259106467)
              ·
                refine ⟨3916063026149608888659701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610708684099739259106467 3916063026149608888659701)
                ·
                  refine ⟨367130908701525833311847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3916063026149608888659701 367130908701525833311847)
                  ·
                    rfl

theorem cell21_1608716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_1608716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608716 prefixEnd_1608716 := by exact prefixLift 1608716
  have htrace : WordTrace (prefixWord ++ tailWord_1608716) baseStart_1608716 baseEnd_1608716 := by
    simpa [prefixWord, tailWord_1608716, baseEnd_1608716] using wordTrace_append hprefix tailTrace_1608716
  have hstable : (prefixWord ++ tailWord_1608716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608716).length < 2 ^ (prefixWord ++ tailWord_1608716).sum := by decide
  have hdescent : baseEnd_1608716 < baseStart_1608716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608730 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_1608730 : Nat := 118140960795 + 1608730 * 2 ^ 59
def prefixEnd_1608730 : Nat := 4983230072969 + 3 ^ 40 * 1608730 * 2
def baseEnd_1608730 : Nat := 367134103692264920078485

theorem tailTrace_1608730 : CollatzResearch.WordTrace tailWord_1608730 prefixEnd_1608730 367134103692264920078485 := by
  unfold tailWord_1608730
  simp only [CollatzResearch.WordTrace]
  refine ⟨14668800865463358513801911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39116802307902289370138429 14668800865463358513801911)
  ·
    refine ⟨22003201298195037770702867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14668800865463358513801911 22003201298195037770702867)
    ·
      refine ⟨33004801947292556656054301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22003201298195037770702867 33004801947292556656054301)
      ·
        refine ⟨12376800730234708746020363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33004801947292556656054301 12376800730234708746020363)
        ·
          refine ⟨18565201095352063119030545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12376800730234708746020363 18565201095352063119030545)
          ·
            refine ⟨13923900821514047339272909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18565201095352063119030545 13923900821514047339272909)
            ·
              refine ⟨5221462808067767752227341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13923900821514047339272909 5221462808067767752227341)
              ·
                refine ⟨1958048553025412907085253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5221462808067767752227341 1958048553025412907085253)
                ·
                  refine ⟨367134103692264920078485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958048553025412907085253 367134103692264920078485)
                  ·
                    rfl

theorem cell21_1608730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_1608730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608730 prefixEnd_1608730 := by exact prefixLift 1608730
  have htrace : WordTrace (prefixWord ++ tailWord_1608730) baseStart_1608730 baseEnd_1608730 := by
    simpa [prefixWord, tailWord_1608730, baseEnd_1608730] using wordTrace_append hprefix tailTrace_1608730
  have hstable : (prefixWord ++ tailWord_1608730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608730).length < 2 ^ (prefixWord ++ tailWord_1608730).sum := by decide
  have hdescent : baseEnd_1608730 < baseStart_1608730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608840 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 4]
def baseStart_1608840 : Nat := 118140960795 + 1608840 * 2 ^ 59
def prefixEnd_1608840 : Nat := 4983230072969 + 3 ^ 40 * 1608840 * 2
def baseEnd_1608840 : Nat := 367159207190929173244927

theorem tailTrace_1608840 : CollatzResearch.WordTrace tailWord_1608840 prefixEnd_1608840 367159207190929173244927 := by
  unfold tailWord_1608840
  simp only [CollatzResearch.WordTrace]
  refine ⟨29339607745727461420855987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39119476994303281894474649 29339607745727461420855987)
  ·
    refine ⟨44009411618591192131283981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29339607745727461420855987 44009411618591192131283981)
    ·
      refine ⟨16503529356971697049231493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44009411618591192131283981 16503529356971697049231493)
      ·
        refine ⟨3094411754432193196730905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16503529356971697049231493 3094411754432193196730905)
        ·
          refine ⟨2320808815824144897548179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3094411754432193196730905 2320808815824144897548179)
          ·
            refine ⟨3481213223736217346322269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320808815824144897548179 3481213223736217346322269)
            ·
              refine ⟨1305454958901081504870851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3481213223736217346322269 1305454958901081504870851)
              ·
                refine ⟨1958182438351622257306277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305454958901081504870851 1958182438351622257306277)
                ·
                  refine ⟨367159207190929173244927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958182438351622257306277 367159207190929173244927)
                  ·
                    rfl

theorem cell21_1608840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_1608840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608840 prefixEnd_1608840 := by exact prefixLift 1608840
  have htrace : WordTrace (prefixWord ++ tailWord_1608840) baseStart_1608840 baseEnd_1608840 := by
    simpa [prefixWord, tailWord_1608840, baseEnd_1608840] using wordTrace_append hprefix tailTrace_1608840
  have hstable : (prefixWord ++ tailWord_1608840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608840).length < 2 ^ (prefixWord ++ tailWord_1608840).sum := by decide
  have hdescent : baseEnd_1608840 < baseStart_1608840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608865 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 8]
def baseStart_1608865 : Nat := 118140960795 + 1608865 * 2 ^ 59
def prefixEnd_1608865 : Nat := 4983230072969 + 3 ^ 40 * 1608865 * 2
def baseEnd_1608865 : Nat := 367164912531534685328209

theorem tailTrace_1608865 : CollatzResearch.WordTrace tailWord_1608865 prefixEnd_1608865 367164912531534685328209 := by
  unfold tailWord_1608865
  simp only [CollatzResearch.WordTrace]
  refine ⟨58680127316364352111372049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39120084877576234740914699 58680127316364352111372049)
  ·
    refine ⟨44010095487273264083529037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58680127316364352111372049 44010095487273264083529037)
    ·
      refine ⟨16503785807727474031323389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44010095487273264083529037 16503785807727474031323389)
      ·
        refine ⟨6188919677897802761746271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16503785807727474031323389 6188919677897802761746271)
        ·
          refine ⟨9283379516846704142619407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6188919677897802761746271 9283379516846704142619407)
          ·
            refine ⟨13925069275270056213929111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9283379516846704142619407 13925069275270056213929111)
            ·
              refine ⟨20887603912905084320893667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13925069275270056213929111 20887603912905084320893667)
              ·
                refine ⟨31331405869357626481340501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20887603912905084320893667 31331405869357626481340501)
                ·
                  refine ⟨367164912531534685328209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31331405869357626481340501 367164912531534685328209)
                  ·
                    rfl

theorem cell21_1608865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_1608865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608865 prefixEnd_1608865 := by exact prefixLift 1608865
  have htrace : WordTrace (prefixWord ++ tailWord_1608865) baseStart_1608865 baseEnd_1608865 := by
    simpa [prefixWord, tailWord_1608865, baseEnd_1608865] using wordTrace_append hprefix tailTrace_1608865
  have hstable : (prefixWord ++ tailWord_1608865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608865).length < 2 ^ (prefixWord ++ tailWord_1608865).sum := by decide
  have hdescent : baseEnd_1608865 < baseStart_1608865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608879 : List Nat := [1, 1, 2, 1, 2, 3, 11]
def baseStart_1608879 : Nat := 118140960795 + 1608879 * 2 ^ 59
def prefixEnd_1608879 : Nat := 4983230072969 + 3 ^ 40 * 1608879 * 2
def baseEnd_1608879 : Nat := 40796456391363752454983

theorem tailTrace_1608879 : CollatzResearch.WordTrace tailWord_1608879 prefixEnd_1608879 40796456391363752454983 := by
  unfold tailWord_1608879
  simp only [CollatzResearch.WordTrace]
  refine ⟨58680637938313632502381691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39120425292209088334921127 58680637938313632502381691)
  ·
    refine ⟨88020956907470448753572537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58680637938313632502381691 88020956907470448753572537)
    ·
      refine ⟨66015717680602836565179403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88020956907470448753572537 66015717680602836565179403)
      ·
        refine ⟨99023576520904254847769105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66015717680602836565179403 99023576520904254847769105)
        ·
          refine ⟨74267682390678191135826829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99023576520904254847769105 74267682390678191135826829)
          ·
            refine ⟨27850380896504321675935061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74267682390678191135826829 27850380896504321675935061)
            ·
              refine ⟨40796456391363752454983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27850380896504321675935061 40796456391363752454983)
              ·
                rfl

theorem cell21_1608879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 11].length) (baseStart_1608879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608879 prefixEnd_1608879 := by exact prefixLift 1608879
  have htrace : WordTrace (prefixWord ++ tailWord_1608879) baseStart_1608879 baseEnd_1608879 := by
    simpa [prefixWord, tailWord_1608879, baseEnd_1608879] using wordTrace_append hprefix tailTrace_1608879
  have hstable : (prefixWord ++ tailWord_1608879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608879).length < 2 ^ (prefixWord ++ tailWord_1608879).sum := by decide
  have hdescent : baseEnd_1608879 < baseStart_1608879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608992 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 4]
def baseStart_1608992 : Nat := 118140960795 + 1608992 * 2 ^ 59
def prefixEnd_1608992 : Nat := 4983230072969 + 3 ^ 40 * 1608992 * 2
def baseEnd_1608992 : Nat := 367193895661810686711283

theorem tailTrace_1608992 : CollatzResearch.WordTrace tailWord_1608992 prefixEnd_1608992 367193895661810686711283 := by
  unfold tailWord_1608992
  simp only [CollatzResearch.WordTrace]
  refine ⟨29342379693452126400622615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39123172924602835200830153 29342379693452126400622615)
  ·
    refine ⟨44013569540178189600933923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29342379693452126400622615 44013569540178189600933923)
    ·
      refine ⟨66020354310267284401400885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44013569540178189600933923 66020354310267284401400885)
      ·
        refine ⟨6189408216587557912631333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66020354310267284401400885 6189408216587557912631333)
        ·
          refine ⟨1160514040610167108618375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6189408216587557912631333 1160514040610167108618375)
          ·
            refine ⟨1740771060915250662927563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160514040610167108618375 1740771060915250662927563)
            ·
              refine ⟨2611156591372875994391345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740771060915250662927563 2611156591372875994391345)
              ·
                refine ⟨1958367443529656995793509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2611156591372875994391345 1958367443529656995793509)
                ·
                  refine ⟨367193895661810686711283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958367443529656995793509 367193895661810686711283)
                  ·
                    rfl

theorem cell21_1608992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 4].length) (baseStart_1608992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1608992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1608992 prefixEnd_1608992 := by exact prefixLift 1608992
  have htrace : WordTrace (prefixWord ++ tailWord_1608992) baseStart_1608992 baseEnd_1608992 := by
    simpa [prefixWord, tailWord_1608992, baseEnd_1608992] using wordTrace_append hprefix tailTrace_1608992
  have hstable : (prefixWord ++ tailWord_1608992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608992).length < 2 ^ (prefixWord ++ tailWord_1608992).sum := by decide
  have hdescent : baseEnd_1608992 < baseStart_1608992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609113 : List Nat := [1, 2, 1, 2, 1, 7, 2, 2, 3]
def baseStart_1609113 : Nat := 118140960795 + 1609113 * 2 ^ 59
def prefixEnd_1609113 : Nat := 4983230072969 + 3 ^ 40 * 1609113 * 2
def baseEnd_1609113 : Nat := 367221509510341365194369

theorem tailTrace_1609113 : CollatzResearch.WordTrace tailWord_1609113 prefixEnd_1609113 367221509510341365194369 := by
  unfold tailWord_1609113
  simp only [CollatzResearch.WordTrace]
  refine ⟨58689172619465890466399993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39126115079643926977599995 58689172619465890466399993)
  ·
    refine ⟨44016879464599417849799995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58689172619465890466399993 44016879464599417849799995)
    ·
      refine ⟨66025319196899126774699993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44016879464599417849799995 66025319196899126774699993)
      ·
        refine ⟨49518989397674345081024995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66025319196899126774699993 49518989397674345081024995)
        ·
          refine ⟨74278484096511517621537493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49518989397674345081024995 74278484096511517621537493)
          ·
            refine ⟨1740901971011988694254785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 74278484096511517621537493 1740901971011988694254785)
            ·
              refine ⟨1305676478258991520691089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740901971011988694254785 1305676478258991520691089)
              ·
                refine ⟨979257358694243640518317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1305676478258991520691089 979257358694243640518317)
                ·
                  refine ⟨367221509510341365194369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979257358694243640518317 367221509510341365194369)
                  ·
                    rfl

theorem cell21_1609113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 3].length) (baseStart_1609113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609113 prefixEnd_1609113 := by exact prefixLift 1609113
  have htrace : WordTrace (prefixWord ++ tailWord_1609113) baseStart_1609113 baseEnd_1609113 := by
    simpa [prefixWord, tailWord_1609113, baseEnd_1609113] using wordTrace_append hprefix tailTrace_1609113
  have hstable : (prefixWord ++ tailWord_1609113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609113).length < 2 ^ (prefixWord ++ tailWord_1609113).sum := by decide
  have hdescent : baseEnd_1609113 < baseStart_1609113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609141 : List Nat := [1, 3, 3, 2, 2, 2, 3, 5]
def baseStart_1609141 : Nat := 118140960795 + 1609141 * 2 ^ 59
def prefixEnd_1609141 : Nat := 4983230072969 + 3 ^ 40 * 1609141 * 2
def baseEnd_1609141 : Nat := 122409299830606512909215

theorem tailTrace_1609141 : CollatzResearch.WordTrace tailWord_1609141 prefixEnd_1609141 122409299830606512909215 := by
  unfold tailWord_1609141
  simp only [CollatzResearch.WordTrace]
  refine ⟨58690193863364451248419277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39126795908909634165612851 58690193863364451248419277)
  ·
    refine ⟨22008822698761669218157229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58690193863364451248419277 22008822698761669218157229)
    ·
      refine ⟨8253308512035625956808961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22008822698761669218157229 8253308512035625956808961)
      ·
        refine ⟨6189981384026719467606721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8253308512035625956808961 6189981384026719467606721)
        ·
          refine ⟨4642486038020039600705041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6189981384026719467606721 4642486038020039600705041)
          ·
            refine ⟨3481864528515029700528781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4642486038020039600705041 3481864528515029700528781)
            ·
              refine ⟨1305699198193136137698293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3481864528515029700528781 1305699198193136137698293)
              ·
                refine ⟨122409299830606512909215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1305699198193136137698293 122409299830606512909215)
                ·
                  rfl

theorem cell21_1609141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 5].length) (baseStart_1609141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609141 prefixEnd_1609141 := by exact prefixLift 1609141
  have htrace : WordTrace (prefixWord ++ tailWord_1609141) baseStart_1609141 baseEnd_1609141 := by
    simpa [prefixWord, tailWord_1609141, baseEnd_1609141] using wordTrace_append hprefix tailTrace_1609141
  have hstable : (prefixWord ++ tailWord_1609141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609141).length < 2 ^ (prefixWord ++ tailWord_1609141).sum := by decide
  have hdescent : baseEnd_1609141 < baseStart_1609141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609155 : List Nat := [1, 1, 1, 3, 1, 1, 5, 5, 3]
def baseStart_1609155 : Nat := 118140960795 + 1609155 * 2 ^ 59
def prefixEnd_1609155 : Nat := 4983230072969 + 3 ^ 40 * 1609155 * 2
def baseEnd_1609155 : Nat := 367231094482558625494283

theorem tailTrace_1609155 : CollatzResearch.WordTrace tailWord_1609155 prefixEnd_1609155 367231094482558625494283 := by
  unfold tailWord_1609155
  simp only [CollatzResearch.WordTrace]
  refine ⟨58690704485313731639428919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39127136323542487759619279 58690704485313731639428919)
  ·
    refine ⟨88036056727970597459143379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58690704485313731639428919 88036056727970597459143379)
    ·
      refine ⟨132054085091955896188715069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88036056727970597459143379 132054085091955896188715069)
      ·
        refine ⟨49520281909483461070768151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132054085091955896188715069 49520281909483461070768151)
        ·
          refine ⟨74280422864225191606152227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49520281909483461070768151 74280422864225191606152227)
          ·
            refine ⟨111420634296337787409228341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74280422864225191606152227 111420634296337787409228341)
            ·
              refine ⟨10445684465281667569615157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111420634296337787409228341 10445684465281667569615157)
              ·
                refine ⟨979282918620156334651421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10445684465281667569615157 979282918620156334651421)
                ·
                  refine ⟨367231094482558625494283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979282918620156334651421 367231094482558625494283)
                  ·
                    rfl

theorem cell21_1609155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 3].length) (baseStart_1609155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609155 prefixEnd_1609155 := by exact prefixLift 1609155
  have htrace : WordTrace (prefixWord ++ tailWord_1609155) baseStart_1609155 baseEnd_1609155 := by
    simpa [prefixWord, tailWord_1609155, baseEnd_1609155] using wordTrace_append hprefix tailTrace_1609155
  have hstable : (prefixWord ++ tailWord_1609155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609155).length < 2 ^ (prefixWord ++ tailWord_1609155).sum := by decide
  have hdescent : baseEnd_1609155 < baseStart_1609155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609172 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1609172 : Nat := 118140960795 + 1609172 * 2 ^ 59
def prefixEnd_1609172 : Nat := 4983230072969 + 3 ^ 40 * 1609172 * 2
def baseEnd_1609172 : Nat := 367234974114170373710915

theorem tailTrace_1609172 : CollatzResearch.WordTrace tailWord_1609172 prefixEnd_1609172 367234974114170373710915 := by
  unfold tailWord_1609172
  simp only [CollatzResearch.WordTrace]
  refine ⟨29345662263126071771398885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39127549684168095695198513 29345662263126071771398885)
  ·
    refine ⟨5502311674336138457137291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29345662263126071771398885 5502311674336138457137291)
    ·
      refine ⟨8253467511504207685705937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5502311674336138457137291 8253467511504207685705937)
      ·
        refine ⟨6190100633628155764279453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8253467511504207685705937 6190100633628155764279453)
        ·
          refine ⟨2321287737610558411604795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6190100633628155764279453 2321287737610558411604795)
          ·
            refine ⟨3481931606415837617407193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321287737610558411604795 3481931606415837617407193)
            ·
              refine ⟨2611448704811878213055395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3481931606415837617407193 2611448704811878213055395)
              ·
                refine ⟨3917173057217817319583093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611448704811878213055395 3917173057217817319583093)
                ·
                  refine ⟨367234974114170373710915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3917173057217817319583093 367234974114170373710915)
                  ·
                    rfl

theorem cell21_1609172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1609172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609172 prefixEnd_1609172 := by exact prefixLift 1609172
  have htrace : WordTrace (prefixWord ++ tailWord_1609172) baseStart_1609172 baseEnd_1609172 := by
    simpa [prefixWord, tailWord_1609172, baseEnd_1609172] using wordTrace_append hprefix tailTrace_1609172
  have hstable : (prefixWord ++ tailWord_1609172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609172).length < 2 ^ (prefixWord ++ tailWord_1609172).sum := by decide
  have hdescent : baseEnd_1609172 < baseStart_1609172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609183 : List Nat := [1, 1, 2, 3, 3, 1, 2, 8]
def baseStart_1609183 : Nat := 118140960795 + 1609183 * 2 ^ 59
def prefixEnd_1609183 : Nat := 4983230072969 + 3 ^ 40 * 1609183 * 2
def baseEnd_1609183 : Nat := 122412494821345599675853

theorem tailTrace_1609183 : CollatzResearch.WordTrace tailWord_1609183 prefixEnd_1609183 122412494821345599675853 := by
  unfold tailWord_1609183
  simp only [CollatzResearch.WordTrace]
  refine ⟨58691725729212292421448203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39127817152808194947632135 58691725729212292421448203)
  ·
    refine ⟨88037588593818438632172305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58691725729212292421448203 88037588593818438632172305)
    ·
      refine ⟨66028191445363828974129229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88037588593818438632172305 66028191445363828974129229)
      ·
        refine ⟨24760571792011435865298461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66028191445363828974129229 24760571792011435865298461)
        ·
          refine ⟨9285214422004288449486923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24760571792011435865298461 9285214422004288449486923)
          ·
            refine ⟨13927821633006432674230385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9285214422004288449486923 13927821633006432674230385)
            ·
              refine ⟨10445866224754824505672789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13927821633006432674230385 10445866224754824505672789)
              ·
                refine ⟨122412494821345599675853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10445866224754824505672789 122412494821345599675853)
                ·
                  rfl

theorem cell21_1609183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 8].length) (baseStart_1609183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609183 prefixEnd_1609183 := by exact prefixLift 1609183
  have htrace : WordTrace (prefixWord ++ tailWord_1609183) baseStart_1609183 baseEnd_1609183 := by
    simpa [prefixWord, tailWord_1609183, baseEnd_1609183] using wordTrace_append hprefix tailTrace_1609183
  have hstable : (prefixWord ++ tailWord_1609183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609183).length < 2 ^ (prefixWord ++ tailWord_1609183).sum := by decide
  have hdescent : baseEnd_1609183 < baseStart_1609183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609200 : List Nat := [2, 1, 1, 1, 3, 4, 4, 5]
def baseStart_1609200 : Nat := 118140960795 + 1609200 * 2 ^ 59
def prefixEnd_1609200 : Nat := 4983230072969 + 3 ^ 40 * 1609200 * 2
def baseEnd_1609200 : Nat := 122413788031882849081397

theorem tailTrace_1609200 : CollatzResearch.WordTrace tailWord_1609200 prefixEnd_1609200 122413788031882849081397 := by
  unfold tailWord_1609200
  simp only [CollatzResearch.WordTrace]
  refine ⟨29346172885075352162408527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39128230513433802883211369 29346172885075352162408527)
  ·
    refine ⟨44019259327613028243612791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29346172885075352162408527 44019259327613028243612791)
    ·
      refine ⟨66028888991419542365419187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44019259327613028243612791 66028888991419542365419187)
      ·
        refine ⟨99043333487129313548128781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66028888991419542365419187 99043333487129313548128781)
        ·
          refine ⟨37141250057673492580548293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99043333487129313548128781 37141250057673492580548293)
          ·
            refine ⟨6963984385813779858852805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37141250057673492580548293 6963984385813779858852805)
            ·
              refine ⟨1305747072340083723534901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6963984385813779858852805 1305747072340083723534901)
              ·
                refine ⟨122413788031882849081397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1305747072340083723534901 122413788031882849081397)
                ·
                  rfl

theorem cell21_1609200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_1609200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609200 prefixEnd_1609200 := by exact prefixLift 1609200
  have htrace : WordTrace (prefixWord ++ tailWord_1609200) baseStart_1609200 baseEnd_1609200 := by
    simpa [prefixWord, tailWord_1609200, baseEnd_1609200] using wordTrace_append hprefix tailTrace_1609200
  have hstable : (prefixWord ++ tailWord_1609200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609200).length < 2 ^ (prefixWord ++ tailWord_1609200).sum := by decide
  have hdescent : baseEnd_1609200 < baseStart_1609200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609217 : List Nat := [1, 2, 4, 1, 5, 1, 7]
def baseStart_1609217 : Nat := 118140960795 + 1609217 * 2 ^ 59
def prefixEnd_1609217 : Nat := 4983230072969 + 3 ^ 40 * 1609217 * 2
def baseEnd_1609217 : Nat := 40805027080806699495647

theorem tailTrace_1609217 : CollatzResearch.WordTrace tailWord_1609217 prefixEnd_1609217 40805027080806699495647 := by
  unfold tailWord_1609217
  simp only [CollatzResearch.WordTrace]
  refine ⟨58692965811089116228185905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39128643874059410818790603 58692965811089116228185905)
  ·
    refine ⟨44019724358316837171139429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58692965811089116228185905 44019724358316837171139429)
    ·
      refine ⟨8253698317184406969588643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44019724358316837171139429 8253698317184406969588643)
      ·
        refine ⟨12380547475776610454382965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8253698317184406969588643 12380547475776610454382965)
        ·
          refine ⟨1160676325854057230098403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12380547475776610454382965 1160676325854057230098403)
          ·
            refine ⟨1741014488781085845147605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160676325854057230098403 1741014488781085845147605)
            ·
              refine ⟨40805027080806699495647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1741014488781085845147605 40805027080806699495647)
              ·
                rfl

theorem cell21_1609217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 7].length) (baseStart_1609217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609217 prefixEnd_1609217 := by exact prefixLift 1609217
  have htrace : WordTrace (prefixWord ++ tailWord_1609217) baseStart_1609217 baseEnd_1609217 := by
    simpa [prefixWord, tailWord_1609217, baseEnd_1609217] using wordTrace_append hprefix tailTrace_1609217
  have hstable : (prefixWord ++ tailWord_1609217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609217).length < 2 ^ (prefixWord ++ tailWord_1609217).sum := by decide
  have hdescent : baseEnd_1609217 < baseStart_1609217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609276 : List Nat := [2, 2, 2, 2, 5, 8]
def baseStart_1609276 : Nat := 118140960795 + 1609276 * 2 ^ 59
def prefixEnd_1609276 : Nat := 4983230072969 + 3 ^ 40 * 1609276 * 2
def baseEnd_1609276 : Nat := 13602174382632937184347

theorem tailTrace_1609276 : CollatzResearch.WordTrace tailWord_1609276 prefixEnd_1609276 13602174382632937184347 := by
  unfold tailWord_1609276
  simp only [CollatzResearch.WordTrace]
  refine ⟨29347558858937684652291841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39130078478583579536389121 29347558858937684652291841)
  ·
    refine ⟨22010669144203263489218881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29347558858937684652291841 22010669144203263489218881)
    ·
      refine ⟨16508001858152447616914161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22010669144203263489218881 16508001858152447616914161)
      ·
        refine ⟨12381001393614335712685621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16508001858152447616914161 12381001393614335712685621)
        ·
          refine ⟨1160718880651343973064277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12381001393614335712685621 1160718880651343973064277)
          ·
            refine ⟨13602174382632937184347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1160718880651343973064277 13602174382632937184347)
            ·
              rfl

theorem cell21_1609276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 8].length) (baseStart_1609276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609276 prefixEnd_1609276 := by exact prefixLift 1609276
  have htrace : WordTrace (prefixWord ++ tailWord_1609276) baseStart_1609276 baseEnd_1609276 := by
    simpa [prefixWord, tailWord_1609276, baseEnd_1609276] using wordTrace_append hprefix tailTrace_1609276
  have hstable : (prefixWord ++ tailWord_1609276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609276).length < 2 ^ (prefixWord ++ tailWord_1609276).sum := by decide
  have hdescent : baseEnd_1609276 < baseStart_1609276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609290 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_1609290 : Nat := 118140960795 + 1609290 * 2 ^ 59
def prefixEnd_1609290 : Nat := 4983230072969 + 3 ^ 40 * 1609290 * 2
def baseEnd_1609290 : Nat := 367261903321828390744007

theorem tailTrace_1609290 : CollatzResearch.WordTrace tailWord_1609290 prefixEnd_1609290 367261903321828390744007 := by
  unfold tailWord_1609290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14673907084956162423898331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39130418893216433130395549 14673907084956162423898331)
  ·
    refine ⟨22010860627434243635847497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14673907084956162423898331 22010860627434243635847497)
    ·
      refine ⟨16508145470575682726885623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22010860627434243635847497 16508145470575682726885623)
      ·
        refine ⟨24762218205863524090328435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16508145470575682726885623 24762218205863524090328435)
        ·
          refine ⟨37143327308795286135492653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24762218205863524090328435 37143327308795286135492653)
          ·
            refine ⟨13928747740798232300809745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37143327308795286135492653 13928747740798232300809745)
            ·
              refine ⟨10446560805598674225607309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13928747740798232300809745 10446560805598674225607309)
              ·
                refine ⟨3917460302099502834602741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10446560805598674225607309 3917460302099502834602741)
                ·
                  refine ⟨367261903321828390744007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3917460302099502834602741 367261903321828390744007)
                  ·
                    rfl

theorem cell21_1609290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_1609290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609290 prefixEnd_1609290 := by exact prefixLift 1609290
  have htrace : WordTrace (prefixWord ++ tailWord_1609290) baseStart_1609290 baseEnd_1609290 := by
    simpa [prefixWord, tailWord_1609290, baseEnd_1609290] using wordTrace_append hprefix tailTrace_1609290
  have hstable : (prefixWord ++ tailWord_1609290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609290).length < 2 ^ (prefixWord ++ tailWord_1609290).sum := by decide
  have hdescent : baseEnd_1609290 < baseStart_1609290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609304 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_1609304 : Nat := 118140960795 + 1609304 * 2 ^ 59
def prefixEnd_1609304 : Nat := 4983230072969 + 3 ^ 40 * 1609304 * 2
def baseEnd_1609304 : Nat := 367265098312567477510645

theorem tailTrace_1609304 : CollatzResearch.WordTrace tailWord_1609304 prefixEnd_1609304 367265098312567477510645 := by
  unfold tailWord_1609304
  simp only [CollatzResearch.WordTrace]
  refine ⟨29348069480886965043301483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39130759307849286724401977 29348069480886965043301483)
  ·
    refine ⟨44022104221330447564952225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29348069480886965043301483 44022104221330447564952225)
    ·
      refine ⟨33016578165997835673714169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44022104221330447564952225 33016578165997835673714169)
      ·
        refine ⟨24762433624498376755285627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33016578165997835673714169 24762433624498376755285627)
        ·
          refine ⟨37143650436747565132928441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24762433624498376755285627 37143650436747565132928441)
          ·
            refine ⟨27857737827560673849696331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37143650436747565132928441 27857737827560673849696331)
            ·
              refine ⟨41786606741341010774544497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27857737827560673849696331 41786606741341010774544497)
              ·
                refine ⟨31339955056005758080908373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41786606741341010774544497 31339955056005758080908373)
                ·
                  refine ⟨367265098312567477510645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31339955056005758080908373 367265098312567477510645)
                  ·
                    rfl

theorem cell21_1609304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_1609304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609304 prefixEnd_1609304 := by exact prefixLift 1609304
  have htrace : WordTrace (prefixWord ++ tailWord_1609304) baseStart_1609304 baseEnd_1609304 := by
    simpa [prefixWord, tailWord_1609304, baseEnd_1609304] using wordTrace_append hprefix tailTrace_1609304
  have hstable : (prefixWord ++ tailWord_1609304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609304).length < 2 ^ (prefixWord ++ tailWord_1609304).sum := by decide
  have hdescent : baseEnd_1609304 < baseStart_1609304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609428 : List Nat := [2, 4, 1, 3, 1, 1, 2, 7]
def baseStart_1609428 : Nat := 118140960795 + 1609428 * 2 ^ 59
def prefixEnd_1609428 : Nat := 4983230072969 + 3 ^ 40 * 1609428 * 2
def baseEnd_1609428 : Nat := 122431132267323605814575

theorem tailTrace_1609428 : CollatzResearch.WordTrace tailWord_1609428 prefixEnd_1609428 122431132267323605814575 := by
  unfold tailWord_1609428
  simp only [CollatzResearch.WordTrace]
  refine ⟨29350330806662349632058469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39133774408883132842744625 29350330806662349632058469)
  ·
    refine ⟨5503187026249190556010963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29350330806662349632058469 5503187026249190556010963)
    ·
      refine ⟨8254780539373785834016445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5503187026249190556010963 8254780539373785834016445)
      ·
        refine ⟨3095542702265169687756167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8254780539373785834016445 3095542702265169687756167)
        ·
          refine ⟨4643314053397754531634251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3095542702265169687756167 4643314053397754531634251)
          ·
            refine ⟨6964971080096631797451377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4643314053397754531634251 6964971080096631797451377)
            ·
              refine ⟨5223728310072473848088533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6964971080096631797451377 5223728310072473848088533)
              ·
                refine ⟨122431132267323605814575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5223728310072473848088533 122431132267323605814575)
                ·
                  rfl

theorem cell21_1609428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_1609428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609428 prefixEnd_1609428 := by exact prefixLift 1609428
  have htrace : WordTrace (prefixWord ++ tailWord_1609428) baseStart_1609428 baseEnd_1609428 := by
    simpa [prefixWord, tailWord_1609428, baseEnd_1609428] using wordTrace_append hprefix tailTrace_1609428
  have hstable : (prefixWord ++ tailWord_1609428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609428).length < 2 ^ (prefixWord ++ tailWord_1609428).sum := by decide
  have hdescent : baseEnd_1609428 < baseStart_1609428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609473 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 4]
def baseStart_1609473 : Nat := 118140960795 + 1609473 * 2 ^ 59
def prefixEnd_1609473 : Nat := 4983230072969 + 3 ^ 40 * 1609473 * 2
def baseEnd_1609473 : Nat := 367303666415060739193633

theorem tailTrace_1609473 : CollatzResearch.WordTrace tailWord_1609473 prefixEnd_1609473 367303666415060739193633 := by
  unfold tailWord_1609473
  simp only [CollatzResearch.WordTrace]
  refine ⟨58702302898161671949505073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39134868598774447966336715 58702302898161671949505073)
  ·
    refine ⟨44026727173621253962128805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58702302898161671949505073 44026727173621253962128805)
    ·
      refine ⟨8255011345053985117899151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44026727173621253962128805 8255011345053985117899151)
      ·
        refine ⟨12382517017580977676848727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8255011345053985117899151 12382517017580977676848727)
        ·
          refine ⟨18573775526371466515273091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12382517017580977676848727 18573775526371466515273091)
          ·
            refine ⟨27860663289557199772909637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18573775526371466515273091 27860663289557199772909637)
            ·
              refine ⟨5223874366791974957420557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27860663289557199772909637 5223874366791974957420557)
              ·
                refine ⟨1958952887546990609032709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5223874366791974957420557 1958952887546990609032709)
                ·
                  refine ⟨367303666415060739193633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958952887546990609032709 367303666415060739193633)
                  ·
                    rfl

theorem cell21_1609473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_1609473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609473 prefixEnd_1609473 := by exact prefixLift 1609473
  have htrace : WordTrace (prefixWord ++ tailWord_1609473) baseStart_1609473 baseEnd_1609473 := by
    simpa [prefixWord, tailWord_1609473, baseEnd_1609473] using wordTrace_append hprefix tailTrace_1609473
  have hstable : (prefixWord ++ tailWord_1609473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609473).length < 2 ^ (prefixWord ++ tailWord_1609473).sum := by decide
  have hdescent : baseEnd_1609473 < baseStart_1609473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609628 : List Nat := [2, 2, 3, 3, 1, 2, 1, 4, 3]
def baseStart_1609628 : Nat := 118140960795 + 1609628 * 2 ^ 59
def prefixEnd_1609628 : Nat := 4983230072969 + 3 ^ 40 * 1609628 * 2
def baseEnd_1609628 : Nat := 367339039526814914109983

theorem tailTrace_1609628 : CollatzResearch.WordTrace tailWord_1609628 prefixEnd_1609628 367339039526814914109983 := by
  unfold tailWord_1609628
  simp only [CollatzResearch.WordTrace]
  refine ⟨29353978106300066710698769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39138637475066755614265025 29353978106300066710698769)
  ·
    refine ⟨22015483579725050033024077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29353978106300066710698769 22015483579725050033024077)
    ·
      refine ⟨8255806342396893762384029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22015483579725050033024077 8255806342396893762384029)
      ·
        refine ⟨3095927378398835160894011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8255806342396893762384029 3095927378398835160894011)
        ·
          refine ⟨4643891067598252741341017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3095927378398835160894011 4643891067598252741341017)
          ·
            refine ⟨3482918300698689556005763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4643891067598252741341017 3482918300698689556005763)
            ·
              refine ⟨5224377451048034334008645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3482918300698689556005763 5224377451048034334008645)
              ·
                refine ⟨979570772071506437626621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5224377451048034334008645 979570772071506437626621)
                ·
                  refine ⟨367339039526814914109983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979570772071506437626621 367339039526814914109983)
                  ·
                    rfl

theorem cell21_1609628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_1609628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609628 prefixEnd_1609628 := by exact prefixLift 1609628
  have htrace : WordTrace (prefixWord ++ tailWord_1609628) baseStart_1609628 baseEnd_1609628 := by
    simpa [prefixWord, tailWord_1609628, baseEnd_1609628] using wordTrace_append hprefix tailTrace_1609628
  have hstable : (prefixWord ++ tailWord_1609628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609628).length < 2 ^ (prefixWord ++ tailWord_1609628).sum := by decide
  have hdescent : baseEnd_1609628 < baseStart_1609628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609839 : List Nat := [1, 1, 2, 1, 3, 5, 2, 3, 3]
def baseStart_1609839 : Nat := 118140960795 + 1609839 * 2 ^ 59
def prefixEnd_1609839 : Nat := 4983230072969 + 3 ^ 40 * 1609839 * 2
def baseEnd_1609839 : Nat := 367387192601525436092885

theorem tailTrace_1609839 : CollatzResearch.WordTrace tailWord_1609839 prefixEnd_1609839 367387192601525436092885 := by
  unfold tailWord_1609839
  simp only [CollatzResearch.WordTrace]
  refine ⟨58715652014835716457328571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39143768009890477638219047 58715652014835716457328571)
  ·
    refine ⟨88073478022253574685992857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58715652014835716457328571 88073478022253574685992857)
    ·
      refine ⟨66055108516690181014494643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88073478022253574685992857 66055108516690181014494643)
      ·
        refine ⟨99082662775035271521741965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66055108516690181014494643 99082662775035271521741965)
        ·
          refine ⟨37155998540638226820653237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99082662775035271521741965 37155998540638226820653237)
          ·
            refine ⟨3483374863184833764436241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37155998540638226820653237 3483374863184833764436241)
            ·
              refine ⟨2612531147388625323327181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3483374863184833764436241 2612531147388625323327181)
              ·
                refine ⟨979699180270734496247693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2612531147388625323327181 979699180270734496247693)
                ·
                  refine ⟨367387192601525436092885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979699180270734496247693 367387192601525436092885)
                  ·
                    rfl

theorem cell21_1609839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 3].length) (baseStart_1609839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609839 prefixEnd_1609839 := by exact prefixLift 1609839
  have htrace : WordTrace (prefixWord ++ tailWord_1609839) baseStart_1609839 baseEnd_1609839 := by
    simpa [prefixWord, tailWord_1609839, baseEnd_1609839] using wordTrace_append hprefix tailTrace_1609839
  have hstable : (prefixWord ++ tailWord_1609839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609839).length < 2 ^ (prefixWord ++ tailWord_1609839).sum := by decide
  have hdescent : baseEnd_1609839 < baseStart_1609839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609853 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 4]
def baseStart_1609853 : Nat := 118140960795 + 1609853 * 2 ^ 59
def prefixEnd_1609853 : Nat := 4983230072969 + 3 ^ 40 * 1609853 * 2
def baseEnd_1609853 : Nat := 367390387592264522859523

theorem tailTrace_1609853 : CollatzResearch.WordTrace tailWord_1609853 prefixEnd_1609853 367390387592264522859523 := by
  unfold tailWord_1609853
  simp only [CollatzResearch.WordTrace]
  refine ⟨58716162636784996848338213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39144108424523331232225475 58716162636784996848338213)
  ·
    refine ⟨11009280494397186909063415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58716162636784996848338213 11009280494397186909063415)
    ·
      refine ⟨16513920741595780363595123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11009280494397186909063415 16513920741595780363595123)
      ·
        refine ⟨24770881112393670545392685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16513920741595780363595123 24770881112393670545392685)
        ·
          refine ⟨9289080417147626454522257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24770881112393670545392685 9289080417147626454522257)
          ·
            refine ⟨6966810312860719840891693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9289080417147626454522257 6966810312860719840891693)
            ·
              refine ⟨2612553867322769940334385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6966810312860719840891693 2612553867322769940334385)
              ·
                refine ⟨1959415400492077455250789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612553867322769940334385 1959415400492077455250789)
                ·
                  refine ⟨367390387592264522859523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1959415400492077455250789 367390387592264522859523)
                  ·
                    rfl

theorem cell21_1609853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_1609853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609853 prefixEnd_1609853 := by exact prefixLift 1609853
  have htrace : WordTrace (prefixWord ++ tailWord_1609853) baseStart_1609853 baseEnd_1609853 := by
    simpa [prefixWord, tailWord_1609853, baseEnd_1609853] using wordTrace_append hprefix tailTrace_1609853
  have hstable : (prefixWord ++ tailWord_1609853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609853).length < 2 ^ (prefixWord ++ tailWord_1609853).sum := by decide
  have hdescent : baseEnd_1609853 < baseStart_1609853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609912 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_1609912 : Nat := 118140960795 + 1609912 * 2 ^ 59
def prefixEnd_1609912 : Nat := 4983230072969 + 3 ^ 40 * 1609912 * 2
def baseEnd_1609912 : Nat := 367403852196093531376069

theorem tailTrace_1609912 : CollatzResearch.WordTrace tailWord_1609912 prefixEnd_1609912 367403852196093531376069 := by
  unfold tailWord_1609912
  simp only [CollatzResearch.WordTrace]
  refine ⟨29359157271785624962367995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39145543029047499949823993 29359157271785624962367995)
  ·
    refine ⟨44038735907678437443551993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29359157271785624962367995 44038735907678437443551993)
    ·
      refine ⟨33029051930758828082663995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44038735907678437443551993 33029051930758828082663995)
      ·
        refine ⟨49543577896138242123995993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33029051930758828082663995 49543577896138242123995993)
        ·
          refine ⟨37157683422103681592996995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49543577896138242123995993 37157683422103681592996995)
          ·
            refine ⟨55736525133155522389495493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37157683422103681592996995 55736525133155522389495493)
            ·
              refine ⟨10450598462466660448030405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55736525133155522389495493 10450598462466660448030405)
              ·
                refine ⟨1959487211712498834005701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10450598462466660448030405 1959487211712498834005701)
                ·
                  refine ⟨367403852196093531376069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1959487211712498834005701 367403852196093531376069)
                  ·
                    rfl

theorem cell21_1609912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_1609912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609912 prefixEnd_1609912 := by exact prefixLift 1609912
  have htrace : WordTrace (prefixWord ++ tailWord_1609912) baseStart_1609912 baseEnd_1609912 := by
    simpa [prefixWord, tailWord_1609912, baseEnd_1609912] using wordTrace_append hprefix tailTrace_1609912
  have hstable : (prefixWord ++ tailWord_1609912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609912).length < 2 ^ (prefixWord ++ tailWord_1609912).sum := by decide
  have hdescent : baseEnd_1609912 < baseStart_1609912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609915 : List Nat := [1, 1, 1, 1, 1, 2, 9, 2, 3]
def baseStart_1609915 : Nat := 118140960795 + 1609915 * 2 ^ 59
def prefixEnd_1609915 : Nat := 4983230072969 + 3 ^ 40 * 1609915 * 2
def baseEnd_1609915 : Nat := 367404536836966192826063

theorem tailTrace_1609915 : CollatzResearch.WordTrace tailWord_1609915 prefixEnd_1609915 367404536836966192826063 := by
  unfold tailWord_1609915
  simp only [CollatzResearch.WordTrace]
  refine ⟨58718423962560381437095199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39145615975040254291396799 58718423962560381437095199)
  ·
    refine ⟨88077635943840572155642799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58718423962560381437095199 88077635943840572155642799)
    ·
      refine ⟨132116453915760858233464199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88077635943840572155642799 132116453915760858233464199)
      ·
        refine ⟨198174680873641287350196299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132116453915760858233464199 198174680873641287350196299)
        ·
          refine ⟨297262021310461931025294449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198174680873641287350196299 297262021310461931025294449)
          ·
            refine ⟨222946515982846448268970837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297262021310461931025294449 222946515982846448268970837)
            ·
              refine ⟨1306327242086990907826001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 222946515982846448268970837 1306327242086990907826001)
              ·
                refine ⟨979745431565243180869501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306327242086990907826001 979745431565243180869501)
                ·
                  refine ⟨367404536836966192826063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979745431565243180869501 367404536836966192826063)
                  ·
                    rfl

theorem cell21_1609915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 3].length) (baseStart_1609915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609915 prefixEnd_1609915 := by exact prefixLift 1609915
  have htrace : WordTrace (prefixWord ++ tailWord_1609915) baseStart_1609915 baseEnd_1609915 := by
    simpa [prefixWord, tailWord_1609915, baseEnd_1609915] using wordTrace_append hprefix tailTrace_1609915
  have hstable : (prefixWord ++ tailWord_1609915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609915).length < 2 ^ (prefixWord ++ tailWord_1609915).sum := by decide
  have hdescent : baseEnd_1609915 < baseStart_1609915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609991 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 5]
def baseStart_1609991 : Nat := 118140960795 + 1609991 * 2 ^ 59
def prefixEnd_1609991 : Nat := 4983230072969 + 3 ^ 40 * 1609991 * 2
def baseEnd_1609991 : Nat := 367421881072406949559241

theorem tailTrace_1609991 : CollatzResearch.WordTrace tailWord_1609991 prefixEnd_1609991 367421881072406949559241 := by
  unfold tailWord_1609991
  simp only [CollatzResearch.WordTrace]
  refine ⟨58721195910285046416861827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39147463940190030944574551 58721195910285046416861827)
  ·
    refine ⟨88081793865427569625292741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58721195910285046416861827 88081793865427569625292741)
    ·
      refine ⟨16515336349767669304742389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88081793865427569625292741 16515336349767669304742389)
      ·
        refine ⟨1548312782790718997319599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16515336349767669304742389 1548312782790718997319599)
        ·
          refine ⟨2322469174186078495979399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548312782790718997319599 2322469174186078495979399)
          ·
            refine ⟨3483703761279117743969099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322469174186078495979399 3483703761279117743969099)
            ·
              refine ⟨5225555641918676615953649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483703761279117743969099 5225555641918676615953649)
              ·
                refine ⟨3919166731439007461965237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5225555641918676615953649 3919166731439007461965237)
                ·
                  refine ⟨367421881072406949559241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3919166731439007461965237 367421881072406949559241)
                  ·
                    rfl

theorem cell21_1609991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 5].length) (baseStart_1609991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1609991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1609991 prefixEnd_1609991 := by exact prefixLift 1609991
  have htrace : WordTrace (prefixWord ++ tailWord_1609991) baseStart_1609991 baseEnd_1609991 := by
    simpa [prefixWord, tailWord_1609991, baseEnd_1609991] using wordTrace_append hprefix tailTrace_1609991
  have hstable : (prefixWord ++ tailWord_1609991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609991).length < 2 ^ (prefixWord ++ tailWord_1609991).sum := by decide
  have hdescent : baseEnd_1609991 < baseStart_1609991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610098 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_1610098 : Nat := 118140960795 + 1610098 * 2 ^ 59
def prefixEnd_1610098 : Nat := 4983230072969 + 3 ^ 40 * 1610098 * 2
def baseEnd_1610098 : Nat := 367446299930198541275689

theorem tailTrace_1610098 : CollatzResearch.WordTrace tailWord_1610098 prefixEnd_1610098 367446299930198541275689 := by
  unfold tailWord_1610098
  simp only [CollatzResearch.WordTrace]
  refine ⟨14681274630224350922751737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39150065680598269127337965 14681274630224350922751737)
  ·
    refine ⟨11010955972668263192063803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14681274630224350922751737 11010955972668263192063803)
    ·
      refine ⟨16516433959002394788095705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11010955972668263192063803 16516433959002394788095705)
      ·
        refine ⟨12387325469251796091071779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16516433959002394788095705 12387325469251796091071779)
        ·
          refine ⟨18580988203877694136607669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12387325469251796091071779 18580988203877694136607669)
          ·
            refine ⟨1741967644113533825306969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18580988203877694136607669 1741967644113533825306969)
            ·
              refine ⟨1306475733085150368980227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1741967644113533825306969 1306475733085150368980227)
              ·
                refine ⟨1959713599627725553470341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306475733085150368980227 1959713599627725553470341)
                ·
                  refine ⟨367446299930198541275689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1959713599627725553470341 367446299930198541275689)
                  ·
                    rfl

theorem cell21_1610098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_1610098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610098 prefixEnd_1610098 := by exact prefixLift 1610098
  have htrace : WordTrace (prefixWord ++ tailWord_1610098) baseStart_1610098 baseEnd_1610098 := by
    simpa [prefixWord, tailWord_1610098, baseEnd_1610098] using wordTrace_append hprefix tailTrace_1610098
  have hstable : (prefixWord ++ tailWord_1610098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610098).length < 2 ^ (prefixWord ++ tailWord_1610098).sum := by decide
  have hdescent : baseEnd_1610098 < baseStart_1610098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610202 : List Nat := [3, 1, 1, 2, 3, 1, 1, 6, 3]
def baseStart_1610202 : Nat := 118140960795 + 1610202 * 2 ^ 59
def prefixEnd_1610202 : Nat := 4983230072969 + 3 ^ 40 * 1610202 * 2
def baseEnd_1610202 : Nat := 367470034147117471542143

theorem tailTrace_1610202 : CollatzResearch.WordTrace tailWord_1610202 prefixEnd_1610202 367470034147117471542143 := by
  unfold tailWord_1610202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682222928130157363198215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39152594475013752968528573 14682222928130157363198215)
  ·
    refine ⟨22023334392195236044797323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14682222928130157363198215 22023334392195236044797323)
    ·
      refine ⟨33035001588292854067195985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22023334392195236044797323 33035001588292854067195985)
      ·
        refine ⟨24776251191219640550396989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33035001588292854067195985 24776251191219640550396989)
        ·
          refine ⟨9291094196707365206398871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24776251191219640550396989 9291094196707365206398871)
          ·
            refine ⟨13936641295061047809598307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9291094196707365206398871 13936641295061047809598307)
            ·
              refine ⟨20904961942591571714397461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13936641295061047809598307 20904961942591571714397461)
              ·
                refine ⟨979920091058979924112381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20904961942591571714397461 979920091058979924112381)
                ·
                  refine ⟨367470034147117471542143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979920091058979924112381 367470034147117471542143)
                  ·
                    rfl

theorem cell21_1610202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_1610202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610202 prefixEnd_1610202 := by exact prefixLift 1610202
  have htrace : WordTrace (prefixWord ++ tailWord_1610202) baseStart_1610202 baseEnd_1610202 := by
    simpa [prefixWord, tailWord_1610202, baseEnd_1610202] using wordTrace_append hprefix tailTrace_1610202
  have hstable : (prefixWord ++ tailWord_1610202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610202).length < 2 ^ (prefixWord ++ tailWord_1610202).sum := by decide
  have hdescent : baseEnd_1610202 < baseStart_1610202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610247 : List Nat := [1, 1, 4, 3, 3, 2, 7]
def baseStart_1610247 : Nat := 118140960795 + 1610247 * 2 ^ 59
def prefixEnd_1610247 : Nat := 4983230072969 + 3 ^ 40 * 1610247 * 2
def baseEnd_1610247 : Nat := 40831144862245265921339

theorem tailTrace_1610247 : CollatzResearch.WordTrace tailWord_1610247 prefixEnd_1610247 40831144862245265921339 := by
  unfold tailWord_1610247
  simp only [CollatzResearch.WordTrace]
  refine ⟨58730532997357602138180995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39153688664905068092120663 58730532997357602138180995)
  ·
    refine ⟨88095799496036403207271493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58730532997357602138180995 88095799496036403207271493)
    ·
      refine ⟨16517962405506825601363405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88095799496036403207271493 16517962405506825601363405)
      ·
        refine ⟨6194235902065059600511277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16517962405506825601363405 6194235902065059600511277)
        ·
          refine ⟨2322838463274397350191729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6194235902065059600511277 2322838463274397350191729)
          ·
            refine ⟨1742128847455798012643797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2322838463274397350191729 1742128847455798012643797)
            ·
              refine ⟨40831144862245265921339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1742128847455798012643797 40831144862245265921339)
              ·
                rfl

theorem cell21_1610247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 7].length) (baseStart_1610247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610247 prefixEnd_1610247 := by exact prefixLift 1610247
  have htrace : WordTrace (prefixWord ++ tailWord_1610247) baseStart_1610247 baseEnd_1610247 := by
    simpa [prefixWord, tailWord_1610247, baseEnd_1610247] using wordTrace_append hprefix tailTrace_1610247
  have hstable : (prefixWord ++ tailWord_1610247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610247).length < 2 ^ (prefixWord ++ tailWord_1610247).sum := by decide
  have hdescent : baseEnd_1610247 < baseStart_1610247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610337 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 5]
def baseStart_1610337 : Nat := 118140960795 + 1610337 * 2 ^ 59
def prefixEnd_1610337 : Nat := 4983230072969 + 3 ^ 40 * 1610337 * 2
def baseEnd_1610337 : Nat := 367500842986387236791867

theorem tailTrace_1610337 : CollatzResearch.WordTrace tailWord_1610337 prefixEnd_1610337 367500842986387236791867 := by
  unfold tailWord_1610337
  simp only [CollatzResearch.WordTrace]
  refine ⟨58733815567031547508957265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39155877044687698339304843 58733815567031547508957265)
  ·
    refine ⟨44050361675273660631717949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58733815567031547508957265 44050361675273660631717949)
    ·
      refine ⟨16518885628227622736894231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44050361675273660631717949 16518885628227622736894231)
      ·
        refine ⟨24778328442341434105341347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16518885628227622736894231 24778328442341434105341347)
        ·
          refine ⟨37167492663512151158012021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24778328442341434105341347 37167492663512151158012021)
          ·
            refine ⟨3484452437204264171063627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37167492663512151158012021 3484452437204264171063627)
            ·
              refine ⟨5226678655806396256595441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484452437204264171063627 5226678655806396256595441)
              ·
                refine ⟨3920008991854797192446581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5226678655806396256595441 3920008991854797192446581)
                ·
                  refine ⟨367500842986387236791867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3920008991854797192446581 367500842986387236791867)
                  ·
                    rfl

theorem cell21_1610337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_1610337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610337 prefixEnd_1610337 := by exact prefixLift 1610337
  have htrace : WordTrace (prefixWord ++ tailWord_1610337) baseStart_1610337 baseEnd_1610337 := by
    simpa [prefixWord, tailWord_1610337, baseEnd_1610337] using wordTrace_append hprefix tailTrace_1610337
  have hstable : (prefixWord ++ tailWord_1610337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610337).length < 2 ^ (prefixWord ++ tailWord_1610337).sum := by decide
  have hdescent : baseEnd_1610337 < baseStart_1610337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610368 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_1610368 : Nat := 118140960795 + 1610368 * 2 ^ 59
def prefixEnd_1610368 : Nat := 4983230072969 + 3 ^ 40 * 1610368 * 2
def baseEnd_1610368 : Nat := 367507917608738071775137

theorem tailTrace_1610368 : CollatzResearch.WordTrace tailWord_1610368 prefixEnd_1610368 367507917608738071775137 := by
  unfold tailWord_1610368
  simp only [CollatzResearch.WordTrace]
  refine ⟨29367473114959619901667879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39156630819946159868890505 29367473114959619901667879)
  ·
    refine ⟨44051209672439429852501819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29367473114959619901667879 44051209672439429852501819)
    ·
      refine ⟨66076814508659144778752729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44051209672439429852501819 66076814508659144778752729)
      ·
        refine ⟨49557610881494358584064547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66076814508659144778752729 49557610881494358584064547)
        ·
          refine ⟨74336416322241537876096821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49557610881494358584064547 74336416322241537876096821)
          ·
            refine ⟨6969039030210144175884077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74336416322241537876096821 6969039030210144175884077)
            ·
              refine ⟨2613389636328804065956529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6969039030210144175884077 2613389636328804065956529)
              ·
                refine ⟨1960042227246603049467397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2613389636328804065956529 1960042227246603049467397)
                ·
                  refine ⟨367507917608738071775137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1960042227246603049467397 367507917608738071775137)
                  ·
                    rfl

theorem cell21_1610368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_1610368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610368 prefixEnd_1610368 := by exact prefixLift 1610368
  have htrace : WordTrace (prefixWord ++ tailWord_1610368) baseStart_1610368 baseEnd_1610368 := by
    simpa [prefixWord, tailWord_1610368, baseEnd_1610368] using wordTrace_append hprefix tailTrace_1610368
  have hstable : (prefixWord ++ tailWord_1610368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610368).length < 2 ^ (prefixWord ++ tailWord_1610368).sum := by decide
  have hdescent : baseEnd_1610368 < baseStart_1610368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610382 : List Nat := [4, 1, 1, 3, 1, 1, 2, 8]
def baseStart_1610382 : Nat := 118140960795 + 1610382 * 2 ^ 59
def prefixEnd_1610382 : Nat := 4983230072969 + 3 ^ 40 * 1610382 * 2
def baseEnd_1610382 : Nat := 122503704199825719513925

theorem tailTrace_1610382 : CollatzResearch.WordTrace tailWord_1610382 prefixEnd_1610382 122503704199825719513925 := by
  unfold tailWord_1610382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341932106483565024293175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39156971234579013462896933 7341932106483565024293175)
  ·
    refine ⟨11012898159725347536439763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7341932106483565024293175 11012898159725347536439763)
    ·
      refine ⟨16519347239588021304659645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11012898159725347536439763 16519347239588021304659645)
      ·
        refine ⟨6194755214845507989247367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16519347239588021304659645 6194755214845507989247367)
        ·
          refine ⟨9292132822268261983871051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6194755214845507989247367 9292132822268261983871051)
          ·
            refine ⟨13938199233402392975806577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9292132822268261983871051 13938199233402392975806577)
            ·
              refine ⟨10453649425051794731854933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13938199233402392975806577 10453649425051794731854933)
              ·
                refine ⟨122503704199825719513925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10453649425051794731854933 122503704199825719513925)
                ·
                  rfl

theorem cell21_1610382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_1610382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610382 prefixEnd_1610382 := by exact prefixLift 1610382
  have htrace : WordTrace (prefixWord ++ tailWord_1610382) baseStart_1610382 baseEnd_1610382 := by
    simpa [prefixWord, tailWord_1610382, baseEnd_1610382] using wordTrace_append hprefix tailTrace_1610382
  have hstable : (prefixWord ++ tailWord_1610382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610382).length < 2 ^ (prefixWord ++ tailWord_1610382).sum := by decide
  have hdescent : baseEnd_1610382 < baseStart_1610382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610599 : List Nat := [1, 1, 5, 1, 2, 3, 3, 2, 3]
def baseStart_1610599 : Nat := 118140960795 + 1610599 * 2 ^ 59
def prefixEnd_1610599 : Nat := 4983230072969 + 3 ^ 40 * 1610599 * 2
def baseEnd_1610599 : Nat := 367560634955933003424665

theorem tailTrace_1610599 : CollatzResearch.WordTrace tailWord_1610599 prefixEnd_1610599 367560634955933003424665 := by
  unfold tailWord_1610599
  simp only [CollatzResearch.WordTrace]
  refine ⟨58743371492082366254994851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39162247661388244169996567 58743371492082366254994851)
  ·
    refine ⟨88115057238123549382492277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58743371492082366254994851 88115057238123549382492277)
    ·
      refine ⟨8260786616074082754608651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88115057238123549382492277 8260786616074082754608651)
      ·
        refine ⟨12391179924111124131912977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8260786616074082754608651 12391179924111124131912977)
        ·
          refine ⟨9293384943083343098934733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12391179924111124131912977 9293384943083343098934733)
          ·
            refine ⟨3485019353656253662100525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9293384943083343098934733 3485019353656253662100525)
            ·
              refine ⟨1306882257621095123287697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3485019353656253662100525 1306882257621095123287697)
              ·
                refine ⟨980161693215821342465773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306882257621095123287697 980161693215821342465773)
                ·
                  refine ⟨367560634955933003424665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980161693215821342465773 367560634955933003424665)
                  ·
                    rfl

theorem cell21_1610599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 3].length) (baseStart_1610599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610599 prefixEnd_1610599 := by exact prefixLift 1610599
  have htrace : WordTrace (prefixWord ++ tailWord_1610599) baseStart_1610599 baseEnd_1610599 := by
    simpa [prefixWord, tailWord_1610599, baseEnd_1610599] using wordTrace_append hprefix tailTrace_1610599
  have hstable : (prefixWord ++ tailWord_1610599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610599).length < 2 ^ (prefixWord ++ tailWord_1610599).sum := by decide
  have hdescent : baseEnd_1610599 < baseStart_1610599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610613 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 4]
def baseStart_1610613 : Nat := 118140960795 + 1610613 * 2 ^ 59
def prefixEnd_1610613 : Nat := 4983230072969 + 3 ^ 40 * 1610613 * 2
def baseEnd_1610613 : Nat := 367563829946672090191303

theorem tailTrace_1610613 : CollatzResearch.WordTrace tailWord_1610613 prefixEnd_1610613 367563829946672090191303 := by
  unfold tailWord_1610613
  simp only [CollatzResearch.WordTrace]
  refine ⟨58743882114031646646004493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39162588076021097764002995 58743882114031646646004493)
  ·
    refine ⟨22028955792761867492251685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58743882114031646646004493 22028955792761867492251685)
    ·
      refine ⟨4130429211142850154797191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22028955792761867492251685 4130429211142850154797191)
      ·
        refine ⟨6195643816714275232195787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130429211142850154797191 6195643816714275232195787)
        ·
          refine ⟨9293465725071412848293681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6195643816714275232195787 9293465725071412848293681)
          ·
            refine ⟨6970099293803559636220261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9293465725071412848293681 6970099293803559636220261)
            ·
              refine ⟨1306893617588167431791299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6970099293803559636220261 1306893617588167431791299)
              ·
                refine ⟨1960340426382251147686949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306893617588167431791299 1960340426382251147686949)
                ·
                  refine ⟨367563829946672090191303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1960340426382251147686949 367563829946672090191303)
                  ·
                    rfl

theorem cell21_1610613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_1610613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610613 prefixEnd_1610613 := by exact prefixLift 1610613
  have htrace : WordTrace (prefixWord ++ tailWord_1610613) baseStart_1610613 baseEnd_1610613 := by
    simpa [prefixWord, tailWord_1610613, baseEnd_1610613] using wordTrace_append hprefix tailTrace_1610613
  have hstable : (prefixWord ++ tailWord_1610613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610613).length < 2 ^ (prefixWord ++ tailWord_1610613).sum := by decide
  have hdescent : baseEnd_1610613 < baseStart_1610613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610641 : List Nat := [1, 2, 2, 1, 1, 1, 3, 7, 3]
def baseStart_1610641 : Nat := 118140960795 + 1610641 * 2 ^ 59
def prefixEnd_1610641 : Nat := 4983230072969 + 3 ^ 40 * 1610641 * 2
def baseEnd_1610641 : Nat := 367570219928150263724579

theorem tailTrace_1610641 : CollatzResearch.WordTrace tailWord_1610641 prefixEnd_1610641 367570219928150263724579 := by
  unfold tailWord_1610641
  simp only [CollatzResearch.WordTrace]
  refine ⟨58744903357930207428023777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39163268905286804952015851 58744903357930207428023777)
  ·
    refine ⟨44058677518447655571017833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58744903357930207428023777 44058677518447655571017833)
    ·
      refine ⟨33044008138835741678263375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44058677518447655571017833 33044008138835741678263375)
      ·
        refine ⟨49566012208253612517395063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33044008138835741678263375 49566012208253612517395063)
        ·
          refine ⟨74349018312380418776092595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49566012208253612517395063 74349018312380418776092595)
          ·
            refine ⟨111523527468570628164138893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74349018312380418776092595 111523527468570628164138893)
            ·
              refine ⟨41821322800713985561552085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111523527468570628164138893 41821322800713985561552085)
              ·
                refine ⟨980187253141734036598877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41821322800713985561552085 980187253141734036598877)
                ·
                  refine ⟨367570219928150263724579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980187253141734036598877 367570219928150263724579)
                  ·
                    rfl

theorem cell21_1610641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 3].length) (baseStart_1610641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610641 prefixEnd_1610641 := by exact prefixLift 1610641
  have htrace : WordTrace (prefixWord ++ tailWord_1610641) baseStart_1610641 baseEnd_1610641 := by
    simpa [prefixWord, tailWord_1610641, baseEnd_1610641] using wordTrace_append hprefix tailTrace_1610641
  have hstable : (prefixWord ++ tailWord_1610641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610641).length < 2 ^ (prefixWord ++ tailWord_1610641).sum := by decide
  have hdescent : baseEnd_1610641 < baseStart_1610641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610678 : List Nat := [5, 1, 4, 1, 1, 1, 3, 5]
def baseStart_1610678 : Nat := 118140960795 + 1610678 * 2 ^ 59
def prefixEnd_1610678 : Nat := 4983230072969 + 3 ^ 40 * 1610678 * 2
def baseEnd_1610678 : Nat := 122526221277415473869279

theorem tailTrace_1610678 : CollatzResearch.WordTrace tailWord_1610678 prefixEnd_1610678 122526221277415473869279 := by
  unfold tailWord_1610678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3671640803674760171695043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39164168572530775164747125 3671640803674760171695043)
  ·
    refine ⟨5507461205512140257542565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3671640803674760171695043 5507461205512140257542565)
    ·
      refine ⟨1032648976033526298289231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5507461205512140257542565 1032648976033526298289231)
      ·
        refine ⟨1548973464050289447433847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032648976033526298289231 1548973464050289447433847)
        ·
          refine ⟨2323460196075434171150771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548973464050289447433847 2323460196075434171150771)
          ·
            refine ⟨3485190294113151256726157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323460196075434171150771 3485190294113151256726157)
            ·
              refine ⟨1306946360292431721272309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3485190294113151256726157 1306946360292431721272309)
              ·
                refine ⟨122526221277415473869279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1306946360292431721272309 122526221277415473869279)
                ·
                  rfl

theorem cell21_1610678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_1610678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610678 prefixEnd_1610678 := by exact prefixLift 1610678
  have htrace : WordTrace (prefixWord ++ tailWord_1610678) baseStart_1610678 baseEnd_1610678 := by
    simpa [prefixWord, tailWord_1610678, baseEnd_1610678] using wordTrace_append hprefix tailTrace_1610678
  have hstable : (prefixWord ++ tailWord_1610678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610678).length < 2 ^ (prefixWord ++ tailWord_1610678).sum := by decide
  have hdescent : baseEnd_1610678 < baseStart_1610678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610692 : List Nat := [2, 3, 3, 3, 1, 1, 2, 3, 3]
def baseStart_1610692 : Nat := 118140960795 + 1610692 * 2 ^ 59
def prefixEnd_1610692 : Nat := 4983230072969 + 3 ^ 40 * 1610692 * 2
def baseEnd_1610692 : Nat := 367581858822985508374475

theorem tailTrace_1610692 : CollatzResearch.WordTrace tailWord_1610692 prefixEnd_1610692 367581858822985508374475 := by
  unfold tailWord_1610692
  simp only [CollatzResearch.WordTrace]
  refine ⟨29373381740372721569065165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39164508987163628758753553 29373381740372721569065165)
  ·
    refine ⟨11015018152639770588399437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29373381740372721569065165 11015018152639770588399437)
    ·
      refine ⟨4130631807239913970649789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11015018152639770588399437 4130631807239913970649789)
      ·
        refine ⟨1548986927714967738993671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4130631807239913970649789 1548986927714967738993671)
        ·
          refine ⟨2323480391572451608490507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548986927714967738993671 2323480391572451608490507)
          ·
            refine ⟨3485220587358677412735761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323480391572451608490507 3485220587358677412735761)
            ·
              refine ⟨2613915440519008059551821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3485220587358677412735761 2613915440519008059551821)
              ·
                refine ⟨980218290194628022331933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2613915440519008059551821 980218290194628022331933)
                ·
                  refine ⟨367581858822985508374475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980218290194628022331933 367581858822985508374475)
                  ·
                    rfl

theorem cell21_1610692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_1610692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610692 prefixEnd_1610692 := by exact prefixLift 1610692
  have htrace : WordTrace (prefixWord ++ tailWord_1610692) baseStart_1610692 baseEnd_1610692 := by
    simpa [prefixWord, tailWord_1610692, baseEnd_1610692] using wordTrace_append hprefix tailTrace_1610692
  have hstable : (prefixWord ++ tailWord_1610692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610692).length < 2 ^ (prefixWord ++ tailWord_1610692).sum := by decide
  have hdescent : baseEnd_1610692 < baseStart_1610692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610700 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_1610700 : Nat := 118140960795 + 1610700 * 2 ^ 59
def prefixEnd_1610700 : Nat := 4983230072969 + 3 ^ 40 * 1610700 * 2
def baseEnd_1610700 : Nat := 367583684531979272241125

theorem tailTrace_1610700 : CollatzResearch.WordTrace tailWord_1610700 prefixEnd_1610700 367583684531979272241125 := by
  unfold tailWord_1610700
  simp only [CollatzResearch.WordTrace]
  refine ⟨29373527632358230252210777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39164703509810973669614369 29373527632358230252210777)
  ·
    refine ⟨22030145724268672689158083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29373527632358230252210777 22030145724268672689158083)
    ·
      refine ⟨33045218586403009033737125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22030145724268672689158083 33045218586403009033737125)
      ·
        refine ⟨6195978484950564193825711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33045218586403009033737125 6195978484950564193825711)
        ·
          refine ⟨9293967727425846290738567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6195978484950564193825711 9293967727425846290738567)
          ·
            refine ⟨13940951591138769436107851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9293967727425846290738567 13940951591138769436107851)
            ·
              refine ⟨20911427386708154154161777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13940951591138769436107851 20911427386708154154161777)
              ·
                refine ⟨15683570540031115615621333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20911427386708154154161777 15683570540031115615621333)
                ·
                  refine ⟨367583684531979272241125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15683570540031115615621333 367583684531979272241125)
                  ·
                    rfl

theorem cell21_1610700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_1610700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610700 prefixEnd_1610700 := by exact prefixLift 1610700
  have htrace : WordTrace (prefixWord ++ tailWord_1610700) baseStart_1610700 baseEnd_1610700 := by
    simpa [prefixWord, tailWord_1610700, baseEnd_1610700] using wordTrace_append hprefix tailTrace_1610700
  have hstable : (prefixWord ++ tailWord_1610700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610700).length < 2 ^ (prefixWord ++ tailWord_1610700).sum := by decide
  have hdescent : baseEnd_1610700 < baseStart_1610700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610717 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1610717 : Nat := 118140960795 + 1610717 * 2 ^ 59
def prefixEnd_1610717 : Nat := 4983230072969 + 3 ^ 40 * 1610717 * 2
def baseEnd_1610717 : Nat := 367587564163591020457757

theorem tailTrace_1610717 : CollatzResearch.WordTrace tailWord_1610717 prefixEnd_1610717 367587564163591020457757 := by
  unfold tailWord_1610717
  simp only [CollatzResearch.WordTrace]
  refine ⟨58747675305654872407790405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39165116870436581605193603 58747675305654872407790405)
  ·
    refine ⟨11015189119810288576460701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58747675305654872407790405 11015189119810288576460701)
    ·
      refine ⟨4130695919928858216172763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11015189119810288576460701 4130695919928858216172763)
      ·
        refine ⟨6196043879893287324259145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130695919928858216172763 6196043879893287324259145)
        ·
          refine ⟨4647032909919965493194359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6196043879893287324259145 4647032909919965493194359)
          ·
            refine ⟨6970549364879948239791539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4647032909919965493194359 6970549364879948239791539)
            ·
              refine ⟨10455824047319922359687309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6970549364879948239791539 10455824047319922359687309)
              ·
                refine ⟨3920934017744970884882741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10455824047319922359687309 3920934017744970884882741)
                ·
                  refine ⟨367587564163591020457757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3920934017744970884882741 367587564163591020457757)
                  ·
                    rfl

theorem cell21_1610717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1610717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610717 prefixEnd_1610717 := by exact prefixLift 1610717
  have htrace : WordTrace (prefixWord ++ tailWord_1610717) baseStart_1610717 baseEnd_1610717 := by
    simpa [prefixWord, tailWord_1610717, baseEnd_1610717] using wordTrace_append hprefix tailTrace_1610717
  have hstable : (prefixWord ++ tailWord_1610717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610717).length < 2 ^ (prefixWord ++ tailWord_1610717).sum := by decide
  have hdescent : baseEnd_1610717 < baseStart_1610717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610745 : List Nat := [1, 2, 1, 3, 1, 3, 3, 7]
def baseStart_1610745 : Nat := 118140960795 + 1610745 * 2 ^ 59
def prefixEnd_1610745 : Nat := 4983230072969 + 3 ^ 40 * 1610745 * 2
def baseEnd_1610745 : Nat := 122531318048356397997011

theorem tailTrace_1610745 : CollatzResearch.WordTrace tailWord_1610745 prefixEnd_1610745 122531318048356397997011 := by
  unfold tailWord_1610745
  simp only [CollatzResearch.WordTrace]
  refine ⟨58748696549553433189809689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39165797699702288793206459 58748696549553433189809689)
  ·
    refine ⟨44061522412165074892357267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58748696549553433189809689 44061522412165074892357267)
    ·
      refine ⟨66092283618247612338535901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44061522412165074892357267 66092283618247612338535901)
      ·
        refine ⟨24784606356842854626950963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66092283618247612338535901 24784606356842854626950963)
        ·
          refine ⟨37176909535264281940426445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24784606356842854626950963 37176909535264281940426445)
          ·
            refine ⟨13941341075724105727659917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37176909535264281940426445 13941341075724105727659917)
            ·
              refine ⟨5228002903396539647872469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13941341075724105727659917 5228002903396539647872469)
              ·
                refine ⟨122531318048356397997011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5228002903396539647872469 122531318048356397997011)
                ·
                  rfl

theorem cell21_1610745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 7].length) (baseStart_1610745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610745 prefixEnd_1610745 := by exact prefixLift 1610745
  have htrace : WordTrace (prefixWord ++ tailWord_1610745) baseStart_1610745 baseEnd_1610745 := by
    simpa [prefixWord, tailWord_1610745, baseEnd_1610745] using wordTrace_append hprefix tailTrace_1610745
  have hstable : (prefixWord ++ tailWord_1610745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610745).length < 2 ^ (prefixWord ++ tailWord_1610745).sum := by decide
  have hdescent : baseEnd_1610745 < baseStart_1610745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610762 : List Nat := [3, 1, 2, 2, 3, 3, 7]
def baseStart_1610762 : Nat := 118140960795 + 1610762 * 2 ^ 59
def prefixEnd_1610762 : Nat := 4983230072969 + 3 ^ 40 * 1610762 * 2
def baseEnd_1610762 : Nat := 40844203752964549134185

theorem tailTrace_1610762 : CollatzResearch.WordTrace tailWord_1610762 prefixEnd_1610762 40844203752964549134185 := by
  unfold tailWord_1610762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14687329147622961273294635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39166211060327896728785693 14687329147622961273294635)
  ·
    refine ⟨22030993721434441909941953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14687329147622961273294635 22030993721434441909941953)
    ·
      refine ⟨16523245291075831432456465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22030993721434441909941953 16523245291075831432456465)
      ·
        refine ⟨12392433968306873574342349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16523245291075831432456465 12392433968306873574342349)
        ·
          refine ⟨4647162738115077590378381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12392433968306873574342349 4647162738115077590378381)
          ·
            refine ⟨1742686026793154096391893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4647162738115077590378381 1742686026793154096391893)
            ·
              refine ⟨40844203752964549134185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1742686026793154096391893 40844203752964549134185)
              ·
                rfl

theorem cell21_1610762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 7].length) (baseStart_1610762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1610762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1610762 prefixEnd_1610762 := by exact prefixLift 1610762
  have htrace : WordTrace (prefixWord ++ tailWord_1610762) baseStart_1610762 baseEnd_1610762 := by
    simpa [prefixWord, tailWord_1610762, baseEnd_1610762] using wordTrace_append hprefix tailTrace_1610762
  have hstable : (prefixWord ++ tailWord_1610762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610762).length < 2 ^ (prefixWord ++ tailWord_1610762).sum := by decide
  have hdescent : baseEnd_1610762 < baseStart_1610762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611018 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_1611018 : Nat := 118140960795 + 1611018 * 2 ^ 59
def prefixEnd_1611018 : Nat := 4983230072969 + 3 ^ 40 * 1611018 * 2
def baseEnd_1611018 : Nat := 367656256464481385940475

theorem tailTrace_1611018 : CollatzResearch.WordTrace tailWord_1611018 prefixEnd_1611018 367656256464481385940475 := by
  unfold tailWord_1611018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14689663419391100203624427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39172435785042933876331805 14689663419391100203624427)
  ·
    refine ⟨22034495129086650305436641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14689663419391100203624427 22034495129086650305436641)
    ·
      refine ⟨16525871346814987729077481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22034495129086650305436641 16525871346814987729077481)
      ·
        refine ⟨12394403510111240796808111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16525871346814987729077481 12394403510111240796808111)
        ·
          refine ⟨18591605265166861195212167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12394403510111240796808111 18591605265166861195212167)
          ·
            refine ⟨27887407897750291792818251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18591605265166861195212167 27887407897750291792818251)
            ·
              refine ⟨41831111846625437689227377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27887407897750291792818251 41831111846625437689227377)
              ·
                refine ⟨31373333884969078266920533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41831111846625437689227377 31373333884969078266920533)
                ·
                  refine ⟨367656256464481385940475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31373333884969078266920533 367656256464481385940475)
                  ·
                    rfl

theorem cell21_1611018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_1611018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611018 prefixEnd_1611018 := by exact prefixLift 1611018
  have htrace : WordTrace (prefixWord ++ tailWord_1611018) baseStart_1611018 baseEnd_1611018 := by
    simpa [prefixWord, tailWord_1611018, baseEnd_1611018] using wordTrace_append hprefix tailTrace_1611018
  have hstable : (prefixWord ++ tailWord_1611018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611018).length < 2 ^ (prefixWord ++ tailWord_1611018).sum := by decide
  have hdescent : baseEnd_1611018 < baseStart_1611018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611097 : List Nat := [1, 2, 1, 2, 2, 2, 5, 3, 3]
def baseStart_1611097 : Nat := 118140960795 + 1611097 * 2 ^ 59
def prefixEnd_1611097 : Nat := 4983230072969 + 3 ^ 40 * 1611097 * 2
def baseEnd_1611097 : Nat := 367674285340794804123647

theorem tailTrace_1611097 : CollatzResearch.WordTrace tailWord_1611097 prefixEnd_1611097 367674285340794804123647 := by
  unfold tailWord_1611097
  simp only [CollatzResearch.WordTrace]
  refine ⟨58761535044278197306623545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39174356696185464871082363 58761535044278197306623545)
  ·
    refine ⟨44071151283208647979967659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58761535044278197306623545 44071151283208647979967659)
    ·
      refine ⟨66106726924812971969951489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44071151283208647979967659 66106726924812971969951489)
      ·
        refine ⟨49580045193609728977463617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66106726924812971969951489 49580045193609728977463617)
        ·
          refine ⟨37185033895207296733097713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49580045193609728977463617 37185033895207296733097713)
          ·
            refine ⟨27888775421405472549823285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37185033895207296733097713 27888775421405472549823285)
            ·
              refine ⟨2614572695756763051545933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27888775421405472549823285 2614572695756763051545933)
              ·
                refine ⟨980464760908786144329725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2614572695756763051545933 980464760908786144329725)
                ·
                  refine ⟨367674285340794804123647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980464760908786144329725 367674285340794804123647)
                  ·
                    rfl

theorem cell21_1611097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 3].length) (baseStart_1611097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611097 prefixEnd_1611097 := by exact prefixLift 1611097
  have htrace : WordTrace (prefixWord ++ tailWord_1611097) baseStart_1611097 baseEnd_1611097 := by
    simpa [prefixWord, tailWord_1611097, baseEnd_1611097] using wordTrace_append hprefix tailTrace_1611097
  have hstable : (prefixWord ++ tailWord_1611097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611097).length < 2 ^ (prefixWord ++ tailWord_1611097).sum := by decide
  have hdescent : baseEnd_1611097 < baseStart_1611097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611114 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_1611114 : Nat := 118140960795 + 1611114 * 2 ^ 59
def prefixEnd_1611114 : Nat := 4983230072969 + 3 ^ 40 * 1611114 * 2
def baseEnd_1611114 : Nat := 367678164972406552340279

theorem tailTrace_1611114 : CollatzResearch.WordTrace tailWord_1611114 prefixEnd_1611114 367678164972406552340279 := by
  unfold tailWord_1611114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14690538771304152302498099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39174770056811072806661597 14690538771304152302498099)
  ·
    refine ⟨22035808156956228453747149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14690538771304152302498099 22035808156956228453747149)
    ·
      refine ⟨8263428058858585670155181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22035808156956228453747149 8263428058858585670155181)
      ·
        refine ⟨3098785522071969626308193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8263428058858585670155181 3098785522071969626308193)
        ·
          refine ⟨2324089141553977219731145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3098785522071969626308193 2324089141553977219731145)
          ·
            refine ⟨1743066856165482914798359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2324089141553977219731145 1743066856165482914798359)
            ·
              refine ⟨2614600284248224372197539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743066856165482914798359 2614600284248224372197539)
              ·
                refine ⟨3921900426372336558296309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614600284248224372197539 3921900426372336558296309)
                ·
                  refine ⟨367678164972406552340279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3921900426372336558296309 367678164972406552340279)
                  ·
                    rfl

theorem cell21_1611114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_1611114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611114 prefixEnd_1611114 := by exact prefixLift 1611114
  have htrace : WordTrace (prefixWord ++ tailWord_1611114) baseStart_1611114 baseEnd_1611114 := by
    simpa [prefixWord, tailWord_1611114, baseEnd_1611114] using wordTrace_append hprefix tailTrace_1611114
  have hstable : (prefixWord ++ tailWord_1611114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611114).length < 2 ^ (prefixWord ++ tailWord_1611114).sum := by decide
  have hdescent : baseEnd_1611114 < baseStart_1611114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611176 : List Nat := [2, 1, 6, 1, 3, 1, 1, 6]
def baseStart_1611176 : Nat := 118140960795 + 1611176 * 2 ^ 59
def prefixEnd_1611176 : Nat := 4983230072969 + 3 ^ 40 * 1611176 * 2
def baseEnd_1611176 : Nat := 122564104739036074102273

theorem tailTrace_1611176 : CollatzResearch.WordTrace tailWord_1611176 prefixEnd_1611176 122564104739036074102273 := by
  unfold tailWord_1611176
  simp only [CollatzResearch.WordTrace]
  refine ⟨29382208205495996899374691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39176277607327995865832921 29382208205495996899374691)
  ·
    refine ⟨44073312308243995349062037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29382208205495996899374691 44073312308243995349062037)
    ·
      refine ⟨2065936514448937281987283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44073312308243995349062037 2065936514448937281987283)
      ·
        refine ⟨3098904771673405922980925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2065936514448937281987283 3098904771673405922980925)
        ·
          refine ⟨1162089289377527221117847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3098904771673405922980925 1162089289377527221117847)
          ·
            refine ⟨1743133934066290831676771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162089289377527221117847 1743133934066290831676771)
            ·
              refine ⟨2614700901099436247515157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743133934066290831676771 2614700901099436247515157)
              ·
                refine ⟨122564104739036074102273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2614700901099436247515157 122564104739036074102273)
                ·
                  rfl

theorem cell21_1611176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 6].length) (baseStart_1611176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611176 prefixEnd_1611176 := by exact prefixLift 1611176
  have htrace : WordTrace (prefixWord ++ tailWord_1611176) baseStart_1611176 baseEnd_1611176 := by
    simpa [prefixWord, tailWord_1611176, baseEnd_1611176] using wordTrace_append hprefix tailTrace_1611176
  have hstable : (prefixWord ++ tailWord_1611176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611176).length < 2 ^ (prefixWord ++ tailWord_1611176).sum := by decide
  have hdescent : baseEnd_1611176 < baseStart_1611176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611184 : List Nat := [2, 1, 1, 1, 2, 1, 1, 12]
def baseStart_1611184 : Nat := 118140960795 + 1611184 * 2 ^ 59
def prefixEnd_1611184 : Nat := 4983230072969 + 3 ^ 40 * 1611184 * 2
def baseEnd_1611184 : Nat := 122564713308700662057823

theorem tailTrace_1611184 : CollatzResearch.WordTrace tailWord_1611184 prefixEnd_1611184 122564713308700662057823 := by
  unfold tailWord_1611184
  simp only [CollatzResearch.WordTrace]
  refine ⟨29382354097481505582520303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39176472129975340776693737 29382354097481505582520303)
  ·
    refine ⟨44073531146222258373780455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29382354097481505582520303 44073531146222258373780455)
    ·
      refine ⟨66110296719333387560670683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44073531146222258373780455 66110296719333387560670683)
      ·
        refine ⟨99165445079000081341006025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66110296719333387560670683 99165445079000081341006025)
        ·
          refine ⟨74374083809250061005754519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99165445079000081341006025 74374083809250061005754519)
          ·
            refine ⟨111561125713875091508631779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74374083809250061005754519 111561125713875091508631779)
            ·
              refine ⟨167341688570812637262947669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111561125713875091508631779 167341688570812637262947669)
              ·
                refine ⟨122564713308700662057823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 167341688570812637262947669 122564713308700662057823)
                ·
                  rfl

theorem cell21_1611184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_1611184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611184 prefixEnd_1611184 := by exact prefixLift 1611184
  have htrace : WordTrace (prefixWord ++ tailWord_1611184) baseStart_1611184 baseEnd_1611184 := by
    simpa [prefixWord, tailWord_1611184, baseEnd_1611184] using wordTrace_append hprefix tailTrace_1611184
  have hstable : (prefixWord ++ tailWord_1611184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611184).length < 2 ^ (prefixWord ++ tailWord_1611184).sum := by decide
  have hdescent : baseEnd_1611184 < baseStart_1611184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611367 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 7]
def baseStart_1611367 : Nat := 118140960795 + 1611367 * 2 ^ 59
def prefixEnd_1611367 : Nat := 4983230072969 + 3 ^ 40 * 1611367 * 2
def baseEnd_1611367 : Nat := 367735903019334334623095

theorem tailTrace_1611367 : CollatzResearch.WordTrace tailWord_1611367 prefixEnd_1611367 367735903019334334623095 := by
  unfold tailWord_1611367
  simp only [CollatzResearch.WordTrace]
  refine ⟨58771382753300033418952355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39180921835533355612634903 58771382753300033418952355)
  ·
    refine ⟨88157074129950050128428533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58771382753300033418952355 88157074129950050128428533)
    ·
      refine ⟨8264725699682817199540175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88157074129950050128428533 8264725699682817199540175)
      ·
        refine ⟨12397088549524225799310263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8264725699682817199540175 12397088549524225799310263)
        ·
          refine ⟨18595632824286338698965395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12397088549524225799310263 18595632824286338698965395)
          ·
            refine ⟨27893449236429508048448093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18595632824286338698965395 27893449236429508048448093)
            ·
              refine ⟨10460043463661065518168035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27893449236429508048448093 10460043463661065518168035)
              ·
                refine ⟨15690065195491598277252053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10460043463661065518168035 15690065195491598277252053)
                ·
                  refine ⟨367735903019334334623095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15690065195491598277252053 367735903019334334623095)
                  ·
                    rfl

theorem cell21_1611367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_1611367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611367 prefixEnd_1611367 := by exact prefixLift 1611367
  have htrace : WordTrace (prefixWord ++ tailWord_1611367) baseStart_1611367 baseEnd_1611367 := by
    simpa [prefixWord, tailWord_1611367, baseEnd_1611367] using wordTrace_append hprefix tailTrace_1611367
  have hstable : (prefixWord ++ tailWord_1611367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611367).length < 2 ^ (prefixWord ++ tailWord_1611367).sum := by decide
  have hdescent : baseEnd_1611367 < baseStart_1611367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611370 : List Nat := [3, 1, 3, 2, 1, 3, 3, 5]
def baseStart_1611370 : Nat := 118140960795 + 1611370 * 2 ^ 59
def prefixEnd_1611370 : Nat := 4983230072969 + 3 ^ 40 * 1611370 * 2
def baseEnd_1611370 : Nat := 122578862553402332024363

theorem tailTrace_1611370 : CollatzResearch.WordTrace tailWord_1611370 prefixEnd_1611370 122578862553402332024363 := by
  unfold tailWord_1611370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14692873043072291232827891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39180994781526109954207709 14692873043072291232827891)
  ·
    refine ⟨22039309564608436849241837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14692873043072291232827891 22039309564608436849241837)
    ·
      refine ⟨8264741086728163818465689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22039309564608436849241837 8264741086728163818465689)
      ·
        refine ⟨6198555815046122863849267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8264741086728163818465689 6198555815046122863849267)
        ·
          refine ⟨9297833722569184295773901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198555815046122863849267 9297833722569184295773901)
          ·
            refine ⟨3486687645963444110915213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9297833722569184295773901 3486687645963444110915213)
            ·
              refine ⟨1307507867236291541593205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3486687645963444110915213 1307507867236291541593205)
              ·
                refine ⟨122578862553402332024363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1307507867236291541593205 122578862553402332024363)
                ·
                  rfl

theorem cell21_1611370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_1611370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611370 prefixEnd_1611370 := by exact prefixLift 1611370
  have htrace : WordTrace (prefixWord ++ tailWord_1611370) baseStart_1611370 baseEnd_1611370 := by
    simpa [prefixWord, tailWord_1611370, baseEnd_1611370] using wordTrace_append hprefix tailTrace_1611370
  have hstable : (prefixWord ++ tailWord_1611370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611370).length < 2 ^ (prefixWord ++ tailWord_1611370).sum := by decide
  have hdescent : baseEnd_1611370 < baseStart_1611370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611429 : List Nat := [1, 3, 1, 2, 1, 2, 6, 5]
def baseStart_1611429 : Nat := 118140960795 + 1611429 * 2 ^ 59
def prefixEnd_1611429 : Nat := 4983230072969 + 3 ^ 40 * 1611429 * 2
def baseEnd_1611429 : Nat := 122583350754678668196545

theorem tailTrace_1611429 : CollatzResearch.WordTrace tailWord_1611429 prefixEnd_1611429 122583350754678668196545 := by
  unfold tailWord_1611429
  simp only [CollatzResearch.WordTrace]
  refine ⟨58773644079075418007709341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39182429386050278671806227 58773644079075418007709341)
  ·
    refine ⟨22040116529653281752891003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58773644079075418007709341 22040116529653281752891003)
    ·
      refine ⟨33060174794479922629336505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22040116529653281752891003 33060174794479922629336505)
      ·
        refine ⟨24795131095859941972002379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33060174794479922629336505 24795131095859941972002379)
        ·
          refine ⟨37192696643789912958003569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24795131095859941972002379 37192696643789912958003569)
          ·
            refine ⟨27894522482842434718502677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37192696643789912958003569 27894522482842434718502677)
            ·
              refine ⟨1307555741383239127429813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27894522482842434718502677 1307555741383239127429813)
              ·
                refine ⟨122583350754678668196545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1307555741383239127429813 122583350754678668196545)
                ·
                  rfl

theorem cell21_1611429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 5].length) (baseStart_1611429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611429 prefixEnd_1611429 := by exact prefixLift 1611429
  have htrace : WordTrace (prefixWord ++ tailWord_1611429) baseStart_1611429 baseEnd_1611429 := by
    simpa [prefixWord, tailWord_1611429, baseEnd_1611429] using wordTrace_append hprefix tailTrace_1611429
  have hstable : (prefixWord ++ tailWord_1611429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611429).length < 2 ^ (prefixWord ++ tailWord_1611429).sum := by decide
  have hdescent : baseEnd_1611429 < baseStart_1611429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611446 : List Nat := [5, 1, 3, 1, 1, 1, 9]
def baseStart_1611446 : Nat := 118140960795 + 1611446 * 2 ^ 59
def prefixEnd_1611446 : Nat := 4983230072969 + 3 ^ 40 * 1611446 * 2
def baseEnd_1611446 : Nat := 40861547988405305867363

theorem tailTrace_1611446 : CollatzResearch.WordTrace tailWord_1611446 prefixEnd_1611446 40861547988405305867363 := by
  unfold tailWord_1611446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673391507500864369442387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39182842746675886607385461 3673391507500864369442387)
  ·
    refine ⟨5510087261251296554163581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3673391507500864369442387 5510087261251296554163581)
    ·
      refine ⟨2066282722969236207811343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5510087261251296554163581 2066282722969236207811343)
      ·
        refine ⟨3099424084453854311717015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066282722969236207811343 3099424084453854311717015)
        ·
          refine ⟨4649136126680781467575523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099424084453854311717015 4649136126680781467575523)
          ·
            refine ⟨6973704190021172201363285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4649136126680781467575523 6973704190021172201363285)
            ·
              refine ⟨40861547988405305867363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6973704190021172201363285 40861547988405305867363)
              ·
                rfl

theorem cell21_1611446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 9].length) (baseStart_1611446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611446 prefixEnd_1611446 := by exact prefixLift 1611446
  have htrace : WordTrace (prefixWord ++ tailWord_1611446) baseStart_1611446 baseEnd_1611446 := by
    simpa [prefixWord, tailWord_1611446, baseEnd_1611446] using wordTrace_append hprefix tailTrace_1611446
  have hstable : (prefixWord ++ tailWord_1611446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611446).length < 2 ^ (prefixWord ++ tailWord_1611446).sum := by decide
  have hdescent : baseEnd_1611446 < baseStart_1611446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611488 : List Nat := [2, 1, 1, 3, 1, 2, 4, 7]
def baseStart_1611488 : Nat := 118140960795 + 1611488 * 2 ^ 59
def prefixEnd_1611488 : Nat := 4983230072969 + 3 ^ 40 * 1611488 * 2
def baseEnd_1611488 : Nat := 122587838955955004368727

theorem tailTrace_1611488 : CollatzResearch.WordTrace tailWord_1611488 prefixEnd_1611488 122587838955955004368727 := by
  unfold tailWord_1611488
  simp only [CollatzResearch.WordTrace]
  refine ⟨29387897992930835542053559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39183863990574447389404745 29387897992930835542053559)
  ·
    refine ⟨44081846989396253313080339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29387897992930835542053559 44081846989396253313080339)
    ·
      refine ⟨66122770484094379969620509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44081846989396253313080339 66122770484094379969620509)
      ·
        refine ⟨24796038931535392488607691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66122770484094379969620509 24796038931535392488607691)
        ·
          refine ⟨37194058397303088732911537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24796038931535392488607691 37194058397303088732911537)
          ·
            refine ⟨27895543797977316549683653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37194058397303088732911537 27895543797977316549683653)
            ·
              refine ⟨5230414462120746853065685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27895543797977316549683653 5230414462120746853065685)
              ·
                refine ⟨122587838955955004368727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5230414462120746853065685 122587838955955004368727)
                ·
                  rfl

theorem cell21_1611488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_1611488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611488 prefixEnd_1611488 := by exact prefixLift 1611488
  have htrace : WordTrace (prefixWord ++ tailWord_1611488) baseStart_1611488 baseEnd_1611488 := by
    simpa [prefixWord, tailWord_1611488, baseEnd_1611488] using wordTrace_append hprefix tailTrace_1611488
  have hstable : (prefixWord ++ tailWord_1611488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611488).length < 2 ^ (prefixWord ++ tailWord_1611488).sum := by decide
  have hdescent : baseEnd_1611488 < baseStart_1611488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611553 : List Nat := [1, 2, 3, 2, 1, 4, 2, 3, 3]
def baseStart_1611553 : Nat := 118140960795 + 1611553 * 2 ^ 59
def prefixEnd_1611553 : Nat := 4983230072969 + 3 ^ 40 * 1611553 * 2
def baseEnd_1611553 : Nat := 367778350753439344522715

theorem tailTrace_1611553 : CollatzResearch.WordTrace tailWord_1611553 prefixEnd_1611553 367778350753439344522715 := by
  unfold tailWord_1611553
  simp only [CollatzResearch.WordTrace]
  refine ⟨58778166730626187185223313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39185444487084124790148875 58778166730626187185223313)
  ·
    refine ⟨44083625047969640388917485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58778166730626187185223313 44083625047969640388917485)
    ·
      refine ⟨16531359392988615145844057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44083625047969640388917485 16531359392988615145844057)
      ·
        refine ⟨12398519544741461359383043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16531359392988615145844057 12398519544741461359383043)
        ·
          refine ⟨18597779317112192039074565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12398519544741461359383043 18597779317112192039074565)
          ·
            refine ⟨3487083621958536007326481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18597779317112192039074565 3487083621958536007326481)
            ·
              refine ⟨2615312716468902005494861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3487083621958536007326481 2615312716468902005494861)
              ·
                refine ⟨980742268675838252060573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2615312716468902005494861 980742268675838252060573)
                ·
                  refine ⟨367778350753439344522715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980742268675838252060573 367778350753439344522715)
                  ·
                    rfl

theorem cell21_1611553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 3].length) (baseStart_1611553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611553 prefixEnd_1611553 := by exact prefixLift 1611553
  have htrace : WordTrace (prefixWord ++ tailWord_1611553) baseStart_1611553 baseEnd_1611553 := by
    simpa [prefixWord, tailWord_1611553, baseEnd_1611553] using wordTrace_append hprefix tailTrace_1611553
  have hstable : (prefixWord ++ tailWord_1611553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611553).length < 2 ^ (prefixWord ++ tailWord_1611553).sum := by decide
  have hdescent : baseEnd_1611553 < baseStart_1611553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611564 : List Nat := [2, 2, 1, 1, 1, 6, 8]
def baseStart_1611564 : Nat := 118140960795 + 1611564 * 2 ^ 59
def prefixEnd_1611564 : Nat := 4983230072969 + 3 ^ 40 * 1611564 * 2
def baseEnd_1611564 : Nat := 40864540122589529982151

theorem tailTrace_1611564 : CollatzResearch.WordTrace tailWord_1611564 prefixEnd_1611564 40864540122589529982151 := by
  unfold tailWord_1611564
  simp only [CollatzResearch.WordTrace]
  refine ⟨29389283966793168031936873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39185711955724224042582497 29389283966793168031936873)
  ·
    refine ⟨22041962975094876023952655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29389283966793168031936873 22041962975094876023952655)
    ·
      refine ⟨33062944462642314035928983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22041962975094876023952655 33062944462642314035928983)
      ·
        refine ⟨49594416693963471053893475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33062944462642314035928983 49594416693963471053893475)
        ·
          refine ⟨74391625040945206580840213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49594416693963471053893475 74391625040945206580840213)
          ·
            refine ⟨3487107423794306558476885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74391625040945206580840213 3487107423794306558476885)
            ·
              refine ⟨40864540122589529982151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3487107423794306558476885 40864540122589529982151)
              ·
                rfl

theorem cell21_1611564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 8].length) (baseStart_1611564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611564 prefixEnd_1611564 := by exact prefixLift 1611564
  have htrace : WordTrace (prefixWord ++ tailWord_1611564) baseStart_1611564 baseEnd_1611564 := by
    simpa [prefixWord, tailWord_1611564, baseEnd_1611564] using wordTrace_append hprefix tailTrace_1611564
  have hstable : (prefixWord ++ tailWord_1611564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611564).length < 2 ^ (prefixWord ++ tailWord_1611564).sum := by decide
  have hdescent : baseEnd_1611564 < baseStart_1611564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611609 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 8]
def baseStart_1611609 : Nat := 118140960795 + 1611609 * 2 ^ 59
def prefixEnd_1611609 : Nat := 4983230072969 + 3 ^ 40 * 1611609 * 2
def baseEnd_1611609 : Nat := 367791130716395691589267

theorem tailTrace_1611609 : CollatzResearch.WordTrace tailWord_1611609 prefixEnd_1611609 367791130716395691589267 := by
  unfold tailWord_1611609
  simp only [CollatzResearch.WordTrace]
  refine ⟨58780209218423308749261881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39186806145615539166174587 58780209218423308749261881)
  ·
    refine ⟨44085156913817481561946411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58780209218423308749261881 44085156913817481561946411)
    ·
      refine ⟨66127735370726222342919617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44085156913817481561946411 66127735370726222342919617)
      ·
        refine ⟨49595801528044666757189713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66127735370726222342919617 49595801528044666757189713)
        ·
          refine ⟨37196851146033500067892285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49595801528044666757189713 37196851146033500067892285)
          ·
            refine ⟨13948819179762562525459607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37196851146033500067892285 13948819179762562525459607)
            ·
              refine ⟨20923228769643843788189411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13948819179762562525459607 20923228769643843788189411)
              ·
                refine ⟨31384843154465765682284117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20923228769643843788189411 31384843154465765682284117)
                ·
                  refine ⟨367791130716395691589267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31384843154465765682284117 367791130716395691589267)
                  ·
                    rfl

theorem cell21_1611609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_1611609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611609 prefixEnd_1611609 := by exact prefixLift 1611609
  have htrace : WordTrace (prefixWord ++ tailWord_1611609) baseStart_1611609 baseEnd_1611609 := by
    simpa [prefixWord, tailWord_1611609, baseEnd_1611609] using wordTrace_append hprefix tailTrace_1611609
  have hstable : (prefixWord ++ tailWord_1611609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611609).length < 2 ^ (prefixWord ++ tailWord_1611609).sum := by decide
  have hdescent : baseEnd_1611609 < baseStart_1611609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611685 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 6]
def baseStart_1611685 : Nat := 118140960795 + 1611685 * 2 ^ 59
def prefixEnd_1611685 : Nat := 4983230072969 + 3 ^ 40 * 1611685 * 2
def baseEnd_1611685 : Nat := 367808474951836448322445

theorem tailTrace_1611685 : CollatzResearch.WordTrace tailWord_1611685 prefixEnd_1611685 367808474951836448322445 := by
  unfold tailWord_1611685
  simp only [CollatzResearch.WordTrace]
  refine ⟨58782981166147973729028509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39188654110765315819352339 58782981166147973729028509)
  ·
    refine ⟨22043617937305490148385691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58782981166147973729028509 22043617937305490148385691)
    ·
      refine ⟨33065426905958235222578537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22043617937305490148385691 33065426905958235222578537)
      ·
        refine ⟨24799070179468676416933903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33065426905958235222578537 24799070179468676416933903)
        ·
          refine ⟨37198605269203014625400855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24799070179468676416933903 37198605269203014625400855)
          ·
            refine ⟨55797907903804521938101283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37198605269203014625400855 55797907903804521938101283)
            ·
              refine ⟨83696861855706782907151925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55797907903804521938101283 83696861855706782907151925)
              ·
                refine ⟨7846580798972510897545493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83696861855706782907151925 7846580798972510897545493)
                ·
                  refine ⟨367808474951836448322445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7846580798972510897545493 367808474951836448322445)
                  ·
                    rfl

theorem cell21_1611685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_1611685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611685 prefixEnd_1611685 := by exact prefixLift 1611685
  have htrace : WordTrace (prefixWord ++ tailWord_1611685) baseStart_1611685 baseEnd_1611685 := by
    simpa [prefixWord, tailWord_1611685, baseEnd_1611685] using wordTrace_append hprefix tailTrace_1611685
  have hstable : (prefixWord ++ tailWord_1611685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611685).length < 2 ^ (prefixWord ++ tailWord_1611685).sum := by decide
  have hdescent : baseEnd_1611685 < baseStart_1611685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611747 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 5]
def baseStart_1611747 : Nat := 118140960795 + 1611747 * 2 ^ 59
def prefixEnd_1611747 : Nat := 4983230072969 + 3 ^ 40 * 1611747 * 2
def baseEnd_1611747 : Nat := 367822624196538118288985

theorem tailTrace_1611747 : CollatzResearch.WordTrace tailWord_1611747 prefixEnd_1611747 367822624196538118288985 := by
  unfold tailWord_1611747
  simp only [CollatzResearch.WordTrace]
  refine ⟨58785242491923358317785495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39190161661282238878523663 58785242491923358317785495)
  ·
    refine ⟨88177863737885037476678243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58785242491923358317785495 88177863737885037476678243)
    ·
      refine ⟨132266795606827556215017365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88177863737885037476678243 132266795606827556215017365)
      ·
        refine ⟨6200006044070041697578939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132266795606827556215017365 6200006044070041697578939)
        ·
          refine ⟨9300009066105062546368409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6200006044070041697578939 9300009066105062546368409)
          ·
            refine ⟨6975006799578796909776307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9300009066105062546368409 6975006799578796909776307)
            ·
              refine ⟨10462510199368195364664461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975006799578796909776307 10462510199368195364664461)
              ·
                refine ⟨3923441324763073261749173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10462510199368195364664461 3923441324763073261749173)
                ·
                  refine ⟨367822624196538118288985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3923441324763073261749173 367822624196538118288985)
                  ·
                    rfl

theorem cell21_1611747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_1611747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611747 prefixEnd_1611747 := by exact prefixLift 1611747
  have htrace : WordTrace (prefixWord ++ tailWord_1611747) baseStart_1611747 baseEnd_1611747 := by
    simpa [prefixWord, tailWord_1611747, baseEnd_1611747] using wordTrace_append hprefix tailTrace_1611747
  have hstable : (prefixWord ++ tailWord_1611747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611747).length < 2 ^ (prefixWord ++ tailWord_1611747).sum := by decide
  have hdescent : baseEnd_1611747 < baseStart_1611747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611781 : List Nat := [1, 3, 1, 1, 2, 6, 1, 3, 3]
def baseStart_1611781 : Nat := 118140960795 + 1611781 * 2 ^ 59
def prefixEnd_1611781 : Nat := 4983230072969 + 3 ^ 40 * 1611781 * 2
def baseEnd_1611781 : Nat := 367830383459761614722249

theorem tailTrace_1611781 : CollatzResearch.WordTrace tailWord_1611781 prefixEnd_1611781 367830383459761614722249 := by
  unfold tailWord_1611781
  simp only [CollatzResearch.WordTrace]
  refine ⟨58786482573800182124523197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39190988382533454749682131 58786482573800182124523197)
  ·
    refine ⟨22044930965175068296696199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58786482573800182124523197 22044930965175068296696199)
    ·
      refine ⟨33067396447762602445044299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22044930965175068296696199 33067396447762602445044299)
      ·
        refine ⟨49601094671643903667566449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33067396447762602445044299 49601094671643903667566449)
        ·
          refine ⟨37200821003732927750674837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49601094671643903667566449 37200821003732927750674837)
          ·
            refine ⟨1743788484549980988312883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37200821003732927750674837 1743788484549980988312883)
            ·
              refine ⟨2615682726824971482469325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743788484549980988312883 2615682726824971482469325)
              ·
                refine ⟨980881022559364305925997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2615682726824971482469325 980881022559364305925997)
                ·
                  refine ⟨367830383459761614722249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980881022559364305925997 367830383459761614722249)
                  ·
                    rfl

theorem cell21_1611781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_1611781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611781 prefixEnd_1611781 := by exact prefixLift 1611781
  have htrace : WordTrace (prefixWord ++ tailWord_1611781) baseStart_1611781 baseEnd_1611781 := by
    simpa [prefixWord, tailWord_1611781, baseEnd_1611781] using wordTrace_append hprefix tailTrace_1611781
  have hstable : (prefixWord ++ tailWord_1611781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611781).length < 2 ^ (prefixWord ++ tailWord_1611781).sum := by decide
  have hdescent : baseEnd_1611781 < baseStart_1611781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611809 : List Nat := [1, 2, 3, 2, 4, 1, 2, 6]
def baseStart_1611809 : Nat := 118140960795 + 1611809 * 2 ^ 59
def prefixEnd_1611809 : Nat := 4983230072969 + 3 ^ 40 * 1611809 * 2
def baseEnd_1611809 : Nat := 122612257813746596085175

theorem tailTrace_1611809 : CollatzResearch.WordTrace tailWord_1611809 prefixEnd_1611809 122612257813746596085175 := by
  unfold tailWord_1611809
  simp only [CollatzResearch.WordTrace]
  refine ⟨58787503817698742906542481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39191669211799161937694987 58787503817698742906542481)
  ·
    refine ⟨44090627863274057179906861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58787503817698742906542481 44090627863274057179906861)
    ·
      refine ⟨16533985448727771442465073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44090627863274057179906861 16533985448727771442465073)
      ·
        refine ⟨12400489086545828581848805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16533985448727771442465073 12400489086545828581848805)
        ·
          refine ⟨2325091703727342859096651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12400489086545828581848805 2325091703727342859096651)
          ·
            refine ⟨3487637555591014288644977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325091703727342859096651 3487637555591014288644977)
            ·
              refine ⟨2615728166693260716483733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3487637555591014288644977 2615728166693260716483733)
              ·
                refine ⟨122612257813746596085175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2615728166693260716483733 122612257813746596085175)
                ·
                  rfl

theorem cell21_1611809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 6].length) (baseStart_1611809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611809 prefixEnd_1611809 := by exact prefixLift 1611809
  have htrace : WordTrace (prefixWord ++ tailWord_1611809) baseStart_1611809 baseEnd_1611809 := by
    simpa [prefixWord, tailWord_1611809, baseEnd_1611809] using wordTrace_append hprefix tailTrace_1611809
  have hstable : (prefixWord ++ tailWord_1611809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611809).length < 2 ^ (prefixWord ++ tailWord_1611809).sum := by decide
  have hdescent : baseEnd_1611809 < baseStart_1611809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611854 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_1611854 : Nat := 118140960795 + 1611854 * 2 ^ 59
def prefixEnd_1611854 : Nat := 4983230072969 + 3 ^ 40 * 1611854 * 2
def baseEnd_1611854 : Nat := 367847043054329710005433

theorem tailTrace_1611854 : CollatzResearch.WordTrace tailWord_1611854 prefixEnd_1611854 367847043054329710005433 := by
  unfold tailWord_1611854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7348643137816964448991327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39192763401690477061287077 7348643137816964448991327)
  ·
    refine ⟨11022964706725446673486991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7348643137816964448991327 11022964706725446673486991)
    ·
      refine ⟨16534447060088170010230487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11022964706725446673486991 16534447060088170010230487)
      ·
        refine ⟨24801670590132255015345731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16534447060088170010230487 24801670590132255015345731)
        ·
          refine ⟨37202505885198382523018597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24801670590132255015345731 37202505885198382523018597)
          ·
            refine ⟨6975469853474696723065987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37202505885198382523018597 6975469853474696723065987)
            ·
              refine ⟨10463204780212045084598981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975469853474696723065987 10463204780212045084598981)
              ·
                refine ⟨1961850896289758453362309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10463204780212045084598981 1961850896289758453362309)
                ·
                  refine ⟨367847043054329710005433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1961850896289758453362309 367847043054329710005433)
                  ·
                    rfl

theorem cell21_1611854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_1611854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611854 prefixEnd_1611854 := by exact prefixLift 1611854
  have htrace : WordTrace (prefixWord ++ tailWord_1611854) baseStart_1611854 baseEnd_1611854 := by
    simpa [prefixWord, tailWord_1611854, baseEnd_1611854] using wordTrace_append hprefix tailTrace_1611854
  have hstable : (prefixWord ++ tailWord_1611854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611854).length < 2 ^ (prefixWord ++ tailWord_1611854).sum := by decide
  have hdescent : baseEnd_1611854 < baseStart_1611854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611885 : List Nat := [1, 5, 1, 1, 2, 1, 5, 5]
def baseStart_1611885 : Nat := 118140960795 + 1611885 * 2 ^ 59
def prefixEnd_1611885 : Nat := 4983230072969 + 3 ^ 40 * 1611885 * 2
def baseEnd_1611885 : Nat := 122618039225560181662901

theorem tailTrace_1611885 : CollatzResearch.WordTrace tailWord_1611885 prefixEnd_1611885 122618039225560181662901 := by
  unfold tailWord_1611885
  simp only [CollatzResearch.WordTrace]
  refine ⟨58790275765423407886309109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39193517176948938590872739 58790275765423407886309109)
  ·
    refine ⟨5511588353008444489341479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58790275765423407886309109 5511588353008444489341479)
    ·
      refine ⟨8267382529512666734012219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5511588353008444489341479 8267382529512666734012219)
      ·
        refine ⟨12401073794269000101018329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8267382529512666734012219 12401073794269000101018329)
        ·
          refine ⟨9300805345701750075763747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12401073794269000101018329 9300805345701750075763747)
          ·
            refine ⟨13951208018552625113645621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9300805345701750075763747 13951208018552625113645621)
            ·
              refine ⟨1307925751739308604404277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13951208018552625113645621 1307925751739308604404277)
              ·
                refine ⟨122618039225560181662901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1307925751739308604404277 122618039225560181662901)
                ·
                  rfl

theorem cell21_1611885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 5].length) (baseStart_1611885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611885 prefixEnd_1611885 := by exact prefixLift 1611885
  have htrace : WordTrace (prefixWord ++ tailWord_1611885) baseStart_1611885 baseEnd_1611885 := by
    simpa [prefixWord, tailWord_1611885, baseEnd_1611885] using wordTrace_append hprefix tailTrace_1611885
  have hstable : (prefixWord ++ tailWord_1611885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611885).length < 2 ^ (prefixWord ++ tailWord_1611885).sum := by decide
  have hdescent : baseEnd_1611885 < baseStart_1611885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611913 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 6]
def baseStart_1611913 : Nat := 118140960795 + 1611913 * 2 ^ 59
def prefixEnd_1611913 : Nat := 4983230072969 + 3 ^ 40 * 1611913 * 2
def baseEnd_1611913 : Nat := 367860507658158718521979

theorem tailTrace_1611913 : CollatzResearch.WordTrace tailWord_1611913 prefixEnd_1611913 367860507658158718521979 := by
  unfold tailWord_1611913
  simp only [CollatzResearch.WordTrace]
  refine ⟨58791297009321968668328393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39194198006214645778885595 58791297009321968668328393)
  ·
    refine ⟨44093472756991476501246295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58791297009321968668328393 44093472756991476501246295)
    ·
      refine ⟨66140209135487214751869443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44093472756991476501246295 66140209135487214751869443)
      ·
        refine ⟨99210313703230822127804165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66140209135487214751869443 99210313703230822127804165)
        ·
          refine ⟨18601933819355779148963281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99210313703230822127804165 18601933819355779148963281)
          ·
            refine ⟨13951450364516834361722461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18601933819355779148963281 13951450364516834361722461)
            ·
              refine ⟨5231793886693812885645923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13951450364516834361722461 5231793886693812885645923)
              ·
                refine ⟨7847690830040719328468885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5231793886693812885645923 7847690830040719328468885)
                ·
                  refine ⟨367860507658158718521979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7847690830040719328468885 367860507658158718521979)
                  ·
                    rfl

theorem cell21_1611913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_1611913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1611913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1611913 prefixEnd_1611913 := by exact prefixLift 1611913
  have htrace : WordTrace (prefixWord ++ tailWord_1611913) baseStart_1611913 baseEnd_1611913 := by
    simpa [prefixWord, tailWord_1611913, baseEnd_1611913] using wordTrace_append hprefix tailTrace_1611913
  have hstable : (prefixWord ++ tailWord_1611913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611913).length < 2 ^ (prefixWord ++ tailWord_1611913).sum := by decide
  have hdescent : baseEnd_1611913 < baseStart_1611913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612068 : List Nat := [2, 3, 1, 3, 1, 2, 1, 5, 3]
def baseStart_1612068 : Nat := 118140960795 + 1612068 * 2 ^ 59
def prefixEnd_1612068 : Nat := 4983230072969 + 3 ^ 40 * 1612068 * 2
def baseEnd_1612068 : Nat := 367895880769912893438329

theorem tailTrace_1612068 : CollatzResearch.WordTrace tailWord_1612068 prefixEnd_1612068 367895880769912893438329 := by
  unfold tailWord_1612068
  simp only [CollatzResearch.WordTrace]
  refine ⟨29398475161880215070110429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39197966882506953426813905 29398475161880215070110429)
  ·
    refine ⟨11024428185705080651291411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29398475161880215070110429 11024428185705080651291411)
    ·
      refine ⟨16536642278557620976937117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11024428185705080651291411 16536642278557620976937117)
      ·
        refine ⟨6201240854459107866351419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16536642278557620976937117 6201240854459107866351419)
        ·
          refine ⟨9301861281688661799527129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6201240854459107866351419 9301861281688661799527129)
          ·
            refine ⟨6976395961266496349645347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9301861281688661799527129 6976395961266496349645347)
            ·
              refine ⟨10464593941899744524468021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976395961266496349645347 10464593941899744524468021)
              ·
                refine ⟨981055682053101049168877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10464593941899744524468021 981055682053101049168877)
                ·
                  refine ⟨367895880769912893438329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981055682053101049168877 367895880769912893438329)
                  ·
                    rfl

theorem cell21_1612068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_1612068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612068 prefixEnd_1612068 := by exact prefixLift 1612068
  have htrace : WordTrace (prefixWord ++ tailWord_1612068) baseStart_1612068 baseEnd_1612068 := by
    simpa [prefixWord, tailWord_1612068, baseEnd_1612068] using wordTrace_append hprefix tailTrace_1612068
  have hstable : (prefixWord ++ tailWord_1612068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612068).length < 2 ^ (prefixWord ++ tailWord_1612068).sum := by decide
  have hdescent : baseEnd_1612068 < baseStart_1612068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612082 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_1612082 : Nat := 118140960795 + 1612082 * 2 ^ 59
def prefixEnd_1612082 : Nat := 4983230072969 + 3 ^ 40 * 1612082 * 2
def baseEnd_1612082 : Nat := 367899075760651980204967

theorem tailTrace_1612082 : CollatzResearch.WordTrace tailWord_1612082 prefixEnd_1612082 367899075760651980204967 := by
  unfold tailWord_1612082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14699365236427427632807625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39198307297139807020820333 14699365236427427632807625)
  ·
    refine ⟨11024523927320570724605719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14699365236427427632807625 11024523927320570724605719)
    ·
      refine ⟨16536785890980856086908579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11024523927320570724605719 16536785890980856086908579)
      ·
        refine ⟨24805178836471284130362869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16536785890980856086908579 24805178836471284130362869)
        ·
          refine ⟨2325485515919182887221519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24805178836471284130362869 2325485515919182887221519)
          ·
            refine ⟨3488228273878774330832279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325485515919182887221519 3488228273878774330832279)
            ·
              refine ⟨5232342410818161496248419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488228273878774330832279 5232342410818161496248419)
              ·
                refine ⟨7848513616227242244372629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232342410818161496248419 7848513616227242244372629)
                ·
                  refine ⟨367899075760651980204967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7848513616227242244372629 367899075760651980204967)
                  ·
                    rfl

theorem cell21_1612082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_1612082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612082 prefixEnd_1612082 := by exact prefixLift 1612082
  have htrace : WordTrace (prefixWord ++ tailWord_1612082) baseStart_1612082 baseEnd_1612082 := by
    simpa [prefixWord, tailWord_1612082, baseEnd_1612082] using wordTrace_append hprefix tailTrace_1612082
  have hstable : (prefixWord ++ tailWord_1612082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612082).length < 2 ^ (prefixWord ++ tailWord_1612082).sum := by decide
  have hdescent : baseEnd_1612082 < baseStart_1612082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612110 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_1612110 : Nat := 118140960795 + 1612110 * 2 ^ 59
def prefixEnd_1612110 : Nat := 4983230072969 + 3 ^ 40 * 1612110 * 2
def baseEnd_1612110 : Nat := 367905465742130153738243

theorem tailTrace_1612110 : CollatzResearch.WordTrace tailWord_1612110 prefixEnd_1612110 367905465742130153738243 := by
  unfold tailWord_1612110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7349810273701033914156223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39198988126405514208833189 7349810273701033914156223)
  ·
    refine ⟨11024715410551550871234335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7349810273701033914156223 11024715410551550871234335)
    ·
      refine ⟨16537073115827326306851503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11024715410551550871234335 16537073115827326306851503)
      ·
        refine ⟨24805609673740989460277255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16537073115827326306851503 24805609673740989460277255)
        ·
          refine ⟨37208414510611484190415883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24805609673740989460277255 37208414510611484190415883)
          ·
            refine ⟨55812621765917226285623825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37208414510611484190415883 55812621765917226285623825)
            ·
              refine ⟨41859466324437919714217869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55812621765917226285623825 41859466324437919714217869)
              ·
                refine ⟨15697299871664219892831701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41859466324437919714217869 15697299871664219892831701)
                ·
                  refine ⟨367905465742130153738243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15697299871664219892831701 367905465742130153738243)
                  ·
                    rfl

theorem cell21_1612110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_1612110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612110 prefixEnd_1612110 := by exact prefixLift 1612110
  have htrace : WordTrace (prefixWord ++ tailWord_1612110) baseStart_1612110 baseEnd_1612110 := by
    simpa [prefixWord, tailWord_1612110, baseEnd_1612110] using wordTrace_append hprefix tailTrace_1612110
  have hstable : (prefixWord ++ tailWord_1612110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612110).length < 2 ^ (prefixWord ++ tailWord_1612110).sum := by decide
  have hdescent : baseEnd_1612110 < baseStart_1612110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612113 : List Nat := [1, 2, 2, 1, 4, 4, 2, 5]
def baseStart_1612113 : Nat := 118140960795 + 1612113 * 2 ^ 59
def prefixEnd_1612113 : Nat := 4983230072969 + 3 ^ 40 * 1612113 * 2
def baseEnd_1612113 : Nat := 122635383461000938396079

theorem tailTrace_1612113 : CollatzResearch.WordTrace tailWord_1612113 prefixEnd_1612113 122635383461000938396079 := by
  unfold tailWord_1612113
  simp only [CollatzResearch.WordTrace]
  refine ⟨58798591608597402825608993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39199061072398268550405995 58798591608597402825608993)
  ·
    refine ⟨44098943706448052119206745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58798591608597402825608993 44098943706448052119206745)
    ·
      refine ⟨33074207779836039089405059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44098943706448052119206745 33074207779836039089405059)
      ·
        refine ⟨49611311669754058634107589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33074207779836039089405059 49611311669754058634107589)
        ·
          refine ⟨9302120938078885993895173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49611311669754058634107589 9302120938078885993895173)
          ·
            refine ⟨1744147675889791123855345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9302120938078885993895173 1744147675889791123855345)
            ·
              refine ⟨1308110756917343342891509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1744147675889791123855345 1308110756917343342891509)
              ·
                refine ⟨122635383461000938396079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1308110756917343342891509 122635383461000938396079)
                ·
                  rfl

theorem cell21_1612113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 5].length) (baseStart_1612113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612113 prefixEnd_1612113 := by exact prefixLift 1612113
  have htrace : WordTrace (prefixWord ++ tailWord_1612113) baseStart_1612113 baseEnd_1612113 := by
    simpa [prefixWord, tailWord_1612113, baseEnd_1612113] using wordTrace_append hprefix tailTrace_1612113
  have hstable : (prefixWord ++ tailWord_1612113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612113).length < 2 ^ (prefixWord ++ tailWord_1612113).sum := by decide
  have hdescent : baseEnd_1612113 < baseStart_1612113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612141 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1612141 : Nat := 118140960795 + 1612141 * 2 ^ 59
def prefixEnd_1612141 : Nat := 4983230072969 + 3 ^ 40 * 1612141 * 2
def baseEnd_1612141 : Nat := 367912540364480988721513

theorem tailTrace_1612141 : CollatzResearch.WordTrace tailWord_1612141 prefixEnd_1612141 367912540364480988721513 := by
  unfold tailWord_1612141
  simp only [CollatzResearch.WordTrace]
  refine ⟨58799612852495963607628277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39199741901663975738418851 58799612852495963607628277)
  ·
    refine ⟨5512463704921496588215151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58799612852495963607628277 5512463704921496588215151)
    ·
      refine ⟨8268695557382244882322727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5512463704921496588215151 8268695557382244882322727)
      ·
        refine ⟨12403043336073367323484091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8268695557382244882322727 12403043336073367323484091)
        ·
          refine ⟨18604565004110050985226137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12403043336073367323484091 18604565004110050985226137)
          ·
            refine ⟨13953423753082538238919603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18604565004110050985226137 13953423753082538238919603)
            ·
              refine ⟨20930135629623807358379405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13953423753082538238919603 20930135629623807358379405)
              ·
                refine ⟨7848800861108927759392277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20930135629623807358379405 7848800861108927759392277)
                ·
                  refine ⟨367912540364480988721513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7848800861108927759392277 367912540364480988721513)
                  ·
                    rfl

theorem cell21_1612141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1612141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612141 prefixEnd_1612141 := by exact prefixLift 1612141
  have htrace : WordTrace (prefixWord ++ tailWord_1612141) baseStart_1612141 baseEnd_1612141 := by
    simpa [prefixWord, tailWord_1612141, baseEnd_1612141] using wordTrace_append hprefix tailTrace_1612141
  have hstable : (prefixWord ++ tailWord_1612141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612141).length < 2 ^ (prefixWord ++ tailWord_1612141).sum := by decide
  have hdescent : baseEnd_1612141 < baseStart_1612141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612150 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1612150 : Nat := 118140960795 + 1612150 * 2 ^ 59
def prefixEnd_1612150 : Nat := 4983230072969 + 3 ^ 40 * 1612150 * 2
def baseEnd_1612150 : Nat := 367914594287098973071495

theorem tailTrace_1612150 : CollatzResearch.WordTrace tailWord_1612150 prefixEnd_1612150 367914594287098973071495 := by
  unfold tailWord_1612150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674996319341459884044119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39199960739642238763137269 3674996319341459884044119)
  ·
    refine ⟨5512494479012189826066179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3674996319341459884044119 5512494479012189826066179)
    ·
      refine ⟨8268741718518284739099269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5512494479012189826066179 8268741718518284739099269)
      ·
        refine ⟨1550389072222178388581113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8268741718518284739099269 1550389072222178388581113)
        ·
          refine ⟨1162791804166633791435835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1550389072222178388581113 1162791804166633791435835)
          ·
            refine ⟨1744187706249950687153753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162791804166633791435835 1744187706249950687153753)
            ·
              refine ⟨1308140779687463015365315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1744187706249950687153753 1308140779687463015365315)
              ·
                refine ⟨1962211169531194523047973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308140779687463015365315 1962211169531194523047973)
                ·
                  refine ⟨367914594287098973071495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1962211169531194523047973 367914594287098973071495)
                  ·
                    rfl

theorem cell21_1612150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1612150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612150 prefixEnd_1612150 := by exact prefixLift 1612150
  have htrace : WordTrace (prefixWord ++ tailWord_1612150) baseStart_1612150 baseEnd_1612150 := by
    simpa [prefixWord, tailWord_1612150, baseEnd_1612150] using wordTrace_append hprefix tailTrace_1612150
  have hstable : (prefixWord ++ tailWord_1612150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612150).length < 2 ^ (prefixWord ++ tailWord_1612150).sum := by decide
  have hdescent : baseEnd_1612150 < baseStart_1612150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612155 : List Nat := [1, 1, 1, 1, 1, 7, 1, 8]
def baseStart_1612155 : Nat := 118140960795 + 1612155 * 2 ^ 59
def prefixEnd_1612155 : Nat := 4983230072969 + 3 ^ 40 * 1612155 * 2
def baseEnd_1612155 : Nat := 122638578451740025162717

theorem tailTrace_1612155 : CollatzResearch.WordTrace tailWord_1612155 prefixEnd_1612155 122638578451740025162717 := by
  unfold tailWord_1612155
  simp only [CollatzResearch.WordTrace]
  refine ⟨58800123474445243998637919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39200082316296829332425279 58800123474445243998637919)
  ·
    refine ⟨88200185211667865997956879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58800123474445243998637919 88200185211667865997956879)
    ·
      refine ⟨132300277817501798996935319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88200185211667865997956879 132300277817501798996935319)
      ·
        refine ⟨198450416726252698495402979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132300277817501798996935319 198450416726252698495402979)
        ·
          refine ⟨297675625089379047743104469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198450416726252698495402979 297675625089379047743104469)
          ·
            refine ⟨6976772463032321431479011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 297675625089379047743104469 6976772463032321431479011)
            ·
              refine ⟨10465158694548482147218517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976772463032321431479011 10465158694548482147218517)
              ·
                refine ⟨122638578451740025162717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10465158694548482147218517 122638578451740025162717)
                ·
                  rfl

theorem cell21_1612155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 8].length) (baseStart_1612155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612155 prefixEnd_1612155 := by exact prefixLift 1612155
  have htrace : WordTrace (prefixWord ++ tailWord_1612155) baseStart_1612155 baseEnd_1612155 := by
    simpa [prefixWord, tailWord_1612155, baseEnd_1612155] using wordTrace_append hprefix tailTrace_1612155
  have hstable : (prefixWord ++ tailWord_1612155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612155).length < 2 ^ (prefixWord ++ tailWord_1612155).sum := by decide
  have hdescent : baseEnd_1612155 < baseStart_1612155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612338 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1612338 : Nat := 118140960795 + 1612338 * 2 ^ 59
def prefixEnd_1612338 : Nat := 4983230072969 + 3 ^ 40 * 1612338 * 2
def baseEnd_1612338 : Nat := 367957498448452423937777

theorem tailTrace_1612338 : CollatzResearch.WordTrace tailWord_1612338 prefixEnd_1612338 367957498448452423937777 := by
  unfold tailWord_1612338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14701699508195566563137417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39204532021854844168366445 14701699508195566563137417)
  ·
    refine ⟨11026274631146674922353063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14701699508195566563137417 11026274631146674922353063)
    ·
      refine ⟨16539411946720012383529595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11026274631146674922353063 16539411946720012383529595)
      ·
        refine ⟨24809117920080018575294393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16539411946720012383529595 24809117920080018575294393)
        ·
          refine ⟨18606838440060013931470795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24809117920080018575294393 18606838440060013931470795)
          ·
            refine ⟨27910257660090020897206193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18606838440060013931470795 27910257660090020897206193)
            ·
              refine ⟨20932693245067515672904645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27910257660090020897206193 20932693245067515672904645)
              ·
                refine ⟨3924879983450159188669621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20932693245067515672904645 3924879983450159188669621)
                ·
                  refine ⟨367957498448452423937777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3924879983450159188669621 367957498448452423937777)
                  ·
                    rfl

theorem cell21_1612338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1612338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612338 prefixEnd_1612338 := by exact prefixLift 1612338
  have htrace : WordTrace (prefixWord ++ tailWord_1612338) baseStart_1612338 baseEnd_1612338 := by
    simpa [prefixWord, tailWord_1612338, baseEnd_1612338] using wordTrace_append hprefix tailTrace_1612338
  have hstable : (prefixWord ++ tailWord_1612338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612338).length < 2 ^ (prefixWord ++ tailWord_1612338).sum := by decide
  have hdescent : baseEnd_1612338 < baseStart_1612338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612352 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_1612352 : Nat := 118140960795 + 1612352 * 2 ^ 59
def prefixEnd_1612352 : Nat := 4983230072969 + 3 ^ 40 * 1612352 * 2
def baseEnd_1612352 : Nat := 367960693439191510704415

theorem tailTrace_1612352 : CollatzResearch.WordTrace tailWord_1612352 prefixEnd_1612352 367960693439191510704415 := by
  unfold tailWord_1612352
  simp only [CollatzResearch.WordTrace]
  refine ⟨29403654327365773321779655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39204872436487697762372873 29403654327365773321779655)
  ·
    refine ⟨44105481491048659982669483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29403654327365773321779655 44105481491048659982669483)
    ·
      refine ⟨66158222236572989974004225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44105481491048659982669483 66158222236572989974004225)
      ·
        refine ⟨49618666677429742480503169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66158222236572989974004225 49618666677429742480503169)
        ·
          refine ⟨37214000008072306860377377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49618666677429742480503169 37214000008072306860377377)
          ·
            refine ⟨27910500006054230145283033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37214000008072306860377377 27910500006054230145283033)
            ·
              refine ⟨20932875004540672608962275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27910500006054230145283033 20932875004540672608962275)
              ·
                refine ⟨31399312506811008913443413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20932875004540672608962275 31399312506811008913443413)
                ·
                  refine ⟨367960693439191510704415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31399312506811008913443413 367960693439191510704415)
                  ·
                    rfl

theorem cell21_1612352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_1612352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612352 prefixEnd_1612352 := by exact prefixLift 1612352
  have htrace : WordTrace (prefixWord ++ tailWord_1612352) baseStart_1612352 baseEnd_1612352 := by
    simpa [prefixWord, tailWord_1612352, baseEnd_1612352] using wordTrace_append hprefix tailTrace_1612352
  have hstable : (prefixWord ++ tailWord_1612352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612352).length < 2 ^ (prefixWord ++ tailWord_1612352).sum := by decide
  have hdescent : baseEnd_1612352 < baseStart_1612352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612369 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 4]
def baseStart_1612369 : Nat := 118140960795 + 1612369 * 2 ^ 59
def prefixEnd_1612369 : Nat := 4983230072969 + 3 ^ 40 * 1612369 * 2
def baseEnd_1612369 : Nat := 367964573070803258921047

theorem tailTrace_1612369 : CollatzResearch.WordTrace tailWord_1612369 prefixEnd_1612369 367964573070803258921047 := by
  unfold tailWord_1612369
  simp only [CollatzResearch.WordTrace]
  refine ⟨58807928695669958546928161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39205285797113305697952107 58807928695669958546928161)
  ·
    refine ⟨44105946521752468910196121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58807928695669958546928161 44105946521752468910196121)
    ·
      refine ⟨33079459891314351682647091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44105946521752468910196121 33079459891314351682647091)
      ·
        refine ⟨49619189836971527523970637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33079459891314351682647091 49619189836971527523970637)
        ·
          refine ⟨18607196188864322821488989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49619189836971527523970637 18607196188864322821488989)
          ·
            refine ⟨6977698570824121058058371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18607196188864322821488989 6977698570824121058058371)
            ·
              refine ⟨10466547856236181587087557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6977698570824121058058371 10466547856236181587087557)
              ·
                refine ⟨1962477723044284047578917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10466547856236181587087557 1962477723044284047578917)
                ·
                  refine ⟨367964573070803258921047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1962477723044284047578917 367964573070803258921047)
                  ·
                    rfl

theorem cell21_1612369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_1612369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612369 prefixEnd_1612369 := by exact prefixLift 1612369
  have htrace : WordTrace (prefixWord ++ tailWord_1612369) baseStart_1612369 baseEnd_1612369 := by
    simpa [prefixWord, tailWord_1612369, baseEnd_1612369] using wordTrace_append hprefix tailTrace_1612369
  have hstable : (prefixWord ++ tailWord_1612369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612369).length < 2 ^ (prefixWord ++ tailWord_1612369).sum := by decide
  have hdescent : baseEnd_1612369 < baseStart_1612369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612372 : List Nat := [2, 4, 1, 1, 1, 4, 1, 4, 3]
def baseStart_1612372 : Nat := 118140960795 + 1612372 * 2 ^ 59
def prefixEnd_1612372 : Nat := 4983230072969 + 3 ^ 40 * 1612372 * 2
def baseEnd_1612372 : Nat := 367965257711675920371041

theorem tailTrace_1612372 : CollatzResearch.WordTrace tailWord_1612372 prefixEnd_1612372 367965257711675920371041 := by
  unfold tailWord_1612372
  simp only [CollatzResearch.WordTrace]
  refine ⟨29404019057329545029643685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39205358743106060039524913 29404019057329545029643685)
  ·
    refine ⟨5513253573249289693058191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29404019057329545029643685 5513253573249289693058191)
    ·
      refine ⟨8269880359873934539587287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5513253573249289693058191 8269880359873934539587287)
      ·
        refine ⟨12404820539810901809380931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8269880359873934539587287 12404820539810901809380931)
        ·
          refine ⟨18607230809716352714071397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12404820539810901809380931 18607230809716352714071397)
          ·
            refine ⟨3488855776821816133888387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18607230809716352714071397 3488855776821816133888387)
            ·
              refine ⟨5233283665232724200832581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488855776821816133888387 5233283665232724200832581)
              ·
                refine ⟨981240687231135787656109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5233283665232724200832581 981240687231135787656109)
                ·
                  refine ⟨367965257711675920371041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981240687231135787656109 367965257711675920371041)
                  ·
                    rfl

theorem cell21_1612372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_1612372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612372 prefixEnd_1612372 := by exact prefixLift 1612372
  have htrace : WordTrace (prefixWord ++ tailWord_1612372) baseStart_1612372 baseEnd_1612372 := by
    simpa [prefixWord, tailWord_1612372, baseEnd_1612372] using wordTrace_append hprefix tailTrace_1612372
  have hstable : (prefixWord ++ tailWord_1612372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612372).length < 2 ^ (prefixWord ++ tailWord_1612372).sum := by decide
  have hdescent : baseEnd_1612372 < baseStart_1612372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612445 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 4]
def baseStart_1612445 : Nat := 118140960795 + 1612445 * 2 ^ 59
def prefixEnd_1612445 : Nat := 4983230072969 + 3 ^ 40 * 1612445 * 2
def baseEnd_1612445 : Nat := 367981917306244015654225

theorem tailTrace_1612445 : CollatzResearch.WordTrace tailWord_1612445 prefixEnd_1612445 367981917306244015654225 := by
  unfold tailWord_1612445
  simp only [CollatzResearch.WordTrace]
  refine ⟨58810700643394623526694789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39207133762263082351129859 58810700643394623526694789)
  ·
    refine ⟨11027006370636491911255273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58810700643394623526694789 11027006370636491911255273)
    ·
      refine ⟨8270254777977368933441455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11027006370636491911255273 8270254777977368933441455)
      ·
        refine ⟨12405382166966053400162183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8270254777977368933441455 12405382166966053400162183)
        ·
          refine ⟨18608073250449080100243275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12405382166966053400162183 18608073250449080100243275)
          ·
            refine ⟨27912109875673620150364913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18608073250449080100243275 27912109875673620150364913)
            ·
              refine ⟨20934082406755215112773685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27912109875673620150364913 20934082406755215112773685)
              ·
                refine ⟨1962570225633301416822533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20934082406755215112773685 1962570225633301416822533)
                ·
                  refine ⟨367981917306244015654225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1962570225633301416822533 367981917306244015654225)
                  ·
                    rfl

theorem cell21_1612445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_1612445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612445 prefixEnd_1612445 := by exact prefixLift 1612445
  have htrace : WordTrace (prefixWord ++ tailWord_1612445) baseStart_1612445 baseEnd_1612445 := by
    simpa [prefixWord, tailWord_1612445, baseEnd_1612445] using wordTrace_append hprefix tailTrace_1612445
  have hstable : (prefixWord ++ tailWord_1612445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612445).length < 2 ^ (prefixWord ++ tailWord_1612445).sum := by decide
  have hdescent : baseEnd_1612445 < baseStart_1612445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612462 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_1612462 : Nat := 118140960795 + 1612462 * 2 ^ 59
def prefixEnd_1612462 : Nat := 4983230072969 + 3 ^ 40 * 1612462 * 2
def baseEnd_1612462 : Nat := 367985796937855763870857

theorem tailTrace_1612462 : CollatzResearch.WordTrace tailWord_1612462 prefixEnd_1612462 367985796937855763870857 := by
  unfold tailWord_1612462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351415085541629428757955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39207547122888690286709093 7351415085541629428757955)
  ·
    refine ⟨11027122628312444143136933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7351415085541629428757955 11027122628312444143136933)
    ·
      refine ⟨2067585492808583276838175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11027122628312444143136933 2067585492808583276838175)
      ·
        refine ⟨3101378239212874915257263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067585492808583276838175 3101378239212874915257263)
        ·
          refine ⟨4652067358819312372885895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3101378239212874915257263 4652067358819312372885895)
          ·
            refine ⟨6978101038228968559328843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4652067358819312372885895 6978101038228968559328843)
            ·
              refine ⟨10467151557343452838993265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6978101038228968559328843 10467151557343452838993265)
              ·
                refine ⟨7850363668007589629244949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10467151557343452838993265 7850363668007589629244949)
                ·
                  refine ⟨367985796937855763870857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7850363668007589629244949 367985796937855763870857)
                  ·
                    rfl

theorem cell21_1612462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_1612462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612462 prefixEnd_1612462 := by exact prefixLift 1612462
  have htrace : WordTrace (prefixWord ++ tailWord_1612462) baseStart_1612462 baseEnd_1612462 := by
    simpa [prefixWord, tailWord_1612462, baseEnd_1612462] using wordTrace_append hprefix tailTrace_1612462
  have hstable : (prefixWord ++ tailWord_1612462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612462).length < 2 ^ (prefixWord ++ tailWord_1612462).sum := by decide
  have hdescent : baseEnd_1612462 < baseStart_1612462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612549 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 9]
def baseStart_1612549 : Nat := 118140960795 + 1612549 * 2 ^ 59
def prefixEnd_1612549 : Nat := 4983230072969 + 3 ^ 40 * 1612549 * 2
def baseEnd_1612549 : Nat := 368005651523162945920679

theorem tailTrace_1612549 : CollatzResearch.WordTrace tailWord_1612549 prefixEnd_1612549 368005651523162945920679 := by
  unfold tailWord_1612549
  simp only [CollatzResearch.WordTrace]
  refine ⟨58814493835017849288480701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39209662556678566192320467 58814493835017849288480701)
  ·
    refine ⟨22055435188131693483180263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58814493835017849288480701 22055435188131693483180263)
    ·
      refine ⟨33083152782197540224770395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22055435188131693483180263 33083152782197540224770395)
      ·
        refine ⟨49624729173296310337155593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33083152782197540224770395 49624729173296310337155593)
        ·
          refine ⟨37218546879972232752866695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49624729173296310337155593 37218546879972232752866695)
          ·
            refine ⟨55827820319958349129300043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37218546879972232752866695 55827820319958349129300043)
            ·
              refine ⟨83741730479937523693950065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55827820319958349129300043 83741730479937523693950065)
              ·
                refine ⟨62806297859953142770462549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83741730479937523693950065 62806297859953142770462549)
                ·
                  refine ⟨368005651523162945920679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62806297859953142770462549 368005651523162945920679)
                  ·
                    rfl

theorem cell21_1612549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_1612549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612549 prefixEnd_1612549 := by exact prefixLift 1612549
  have htrace : WordTrace (prefixWord ++ tailWord_1612549) baseStart_1612549 baseEnd_1612549 := by
    simpa [prefixWord, tailWord_1612549, baseEnd_1612549] using wordTrace_append hprefix tailTrace_1612549
  have hstable : (prefixWord ++ tailWord_1612549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612549).length < 2 ^ (prefixWord ++ tailWord_1612549).sum := by decide
  have hdescent : baseEnd_1612549 < baseStart_1612549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612552 : List Nat := [2, 1, 3, 2, 2, 4, 1, 6]
def baseStart_1612552 : Nat := 118140960795 + 1612552 * 2 ^ 59
def prefixEnd_1612552 : Nat := 4983230072969 + 3 ^ 40 * 1612552 * 2
def baseEnd_1612552 : Nat := 122668778721345202456891

theorem tailTrace_1612552 : CollatzResearch.WordTrace tailWord_1612552 prefixEnd_1612552 122668778721345202456891 := by
  unfold tailWord_1612552
  simp only [CollatzResearch.WordTrace]
  refine ⟨29407301627003490400419955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39209735502671320533893273 29407301627003490400419955)
  ·
    refine ⟨44110952440505235600629933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29407301627003490400419955 44110952440505235600629933)
    ·
      refine ⟨16541607165189463350236225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44110952440505235600629933 16541607165189463350236225)
      ·
        refine ⟨12406205373892097512677169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16541607165189463350236225 12406205373892097512677169)
        ·
          refine ⟨9304654030419073134507877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12406205373892097512677169 9304654030419073134507877)
          ·
            refine ⟨1744622630703576212720227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9304654030419073134507877 1744622630703576212720227)
            ·
              refine ⟨2616933946055364319080341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744622630703576212720227 2616933946055364319080341)
              ·
                refine ⟨122668778721345202456891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2616933946055364319080341 122668778721345202456891)
                ·
                  rfl

theorem cell21_1612552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_1612552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612552 prefixEnd_1612552 := by exact prefixLift 1612552
  have htrace : WordTrace (prefixWord ++ tailWord_1612552) baseStart_1612552 baseEnd_1612552 := by
    simpa [prefixWord, tailWord_1612552, baseEnd_1612552] using wordTrace_append hprefix tailTrace_1612552
  have hstable : (prefixWord ++ tailWord_1612552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612552).length < 2 ^ (prefixWord ++ tailWord_1612552).sum := by decide
  have hdescent : baseEnd_1612552 < baseStart_1612552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612589 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1612589 : Nat := 118140960795 + 1612589 * 2 ^ 59
def prefixEnd_1612589 : Nat := 4983230072969 + 3 ^ 40 * 1612589 * 2
def baseEnd_1612589 : Nat := 368014780068131765253931

theorem tailTrace_1612589 : CollatzResearch.WordTrace tailWord_1612589 prefixEnd_1612589 368014780068131765253931 := by
  unfold tailWord_1612589
  simp only [CollatzResearch.WordTrace]
  refine ⟨58815952754872936119936821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39210635169915290746624547 58815952754872936119936821)
  ·
    refine ⟨5513995570769337761244077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58815952754872936119936821 5513995570769337761244077)
    ·
      refine ⟨2067748339038501660466529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5513995570769337761244077 2067748339038501660466529)
      ·
        refine ⟨1550811254278876245349897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2067748339038501660466529 1550811254278876245349897)
        ·
          refine ⟨1163108440709157184012423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1550811254278876245349897 1163108440709157184012423)
          ·
            refine ⟨1744662661063735776018635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163108440709157184012423 1744662661063735776018635)
            ·
              refine ⟨2616993991595603664027953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744662661063735776018635 2616993991595603664027953)
              ·
                refine ⟨1962745493696702748020965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2616993991595603664027953 1962745493696702748020965)
                ·
                  refine ⟨368014780068131765253931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1962745493696702748020965 368014780068131765253931)
                  ·
                    rfl

theorem cell21_1612589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1612589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612589 prefixEnd_1612589 := by exact prefixLift 1612589
  have htrace : WordTrace (prefixWord ++ tailWord_1612589) baseStart_1612589 baseEnd_1612589 := by
    simpa [prefixWord, tailWord_1612589, baseEnd_1612589] using wordTrace_append hprefix tailTrace_1612589
  have hstable : (prefixWord ++ tailWord_1612589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612589).length < 2 ^ (prefixWord ++ tailWord_1612589).sum := by decide
  have hdescent : baseEnd_1612589 < baseStart_1612589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612597 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 6]
def baseStart_1612597 : Nat := 118140960795 + 1612597 * 2 ^ 59
def prefixEnd_1612597 : Nat := 4983230072969 + 3 ^ 40 * 1612597 * 2
def baseEnd_1612597 : Nat := 368016605777125529120581

theorem tailTrace_1612597 : CollatzResearch.WordTrace tailWord_1612597 prefixEnd_1612597 368016605777125529120581 := by
  unfold tailWord_1612597
  simp only [CollatzResearch.WordTrace]
  refine ⟨58816244538843953486228045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39210829692562635657485363 58816244538843953486228045)
  ·
    refine ⟨22056091702066482557335517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58816244538843953486228045 22056091702066482557335517)
    ·
      refine ⟨8271034388274930959000819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22056091702066482557335517 8271034388274930959000819)
      ·
        refine ⟨12406551582412396438501229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8271034388274930959000819 12406551582412396438501229)
        ·
          refine ⟨4652456843404648664437961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12406551582412396438501229 4652456843404648664437961)
          ·
            refine ⟨3489342632553486498328471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4652456843404648664437961 3489342632553486498328471)
            ·
              refine ⟨5234013948830229747492707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489342632553486498328471 5234013948830229747492707)
              ·
                refine ⟨7851020923245344621239061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234013948830229747492707 7851020923245344621239061)
                ·
                  refine ⟨368016605777125529120581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7851020923245344621239061 368016605777125529120581)
                  ·
                    rfl

theorem cell21_1612597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_1612597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612597 prefixEnd_1612597 := by exact prefixLift 1612597
  have htrace : WordTrace (prefixWord ++ tailWord_1612597) baseStart_1612597 baseEnd_1612597 := by
    simpa [prefixWord, tailWord_1612597, baseEnd_1612597] using wordTrace_append hprefix tailTrace_1612597
  have hstable : (prefixWord ++ tailWord_1612597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612597).length < 2 ^ (prefixWord ++ tailWord_1612597).sum := by decide
  have hdescent : baseEnd_1612597 < baseStart_1612597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612628 : List Nat := [2, 4, 1, 1, 4, 1, 1, 7]
def baseStart_1612628 : Nat := 118140960795 + 1612628 * 2 ^ 59
def prefixEnd_1612628 : Nat := 4983230072969 + 3 ^ 40 * 1612628 * 2
def baseEnd_1612628 : Nat := 122674560133158788034617

theorem tailTrace_1612628 : CollatzResearch.WordTrace tailWord_1612628 prefixEnd_1612628 122674560133158788034617 := by
  unfold tailWord_1612628
  simp only [CollatzResearch.WordTrace]
  refine ⟨29408687600865822890303269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39211583467821097187071025 29408687600865822890303269)
  ·
    refine ⟨5514128925162341791931863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29408687600865822890303269 5514128925162341791931863)
    ·
      refine ⟨8271193387743512687897795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5514128925162341791931863 8271193387743512687897795)
      ·
        refine ⟨12406790081615269031846693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8271193387743512687897795 12406790081615269031846693)
        ·
          refine ⟨2326273140302862943471255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12406790081615269031846693 2326273140302862943471255)
          ·
            refine ⟨3489409710454294415206883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326273140302862943471255 3489409710454294415206883)
            ·
              refine ⟨5234114565681441622810325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489409710454294415206883 5234114565681441622810325)
              ·
                refine ⟨122674560133158788034617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5234114565681441622810325 122674560133158788034617)
                ·
                  rfl

theorem cell21_1612628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_1612628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612628 prefixEnd_1612628 := by exact prefixLift 1612628
  have htrace : WordTrace (prefixWord ++ tailWord_1612628) baseStart_1612628 baseEnd_1612628 := by
    simpa [prefixWord, tailWord_1612628, baseEnd_1612628] using wordTrace_append hprefix tailTrace_1612628
  have hstable : (prefixWord ++ tailWord_1612628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612628).length < 2 ^ (prefixWord ++ tailWord_1612628).sum := by decide
  have hdescent : baseEnd_1612628 < baseStart_1612628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612656 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_1612656 : Nat := 118140960795 + 1612656 * 2 ^ 59
def prefixEnd_1612656 : Nat := 4983230072969 + 3 ^ 40 * 1612656 * 2
def baseEnd_1612656 : Nat := 368030070380954537637127

theorem tailTrace_1612656 : CollatzResearch.WordTrace tailWord_1612656 prefixEnd_1612656 368030070380954537637127 := by
  unfold tailWord_1612656
  simp only [CollatzResearch.WordTrace]
  refine ⟨29409198222815103281312911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39212264297086804375083881 29409198222815103281312911)
  ·
    refine ⟨44113797334222654921969367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29409198222815103281312911 44113797334222654921969367)
    ·
      refine ⟨66170696001333982382954051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44113797334222654921969367 66170696001333982382954051)
      ·
        refine ⟨99256044002000973574431077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66170696001333982382954051 99256044002000973574431077)
        ·
          refine ⟨18610508250375182545205827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99256044002000973574431077 18610508250375182545205827)
          ·
            refine ⟨27915762375562773817808741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18610508250375182545205827 27915762375562773817808741)
            ·
              refine ⟨5234205445418020090839139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27915762375562773817808741 5234205445418020090839139)
              ·
                refine ⟨7851308168127030136258709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234205445418020090839139 7851308168127030136258709)
                ·
                  refine ⟨368030070380954537637127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7851308168127030136258709 368030070380954537637127)
                  ·
                    rfl

theorem cell21_1612656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_1612656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612656 prefixEnd_1612656 := by exact prefixLift 1612656
  have htrace : WordTrace (prefixWord ++ tailWord_1612656) baseStart_1612656 baseEnd_1612656 := by
    simpa [prefixWord, tailWord_1612656, baseEnd_1612656] using wordTrace_append hprefix tailTrace_1612656
  have hstable : (prefixWord ++ tailWord_1612656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612656).length < 2 ^ (prefixWord ++ tailWord_1612656).sum := by decide
  have hdescent : baseEnd_1612656 < baseStart_1612656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612721 : List Nat := [1, 2, 2, 4, 4, 1, 1, 6]
def baseStart_1612721 : Nat := 118140960795 + 1612721 * 2 ^ 59
def prefixEnd_1612721 : Nat := 4983230072969 + 3 ^ 40 * 1612721 * 2
def baseEnd_1612721 : Nat := 122681634755509623017887

theorem tailTrace_1612721 : CollatzResearch.WordTrace tailWord_1612721 prefixEnd_1612721 122681634755509623017887 := by
  unfold tailWord_1612721
  simp only [CollatzResearch.WordTrace]
  refine ⟨58820767190394722663742017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39213844793596481775828011 58820767190394722663742017)
  ·
    refine ⟨44115575392796041997806513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58820767190394722663742017 44115575392796041997806513)
    ·
      refine ⟨33086681544597031498354885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44115575392796041997806513 33086681544597031498354885)
      ·
        refine ⟨6203752789611943405941541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33086681544597031498354885 6203752789611943405941541)
        ·
          refine ⟨1163203648052239388614039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6203752789611943405941541 1163203648052239388614039)
          ·
            refine ⟨1744805472078359082921059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163203648052239388614039 1744805472078359082921059)
            ·
              refine ⟨2617208208117538624381589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744805472078359082921059 2617208208117538624381589)
              ·
                refine ⟨122681634755509623017887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2617208208117538624381589 122681634755509623017887)
                ·
                  rfl

theorem cell21_1612721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 6].length) (baseStart_1612721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612721 prefixEnd_1612721 := by exact prefixLift 1612721
  have htrace : WordTrace (prefixWord ++ tailWord_1612721) baseStart_1612721 baseEnd_1612721 := by
    simpa [prefixWord, tailWord_1612721, baseEnd_1612721] using wordTrace_append hprefix tailTrace_1612721
  have hstable : (prefixWord ++ tailWord_1612721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612721).length < 2 ^ (prefixWord ++ tailWord_1612721).sum := by decide
  have hdescent : baseEnd_1612721 < baseStart_1612721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612808 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_1612808 : Nat := 118140960795 + 1612808 * 2 ^ 59
def prefixEnd_1612808 : Nat := 4983230072969 + 3 ^ 40 * 1612808 * 2
def baseEnd_1612808 : Nat := 368064758851836051103483

theorem tailTrace_1612808 : CollatzResearch.WordTrace tailWord_1612808 prefixEnd_1612808 368064758851836051103483 := by
  unfold tailWord_1612808
  simp only [CollatzResearch.WordTrace]
  refine ⟨29411970170539768261079539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39215960227386357681439385 29411970170539768261079539)
  ·
    refine ⟨44117955255809652391619309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29411970170539768261079539 44117955255809652391619309)
    ·
      refine ⟨16544233220928619646857241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44117955255809652391619309 16544233220928619646857241)
      ·
        refine ⟨12408174915696464735142931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16544233220928619646857241 12408174915696464735142931)
        ·
          refine ⟨18612262373544697102714397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12408174915696464735142931 18612262373544697102714397)
          ·
            refine ⟨6979598390079261413517899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18612262373544697102714397 6979598390079261413517899)
            ·
              refine ⟨10469397585118892120276849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6979598390079261413517899 10469397585118892120276849)
              ·
                refine ⟨7852048188839169090207637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10469397585118892120276849 7852048188839169090207637)
                ·
                  refine ⟨368064758851836051103483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7852048188839169090207637 368064758851836051103483)
                  ·
                    rfl

theorem cell21_1612808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_1612808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612808 prefixEnd_1612808 := by exact prefixLift 1612808
  have htrace : WordTrace (prefixWord ++ tailWord_1612808) baseStart_1612808 baseEnd_1612808 := by
    simpa [prefixWord, tailWord_1612808, baseEnd_1612808] using wordTrace_append hprefix tailTrace_1612808
  have hstable : (prefixWord ++ tailWord_1612808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612808).length < 2 ^ (prefixWord ++ tailWord_1612808).sum := by decide
  have hdescent : baseEnd_1612808 < baseStart_1612808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612811 : List Nat := [1, 1, 1, 1, 6, 2, 3, 3, 3]
def baseStart_1612811 : Nat := 118140960795 + 1612811 * 2 ^ 59
def prefixEnd_1612811 : Nat := 4983230072969 + 3 ^ 40 * 1612811 * 2
def baseEnd_1612811 : Nat := 368065443492708712553477

theorem tailTrace_1612811 : CollatzResearch.WordTrace tailWord_1612811 prefixEnd_1612811 368065443492708712553477 := by
  unfold tailWord_1612811
  simp only [CollatzResearch.WordTrace]
  refine ⟨58824049760068668034518287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39216033173379112023012191 58824049760068668034518287)
  ·
    refine ⟨88236074640103002051777431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58824049760068668034518287 88236074640103002051777431)
    ·
      refine ⟨132354111960154503077666147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88236074640103002051777431 132354111960154503077666147)
      ·
        refine ⟨198531167940231754616499221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132354111960154503077666147 198531167940231754616499221)
        ·
          refine ⟨9306148497198363497648401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 198531167940231754616499221 9306148497198363497648401)
          ·
            refine ⟨6979611372898772623236301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9306148497198363497648401 6979611372898772623236301)
            ·
              refine ⟨2617354264837039733713613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6979611372898772623236301 2617354264837039733713613)
              ·
                refine ⟨981507849313889900142605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2617354264837039733713613 981507849313889900142605)
                ·
                  refine ⟨368065443492708712553477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981507849313889900142605 368065443492708712553477)
                  ·
                    rfl

theorem cell21_1612811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 3].length) (baseStart_1612811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612811 prefixEnd_1612811 := by exact prefixLift 1612811
  have htrace : WordTrace (prefixWord ++ tailWord_1612811) baseStart_1612811 baseEnd_1612811 := by
    simpa [prefixWord, tailWord_1612811, baseEnd_1612811] using wordTrace_append hprefix tailTrace_1612811
  have hstable : (prefixWord ++ tailWord_1612811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612811).length < 2 ^ (prefixWord ++ tailWord_1612811).sum := by decide
  have hdescent : baseEnd_1612811 < baseStart_1612811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612828 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 5]
def baseStart_1612828 : Nat := 118140960795 + 1612828 * 2 ^ 59
def prefixEnd_1612828 : Nat := 4983230072969 + 3 ^ 40 * 1612828 * 2
def baseEnd_1612828 : Nat := 368069323124320460770109

theorem tailTrace_1612828 : CollatzResearch.WordTrace tailWord_1612828 prefixEnd_1612828 368069323124320460770109 := by
  unfold tailWord_1612828
  simp only [CollatzResearch.WordTrace]
  refine ⟨29412334900503539968943569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39216446534004719958591425 29412334900503539968943569)
  ·
    refine ⟨22059251175377654976707677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29412334900503539968943569 22059251175377654976707677)
    ·
      refine ⟨8272219190766620616265379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22059251175377654976707677 8272219190766620616265379)
      ·
        refine ⟨12408328786149930924398069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272219190766620616265379 12408328786149930924398069)
        ·
          refine ⟨1163280823701556024162319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12408328786149930924398069 1163280823701556024162319)
          ·
            refine ⟨1744921235552334036243479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163280823701556024162319 1744921235552334036243479)
            ·
              refine ⟨2617381853328501054365219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744921235552334036243479 2617381853328501054365219)
              ·
                refine ⟨3926072779992751581547829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617381853328501054365219 3926072779992751581547829)
                ·
                  refine ⟨368069323124320460770109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3926072779992751581547829 368069323124320460770109)
                  ·
                    rfl

theorem cell21_1612828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_1612828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612828 prefixEnd_1612828 := by exact prefixLift 1612828
  have htrace : WordTrace (prefixWord ++ tailWord_1612828) baseStart_1612828 baseEnd_1612828 := by
    simpa [prefixWord, tailWord_1612828, baseEnd_1612828] using wordTrace_append hprefix tailTrace_1612828
  have hstable : (prefixWord ++ tailWord_1612828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612828).length < 2 ^ (prefixWord ++ tailWord_1612828).sum := by decide
  have hdescent : baseEnd_1612828 < baseStart_1612828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612842 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_1612842 : Nat := 118140960795 + 1612842 * 2 ^ 59
def prefixEnd_1612842 : Nat := 4983230072969 + 3 ^ 40 * 1612842 * 2
def baseEnd_1612842 : Nat := 368072518115059547536747

theorem tailTrace_1612842 : CollatzResearch.WordTrace tailWord_1612842 prefixEnd_1612842 368072518115059547536747 := by
  unfold tailWord_1612842
  simp only [CollatzResearch.WordTrace]
  refine ⟨14706295105739090082224195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39216786948637573552597853 14706295105739090082224195)
  ·
    refine ⟨22059442658608635123336293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14706295105739090082224195 22059442658608635123336293)
    ·
      refine ⟨4136145498489119085625555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22059442658608635123336293 4136145498489119085625555)
      ·
        refine ⟨6204218247733678628438333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136145498489119085625555 6204218247733678628438333)
        ·
          refine ⟨2326581842900129485664375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6204218247733678628438333 2326581842900129485664375)
          ·
            refine ⟨3489872764350194228496563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326581842900129485664375 3489872764350194228496563)
            ·
              refine ⟨5234809146525291342744845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489872764350194228496563 5234809146525291342744845)
              ·
                refine ⟨1963053429946984253529317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5234809146525291342744845 1963053429946984253529317)
                ·
                  refine ⟨368072518115059547536747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1963053429946984253529317 368072518115059547536747)
                  ·
                    rfl

theorem cell21_1612842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_1612842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612842 prefixEnd_1612842 := by exact prefixLift 1612842
  have htrace : WordTrace (prefixWord ++ tailWord_1612842) baseStart_1612842 baseEnd_1612842 := by
    simpa [prefixWord, tailWord_1612842, baseEnd_1612842] using wordTrace_append hprefix tailTrace_1612842
  have hstable : (prefixWord ++ tailWord_1612842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612842).length < 2 ^ (prefixWord ++ tailWord_1612842).sum := by decide
  have hdescent : baseEnd_1612842 < baseStart_1612842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612853 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 7]
def baseStart_1612853 : Nat := 118140960795 + 1612853 * 2 ^ 59
def prefixEnd_1612853 : Nat := 4983230072969 + 3 ^ 40 * 1612853 * 2
def baseEnd_1612853 : Nat := 368075028464925972853391

theorem tailTrace_1612853 : CollatzResearch.WordTrace tailWord_1612853 prefixEnd_1612853 368075028464925972853391 := by
  unfold tailWord_1612853
  simp only [CollatzResearch.WordTrace]
  refine ⟨58825581625916509207547213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39217054417277672805031475 58825581625916509207547213)
  ·
    refine ⟨22059593109718690952830205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58825581625916509207547213 22059593109718690952830205)
    ·
      refine ⟨8272347416144509107311327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22059593109718690952830205 8272347416144509107311327)
      ·
        refine ⟨12408521124216763660966991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272347416144509107311327 12408521124216763660966991)
        ·
          refine ⟨18612781686325145491450487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12408521124216763660966991 18612781686325145491450487)
          ·
            refine ⟨27919172529487718237175731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18612781686325145491450487 27919172529487718237175731)
            ·
              refine ⟨41878758794231577355763597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27919172529487718237175731 41878758794231577355763597)
              ·
                refine ⟨15704534547836841508411349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41878758794231577355763597 15704534547836841508411349)
                ·
                  refine ⟨368075028464925972853391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15704534547836841508411349 368075028464925972853391)
                  ·
                    rfl

theorem cell21_1612853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_1612853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612853 prefixEnd_1612853 := by exact prefixLift 1612853
  have htrace : WordTrace (prefixWord ++ tailWord_1612853) baseStart_1612853 baseEnd_1612853 := by
    simpa [prefixWord, tailWord_1612853, baseEnd_1612853] using wordTrace_append hprefix tailTrace_1612853
  have hstable : (prefixWord ++ tailWord_1612853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612853).length < 2 ^ (prefixWord ++ tailWord_1612853).sum := by decide
  have hdescent : baseEnd_1612853 < baseStart_1612853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612884 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1612884 : Nat := 118140960795 + 1612884 * 2 ^ 59
def prefixEnd_1612884 : Nat := 4983230072969 + 3 ^ 40 * 1612884 * 2
def baseEnd_1612884 : Nat := 368082103087276807836661

theorem tailTrace_1612884 : CollatzResearch.WordTrace tailWord_1612884 prefixEnd_1612884 368082103087276807836661 := by
  unfold tailWord_1612884
  simp only [CollatzResearch.WordTrace]
  refine ⟨29413356144402100750962853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39217808192536134334617137 29413356144402100750962853)
  ·
    refine ⟨5515004277075393890805535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29413356144402100750962853 5515004277075393890805535)
    ·
      refine ⟨8272506415613090836208303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5515004277075393890805535 8272506415613090836208303)
      ·
        refine ⟨12408759623419636254312455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272506415613090836208303 12408759623419636254312455)
        ·
          refine ⟨18613139435129454381468683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12408759623419636254312455 18613139435129454381468683)
          ·
            refine ⟨27919709152694181572203025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18613139435129454381468683 27919709152694181572203025)
            ·
              refine ⟨20939781864520636179152269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27919709152694181572203025 20939781864520636179152269)
              ·
                refine ⟨7852418199195238567182101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20939781864520636179152269 7852418199195238567182101)
                ·
                  refine ⟨368082103087276807836661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7852418199195238567182101 368082103087276807836661)
                  ·
                    rfl

theorem cell21_1612884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1612884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612884 prefixEnd_1612884 := by exact prefixLift 1612884
  have htrace : WordTrace (prefixWord ++ tailWord_1612884) baseStart_1612884 baseEnd_1612884 := by
    simpa [prefixWord, tailWord_1612884, baseEnd_1612884] using wordTrace_append hprefix tailTrace_1612884
  have hstable : (prefixWord ++ tailWord_1612884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612884).length < 2 ^ (prefixWord ++ tailWord_1612884).sum := by decide
  have hdescent : baseEnd_1612884 < baseStart_1612884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612946 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_1612946 : Nat := 118140960795 + 1612946 * 2 ^ 59
def prefixEnd_1612946 : Nat := 4983230072969 + 3 ^ 40 * 1612946 * 2
def baseEnd_1612946 : Nat := 368096252331978477803201

theorem tailTrace_1612946 : CollatzResearch.WordTrace tailWord_1612946 prefixEnd_1612946 368096252331978477803201 := by
  unfold tailWord_1612946
  simp only [CollatzResearch.WordTrace]
  refine ⟨14707243403644896522670673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39219315743053057393788461 14707243403644896522670673)
  ·
    refine ⟨11030432552733672392003005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14707243403644896522670673 11030432552733672392003005)
    ·
      refine ⟨4136412207275127147001127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11030432552733672392003005 4136412207275127147001127)
      ·
        refine ⟨6204618310912690720501691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136412207275127147001127 6204618310912690720501691)
        ·
          refine ⟨9306927466369036080752537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6204618310912690720501691 9306927466369036080752537)
          ·
            refine ⟨6980195599776777060564403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9306927466369036080752537 6980195599776777060564403)
            ·
              refine ⟨10470293399665165590846605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980195599776777060564403 10470293399665165590846605)
              ·
                refine ⟨3926360024874437096567477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10470293399665165590846605 3926360024874437096567477)
                ·
                  refine ⟨368096252331978477803201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3926360024874437096567477 368096252331978477803201)
                  ·
                    rfl

theorem cell21_1612946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_1612946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1612946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1612946 prefixEnd_1612946 := by exact prefixLift 1612946
  have htrace : WordTrace (prefixWord ++ tailWord_1612946) baseStart_1612946 baseEnd_1612946 := by
    simpa [prefixWord, tailWord_1612946, baseEnd_1612946] using wordTrace_append hprefix tailTrace_1612946
  have hstable : (prefixWord ++ tailWord_1612946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612946).length < 2 ^ (prefixWord ++ tailWord_1612946).sum := by decide
  have hdescent : baseEnd_1612946 < baseStart_1612946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613067 : List Nat := [1, 1, 1, 1, 5, 5, 1, 6]
def baseStart_1613067 : Nat := 118140960795 + 1613067 * 2 ^ 59
def prefixEnd_1613067 : Nat := 4983230072969 + 3 ^ 40 * 1613067 * 2
def baseEnd_1613067 : Nat := 122707955393503052095429

theorem tailTrace_1613067 : CollatzResearch.WordTrace tailWord_1613067 prefixEnd_1613067 122707955393503052095429 := by
  unfold tailWord_1613067
  simp only [CollatzResearch.WordTrace]
  refine ⟨58833386847141223755837455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39222257898094149170558303 58833386847141223755837455)
  ·
    refine ⟨88250080270711835633756183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58833386847141223755837455 88250080270711835633756183)
    ·
      refine ⟨132375120406067753450634275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88250080270711835633756183 132375120406067753450634275)
      ·
        refine ⟨198562680609101630175951413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132375120406067753450634275 198562680609101630175951413)
        ·
          refine ⟨18615251307103277828995445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198562680609101630175951413 18615251307103277828995445)
          ·
            refine ⟨1745179810040932296468323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18615251307103277828995445 1745179810040932296468323)
            ·
              refine ⟨2617769715061398444702485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745179810040932296468323 2617769715061398444702485)
              ·
                refine ⟨122707955393503052095429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2617769715061398444702485 122707955393503052095429)
                ·
                  rfl

theorem cell21_1613067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 6].length) (baseStart_1613067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613067 prefixEnd_1613067 := by exact prefixLift 1613067
  have htrace : WordTrace (prefixWord ++ tailWord_1613067) baseStart_1613067 baseEnd_1613067 := by
    simpa [prefixWord, tailWord_1613067, baseEnd_1613067] using wordTrace_append hprefix tailTrace_1613067
  have hstable : (prefixWord ++ tailWord_1613067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613067).length < 2 ^ (prefixWord ++ tailWord_1613067).sum := by decide
  have hdescent : baseEnd_1613067 < baseStart_1613067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613143 : List Nat := [1, 1, 3, 2, 3, 2, 4, 5]
def baseStart_1613143 : Nat := 118140960795 + 1613143 * 2 ^ 59
def prefixEnd_1613143 : Nat := 4983230072969 + 3 ^ 40 * 1613143 * 2
def baseEnd_1613143 : Nat := 122713736805316637673155

theorem tailTrace_1613143 : CollatzResearch.WordTrace tailWord_1613143 prefixEnd_1613143 122713736805316637673155 := by
  unfold tailWord_1613143
  simp only [CollatzResearch.WordTrace]
  refine ⟨58836158794865888735604083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39224105863243925823736055 58836158794865888735604083)
  ·
    refine ⟨88254238192298833103406125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58836158794865888735604083 88254238192298833103406125)
    ·
      refine ⟨33095339322112062413777297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88254238192298833103406125 33095339322112062413777297)
      ·
        refine ⟨24821504491584046810332973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33095339322112062413777297 24821504491584046810332973)
        ·
          refine ⟨9308064184344017553874865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24821504491584046810332973 9308064184344017553874865)
          ·
            refine ⟨6981048138258013165406149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9308064184344017553874865 6981048138258013165406149)
            ·
              refine ⟨1308946525923377468513653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6981048138258013165406149 1308946525923377468513653)
              ·
                refine ⟨122713736805316637673155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1308946525923377468513653 122713736805316637673155)
                ·
                  rfl

theorem cell21_1613143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 5].length) (baseStart_1613143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613143 prefixEnd_1613143 := by exact prefixLift 1613143
  have htrace : WordTrace (prefixWord ++ tailWord_1613143) baseStart_1613143 baseEnd_1613143 := by
    simpa [prefixWord, tailWord_1613143, baseEnd_1613143] using wordTrace_append hprefix tailTrace_1613143
  have hstable : (prefixWord ++ tailWord_1613143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613143).length < 2 ^ (prefixWord ++ tailWord_1613143).sum := by decide
  have hdescent : baseEnd_1613143 < baseStart_1613143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613160 : List Nat := [2, 1, 4, 2, 4, 1, 7]
def baseStart_1613160 : Nat := 118140960795 + 1613160 * 2 ^ 59
def prefixEnd_1613160 : Nat := 4983230072969 + 3 ^ 40 * 1613160 * 2
def baseEnd_1613160 : Nat := 40905010005284629026233

theorem tailTrace_1613160 : CollatzResearch.WordTrace tailWord_1613160 prefixEnd_1613160 40905010005284629026233 := by
  unfold tailWord_1613160
  simp only [CollatzResearch.WordTrace]
  refine ⟨29418389417902150319486467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39224519223869533759315289 29418389417902150319486467)
  ·
    refine ⟨44127584126853225479229701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29418389417902150319486467 44127584126853225479229701)
    ·
      refine ⟨8273922023784979777355569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44127584126853225479229701 8273922023784979777355569)
      ·
        refine ⟨6205441517838734833016677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8273922023784979777355569 6205441517838734833016677)
        ·
          refine ⟨1163520284594762781190627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6205441517838734833016677 1163520284594762781190627)
          ·
            refine ⟨1745280426892144171785941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163520284594762781190627 1745280426892144171785941)
            ·
              refine ⟨40905010005284629026233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1745280426892144171785941 40905010005284629026233)
              ·
                rfl

theorem cell21_1613160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 7].length) (baseStart_1613160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613160 prefixEnd_1613160 := by exact prefixLift 1613160
  have htrace : WordTrace (prefixWord ++ tailWord_1613160) baseStart_1613160 baseEnd_1613160 := by
    simpa [prefixWord, tailWord_1613160, baseEnd_1613160] using wordTrace_append hprefix tailTrace_1613160
  have hstable : (prefixWord ++ tailWord_1613160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613160).length < 2 ^ (prefixWord ++ tailWord_1613160).sum := by decide
  have hdescent : baseEnd_1613160 < baseStart_1613160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613233 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 5]
def baseStart_1613233 : Nat := 118140960795 + 1613233 * 2 ^ 59
def prefixEnd_1613233 : Nat := 4983230072969 + 3 ^ 40 * 1613233 * 2
def baseEnd_1613233 : Nat := 368161749642129756519281

theorem tailTrace_1613233 : CollatzResearch.WordTrace tailWord_1613233 prefixEnd_1613233 368161749642129756519281 := by
  unfold tailWord_1613233
  simp only [CollatzResearch.WordTrace]
  refine ⟨58839441364539834106380353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39226294243026556070920235 58839441364539834106380353)
  ·
    refine ⟨44129581023404875579785265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58839441364539834106380353 44129581023404875579785265)
    ·
      refine ⟨33097185767553656684838949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44129581023404875579785265 33097185767553656684838949)
      ·
        refine ⟨6205722331416310628407303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33097185767553656684838949 6205722331416310628407303)
        ·
          refine ⟨9308583497124465942610955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6205722331416310628407303 9308583497124465942610955)
          ·
            refine ⟨13962875245686698913916433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9308583497124465942610955 13962875245686698913916433)
            ·
              refine ⟨10472156434265024185437325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13962875245686698913916433 10472156434265024185437325)
              ·
                refine ⟨3927058662849384069538997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10472156434265024185437325 3927058662849384069538997)
                ·
                  refine ⟨368161749642129756519281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3927058662849384069538997 368161749642129756519281)
                  ·
                    rfl

theorem cell21_1613233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_1613233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613233 prefixEnd_1613233 := by exact prefixLift 1613233
  have htrace : WordTrace (prefixWord ++ tailWord_1613233) baseStart_1613233 baseEnd_1613233 := by
    simpa [prefixWord, tailWord_1613233, baseEnd_1613233] using wordTrace_append hprefix tailTrace_1613233
  have hstable : (prefixWord ++ tailWord_1613233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613233).length < 2 ^ (prefixWord ++ tailWord_1613233).sum := by decide
  have hdescent : baseEnd_1613233 < baseStart_1613233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613281 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 4]
def baseStart_1613281 : Nat := 118140960795 + 1613281 * 2 ^ 59
def prefixEnd_1613281 : Nat := 4983230072969 + 3 ^ 40 * 1613281 * 2
def baseEnd_1613281 : Nat := 368172703896092339719183

theorem tailTrace_1613281 : CollatzResearch.WordTrace tailWord_1613281 prefixEnd_1613281 368172703896092339719183 := by
  unfold tailWord_1613281
  simp only [CollatzResearch.WordTrace]
  refine ⟨58841192068365938304127697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39227461378910625536085131 58841192068365938304127697)
  ·
    refine ⟨44130894051274453728095773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58841192068365938304127697 44130894051274453728095773)
    ·
      refine ⟨16549085269227920148035915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44130894051274453728095773 16549085269227920148035915)
      ·
        refine ⟨24823627903841880222053873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16549085269227920148035915 24823627903841880222053873)
        ·
          refine ⟨18617720927881410166540405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24823627903841880222053873 18617720927881410166540405)
          ·
            refine ⟨1745411336988882203113163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18617720927881410166540405 1745411336988882203113163)
            ·
              refine ⟨2618117005483323304669745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745411336988882203113163 2618117005483323304669745)
              ·
                refine ⟨1963587754112492478502309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2618117005483323304669745 1963587754112492478502309)
                ·
                  refine ⟨368172703896092339719183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1963587754112492478502309 368172703896092339719183)
                  ·
                    rfl

theorem cell21_1613281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_1613281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613281 prefixEnd_1613281 := by exact prefixLift 1613281
  have htrace : WordTrace (prefixWord ++ tailWord_1613281) baseStart_1613281 baseEnd_1613281 := by
    simpa [prefixWord, tailWord_1613281, baseEnd_1613281] using wordTrace_append hprefix tailTrace_1613281
  have hstable : (prefixWord ++ tailWord_1613281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613281).length < 2 ^ (prefixWord ++ tailWord_1613281).sum := by decide
  have hdescent : baseEnd_1613281 < baseStart_1613281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613298 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_1613298 : Nat := 118140960795 + 1613298 * 2 ^ 59
def prefixEnd_1613298 : Nat := 4983230072969 + 3 ^ 40 * 1613298 * 2
def baseEnd_1613298 : Nat := 368176583527704087935815

theorem tailTrace_1613298 : CollatzResearch.WordTrace tailWord_1613298 prefixEnd_1613298 368176583527704087935815 := by
  unfold tailWord_1613298
  simp only [CollatzResearch.WordTrace]
  refine ⟨14710453027326087551874137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39227874739536233471664365 14710453027326087551874137)
  ·
    refine ⟨11032839770494565663905603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14710453027326087551874137 11032839770494565663905603)
    ·
      refine ⟨16549259655741848495858405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11032839770494565663905603 16549259655741848495858405)
      ·
        refine ⟨3102986185451596592973451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16549259655741848495858405 3102986185451596592973451)
        ·
          refine ⟨4654479278177394889460177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102986185451596592973451 4654479278177394889460177)
          ·
            refine ⟨3490859458633046167095133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4654479278177394889460177 3490859458633046167095133)
            ·
              refine ⟨1309072296987392312660675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3490859458633046167095133 1309072296987392312660675)
              ·
                refine ⟨1963608445481088468991013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309072296987392312660675 1963608445481088468991013)
                ·
                  refine ⟨368176583527704087935815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1963608445481088468991013 368176583527704087935815)
                  ·
                    rfl

theorem cell21_1613298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_1613298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613298 prefixEnd_1613298 := by exact prefixLift 1613298
  have htrace : WordTrace (prefixWord ++ tailWord_1613298) baseStart_1613298 baseEnd_1613298 := by
    simpa [prefixWord, tailWord_1613298, baseEnd_1613298] using wordTrace_append hprefix tailTrace_1613298
  have hstable : (prefixWord ++ tailWord_1613298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613298).length < 2 ^ (prefixWord ++ tailWord_1613298).sum := by decide
  have hdescent : baseEnd_1613298 < baseStart_1613298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613309 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1613309 : Nat := 118140960795 + 1613309 * 2 ^ 59
def prefixEnd_1613309 : Nat := 4983230072969 + 3 ^ 40 * 1613309 * 2
def baseEnd_1613309 : Nat := 368179093877570513252459

theorem tailTrace_1613309 : CollatzResearch.WordTrace tailWord_1613309 prefixEnd_1613309 368179093877570513252459 := by
  unfold tailWord_1613309
  simp only [CollatzResearch.WordTrace]
  refine ⟨58842213312264499086146981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39228142208176332724097987 58842213312264499086146981)
  ·
    refine ⟨11032914996049593578652559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58842213312264499086146981 11032914996049593578652559)
    ·
      refine ⟨16549372494074390367978839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11032914996049593578652559 16549372494074390367978839)
      ·
        refine ⟨24824058741111585551968259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16549372494074390367978839 24824058741111585551968259)
        ·
          refine ⟨37236088111667378327952389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24824058741111585551968259 37236088111667378327952389)
          ·
            refine ⟨6981766520937633436491073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37236088111667378327952389 6981766520937633436491073)
            ·
              refine ⟨5236324890703225077368305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6981766520937633436491073 5236324890703225077368305)
              ·
                refine ⟨3927243668027418808026229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5236324890703225077368305 3927243668027418808026229)
                ·
                  refine ⟨368179093877570513252459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3927243668027418808026229 368179093877570513252459)
                  ·
                    rfl

theorem cell21_1613309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1613309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613309 prefixEnd_1613309 := by exact prefixLift 1613309
  have htrace : WordTrace (prefixWord ++ tailWord_1613309) baseStart_1613309 baseEnd_1613309 := by
    simpa [prefixWord, tailWord_1613309, baseEnd_1613309] using wordTrace_append hprefix tailTrace_1613309
  have hstable : (prefixWord ++ tailWord_1613309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613309).length < 2 ^ (prefixWord ++ tailWord_1613309).sum := by decide
  have hdescent : baseEnd_1613309 < baseStart_1613309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613340 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_1613340 : Nat := 118140960795 + 1613340 * 2 ^ 59
def prefixEnd_1613340 : Nat := 4983230072969 + 3 ^ 40 * 1613340 * 2
def baseEnd_1613340 : Nat := 368186168499921348235729

theorem tailTrace_1613340 : CollatzResearch.WordTrace tailWord_1613340 prefixEnd_1613340 368186168499921348235729 := by
  unfold tailWord_1613340
  simp only [CollatzResearch.WordTrace]
  refine ⟨29421671987576095690262737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39228895983434794253683649 29421671987576095690262737)
  ·
    refine ⟨22066253990682071767697053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29421671987576095690262737 22066253990682071767697053)
    ·
      refine ⟨8274845246505776912886395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22066253990682071767697053 8274845246505776912886395)
      ·
        refine ⟨12412267869758665369329593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8274845246505776912886395 12412267869758665369329593)
        ·
          refine ⟨9309200902318999026997195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12412267869758665369329593 9309200902318999026997195)
          ·
            refine ⟨13963801353478498540495793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9309200902318999026997195 13963801353478498540495793)
            ·
              refine ⟨10472851015108873905371845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13963801353478498540495793 10472851015108873905371845)
              ·
                refine ⟨1963659565332913857257221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10472851015108873905371845 1963659565332913857257221)
                ·
                  refine ⟨368186168499921348235729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1963659565332913857257221 368186168499921348235729)
                  ·
                    rfl

theorem cell21_1613340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_1613340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613340 prefixEnd_1613340 := by exact prefixLift 1613340
  have htrace : WordTrace (prefixWord ++ tailWord_1613340) baseStart_1613340 baseEnd_1613340 := by
    simpa [prefixWord, tailWord_1613340, baseEnd_1613340] using wordTrace_append hprefix tailTrace_1613340
  have hstable : (prefixWord ++ tailWord_1613340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613340).length < 2 ^ (prefixWord ++ tailWord_1613340).sum := by decide
  have hdescent : baseEnd_1613340 < baseStart_1613340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613405 : List Nat := [1, 4, 4, 2, 1, 2, 1, 6]
def baseStart_1613405 : Nat := 118140960795 + 1613405 * 2 ^ 59
def prefixEnd_1613405 : Nat := 4983230072969 + 3 ^ 40 * 1613405 * 2
def baseEnd_1613405 : Nat := 122733667461831893217421

theorem tailTrace_1613405 : CollatzResearch.WordTrace tailWord_1613405 prefixEnd_1613405 122733667461831893217421 := by
  unfold tailWord_1613405
  simp only [CollatzResearch.WordTrace]
  refine ⟨58845714719916707481641669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39230476479944471654427779 58845714719916707481641669)
  ·
    refine ⟨11033571509984382652807813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58845714719916707481641669 11033571509984382652807813)
    ·
      refine ⟨2068794658122071747401465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11033571509984382652807813 2068794658122071747401465)
      ·
        refine ⟨1551595993591553810551099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2068794658122071747401465 1551595993591553810551099)
        ·
          refine ⟨2327393990387330715826649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551595993591553810551099 2327393990387330715826649)
          ·
            refine ⟨1745545492790498036869987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2327393990387330715826649 1745545492790498036869987)
            ·
              refine ⟨2618318239185747055304981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745545492790498036869987 2618318239185747055304981)
              ·
                refine ⟨122733667461831893217421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2618318239185747055304981 122733667461831893217421)
                ·
                  rfl

theorem cell21_1613405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 6].length) (baseStart_1613405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613405 prefixEnd_1613405 := by exact prefixLift 1613405
  have htrace : WordTrace (prefixWord ++ tailWord_1613405) baseStart_1613405 baseEnd_1613405 := by
    simpa [prefixWord, tailWord_1613405, baseEnd_1613405] using wordTrace_append hprefix tailTrace_1613405
  have hstable : (prefixWord ++ tailWord_1613405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613405).length < 2 ^ (prefixWord ++ tailWord_1613405).sum := by decide
  have hdescent : baseEnd_1613405 < baseStart_1613405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613495 : List Nat := [1, 1, 3, 1, 5, 3, 1, 3, 3]
def baseStart_1613495 : Nat := 118140960795 + 1613495 * 2 ^ 59
def prefixEnd_1613495 : Nat := 4983230072969 + 3 ^ 40 * 1613495 * 2
def baseEnd_1613495 : Nat := 368221541611675523152079

theorem tailTrace_1613495 : CollatzResearch.WordTrace tailWord_1613495 prefixEnd_1613495 368221541611675523152079 := by
  unfold tailWord_1613495
  simp only [CollatzResearch.WordTrace]
  refine ⟨58848997289590652852417939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39232664859727101901611959 58848997289590652852417939)
  ·
    refine ⟨88273495934385979278626909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58848997289590652852417939 88273495934385979278626909)
    ·
      refine ⟨33102560975394742229485091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88273495934385979278626909 33102560975394742229485091)
      ·
        refine ⟨49653841463092113344227637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33102560975394742229485091 49653841463092113344227637)
        ·
          refine ⟨4655047637164885626021341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49653841463092113344227637 4655047637164885626021341)
          ·
            refine ⟨1745642863936832109758003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4655047637164885626021341 1745642863936832109758003)
            ·
              refine ⟨2618464295905248164637005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745642863936832109758003 2618464295905248164637005)
              ·
                refine ⟨981924110964468061738877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2618464295905248164637005 981924110964468061738877)
                ·
                  refine ⟨368221541611675523152079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981924110964468061738877 368221541611675523152079)
                  ·
                    rfl

theorem cell21_1613495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 3].length) (baseStart_1613495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613495 prefixEnd_1613495 := by exact prefixLift 1613495
  have htrace : WordTrace (prefixWord ++ tailWord_1613495) baseStart_1613495 baseEnd_1613495 := by
    simpa [prefixWord, tailWord_1613495, baseEnd_1613495] using wordTrace_append hprefix tailTrace_1613495
  have hstable : (prefixWord ++ tailWord_1613495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613495).length < 2 ^ (prefixWord ++ tailWord_1613495).sum := by decide
  have hdescent : baseEnd_1613495 < baseStart_1613495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613520 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_1613520 : Nat := 118140960795 + 1613520 * 2 ^ 59
def prefixEnd_1613520 : Nat := 4983230072969 + 3 ^ 40 * 1613520 * 2
def baseEnd_1613520 : Nat := 368227246952281035235361

theorem tailTrace_1613520 : CollatzResearch.WordTrace tailWord_1613520 prefixEnd_1613520 368227246952281035235361 := by
  unfold tailWord_1613520
  simp only [CollatzResearch.WordTrace]
  refine ⟨29424954557250041061039007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39233272743000054748052009 29424954557250041061039007)
  ·
    refine ⟨44137431835875061591558511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29424954557250041061039007 44137431835875061591558511)
    ·
      refine ⟨66206147753812592387337767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44137431835875061591558511 66206147753812592387337767)
      ·
        refine ⟨99309221630718888581006651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66206147753812592387337767 99309221630718888581006651)
        ·
          refine ⟨148963832446078332871509977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99309221630718888581006651 148963832446078332871509977)
          ·
            refine ⟨111722874334558749653632483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148963832446078332871509977 111722874334558749653632483)
            ·
              refine ⟨167584311501838124480448725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111722874334558749653632483 167584311501838124480448725)
              ·
                refine ⟨3927757300824331042510517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 167584311501838124480448725 3927757300824331042510517)
                ·
                  refine ⟨368227246952281035235361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3927757300824331042510517 368227246952281035235361)
                  ·
                    rfl

theorem cell21_1613520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_1613520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613520 prefixEnd_1613520 := by exact prefixLift 1613520
  have htrace : WordTrace (prefixWord ++ tailWord_1613520) baseStart_1613520 baseEnd_1613520 := by
    simpa [prefixWord, tailWord_1613520, baseEnd_1613520] using wordTrace_append hprefix tailTrace_1613520
  have hstable : (prefixWord ++ tailWord_1613520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613520).length < 2 ^ (prefixWord ++ tailWord_1613520).sum := by decide
  have hdescent : baseEnd_1613520 < baseStart_1613520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613554 : List Nat := [3, 2, 1, 3, 1, 1, 2, 5, 3]
def baseStart_1613554 : Nat := 118140960795 + 1613554 * 2 ^ 59
def prefixEnd_1613554 : Nat := 4983230072969 + 3 ^ 40 * 1613554 * 2
def baseEnd_1613554 : Nat := 368235006215504531668625

theorem tailTrace_1613554 : CollatzResearch.WordTrace tailWord_1613554 prefixEnd_1613554 368235006215504531668625 := by
  unfold tailWord_1613554
  simp only [CollatzResearch.WordTrace]
  refine ⟨14712787299094226482203929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39234099464251270619210477 14712787299094226482203929)
  ·
    refine ⟨11034590474320669861652947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14712787299094226482203929 11034590474320669861652947)
    ·
      refine ⟨16551885711481004792479421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11034590474320669861652947 16551885711481004792479421)
      ·
        refine ⟨6206957141805376797179783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16551885711481004792479421 6206957141805376797179783)
        ·
          refine ⟨9310435712708065195769675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206957141805376797179783 9310435712708065195769675)
          ·
            refine ⟨13965653569062097793654513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9310435712708065195769675 13965653569062097793654513)
            ·
              refine ⟨10474240176796573345240885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13965653569062097793654513 10474240176796573345240885)
              ·
                refine ⟨981960016574678751116333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10474240176796573345240885 981960016574678751116333)
                ·
                  refine ⟨368235006215504531668625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981960016574678751116333 368235006215504531668625)
                  ·
                    rfl

theorem cell21_1613554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_1613554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613554 prefixEnd_1613554 := by exact prefixLift 1613554
  have htrace : WordTrace (prefixWord ++ tailWord_1613554) baseStart_1613554 baseEnd_1613554 := by
    simpa [prefixWord, tailWord_1613554, baseEnd_1613554] using wordTrace_append hprefix tailTrace_1613554
  have hstable : (prefixWord ++ tailWord_1613554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613554).length < 2 ^ (prefixWord ++ tailWord_1613554).sum := by decide
  have hdescent : baseEnd_1613554 < baseStart_1613554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613582 : List Nat := [4, 1, 1, 2, 1, 1, 5, 6]
def baseStart_1613582 : Nat := 118140960795 + 1613582 * 2 ^ 59
def prefixEnd_1613582 : Nat := 4983230072969 + 3 ^ 40 * 1613582 * 2
def baseEnd_1613582 : Nat := 122747132065660901733967

theorem tailTrace_1613582 : CollatzResearch.WordTrace tailWord_1613582 prefixEnd_1613582 122747132065660901733967 := by
  unfold tailWord_1613582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7356521305034433338854375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39234780293516977807223333 7356521305034433338854375)
  ·
    refine ⟨11034781957551650008281563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7356521305034433338854375 11034781957551650008281563)
    ·
      refine ⟨16552172936327475012422345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11034781957551650008281563 16552172936327475012422345)
      ·
        refine ⟨12414129702245606259316759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16552172936327475012422345 12414129702245606259316759)
        ·
          refine ⟨18621194553368409388975139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12414129702245606259316759 18621194553368409388975139)
          ·
            refine ⟨27931791830052614083462709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18621194553368409388975139 27931791830052614083462709)
            ·
              refine ⟨2618605484067432570324629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27931791830052614083462709 2618605484067432570324629)
              ·
                refine ⟨122747132065660901733967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2618605484067432570324629 122747132065660901733967)
                ·
                  rfl

theorem cell21_1613582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_1613582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613582 prefixEnd_1613582 := by exact prefixLift 1613582
  have htrace : WordTrace (prefixWord ++ tailWord_1613582) baseStart_1613582 baseEnd_1613582 := by
    simpa [prefixWord, tailWord_1613582, baseEnd_1613582] using wordTrace_append hprefix tailTrace_1613582
  have hstable : (prefixWord ++ tailWord_1613582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613582).length < 2 ^ (prefixWord ++ tailWord_1613582).sum := by decide
  have hdescent : baseEnd_1613582 < baseStart_1613582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613588 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 5]
def baseStart_1613588 : Nat := 118140960795 + 1613588 * 2 ^ 59
def prefixEnd_1613588 : Nat := 4983230072969 + 3 ^ 40 * 1613588 * 2
def baseEnd_1613588 : Nat := 368242765478728028101889

theorem tailTrace_1613588 : CollatzResearch.WordTrace tailWord_1613588 prefixEnd_1613588 368242765478728028101889 := by
  unfold tailWord_1613588
  simp only [CollatzResearch.WordTrace]
  refine ⟨29426194639126864867776709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39234926185502486490368945 29426194639126864867776709)
  ·
    refine ⟨5517411494836287162708133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29426194639126864867776709 5517411494836287162708133)
    ·
      refine ⟨1034514655281803843007775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5517411494836287162708133 1034514655281803843007775)
      ·
        refine ⟨1551771982922705764511663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034514655281803843007775 1551771982922705764511663)
        ·
          refine ⟨2327657974384058646767495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551771982922705764511663 2327657974384058646767495)
          ·
            refine ⟨3491486961576087970151243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327657974384058646767495 3491486961576087970151243)
            ·
              refine ⟨5237230442364131955226865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491486961576087970151243 5237230442364131955226865)
              ·
                refine ⟨3927922831773098966420149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5237230442364131955226865 3927922831773098966420149)
                ·
                  refine ⟨368242765478728028101889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3927922831773098966420149 368242765478728028101889)
                  ·
                    rfl

theorem cell21_1613588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_1613588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613588 prefixEnd_1613588 := by exact prefixLift 1613588
  have htrace : WordTrace (prefixWord ++ tailWord_1613588) baseStart_1613588 baseEnd_1613588 := by
    simpa [prefixWord, tailWord_1613588, baseEnd_1613588] using wordTrace_append hprefix tailTrace_1613588
  have hstable : (prefixWord ++ tailWord_1613588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613588).length < 2 ^ (prefixWord ++ tailWord_1613588).sum := by decide
  have hdescent : baseEnd_1613588 < baseStart_1613588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613630 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_1613630 : Nat := 118140960795 + 1613630 * 2 ^ 59
def prefixEnd_1613630 : Nat := 4983230072969 + 3 ^ 40 * 1613630 * 2
def baseEnd_1613630 : Nat := 368252350450945288401803

theorem tailTrace_1613630 : CollatzResearch.WordTrace tailWord_1613630 prefixEnd_1613630 368252350450945288401803 := by
  unfold tailWord_1613630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7356740143012696363572793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39235947429401047272388229 7356740143012696363572793)
  ·
    refine ⟨5517555107259522272679595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7356740143012696363572793 5517555107259522272679595)
    ·
      refine ⟨8276332660889283409019393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5517555107259522272679595 8276332660889283409019393)
      ·
        refine ⟨6207249495666962556764545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8276332660889283409019393 6207249495666962556764545)
        ·
          refine ⟨4655437121750221917573409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6207249495666962556764545 4655437121750221917573409)
          ·
            refine ⟨3491577841312666438180057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4655437121750221917573409 3491577841312666438180057)
            ·
              refine ⟨2618683380984499828635043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3491577841312666438180057 2618683380984499828635043)
              ·
                refine ⟨3928025071476749742952565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618683380984499828635043 3928025071476749742952565)
                ·
                  refine ⟨368252350450945288401803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3928025071476749742952565 368252350450945288401803)
                  ·
                    rfl

theorem cell21_1613630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_1613630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613630 prefixEnd_1613630 := by exact prefixLift 1613630
  have htrace : WordTrace (prefixWord ++ tailWord_1613630) baseStart_1613630 baseEnd_1613630 := by
    simpa [prefixWord, tailWord_1613630, baseEnd_1613630] using wordTrace_append hprefix tailTrace_1613630
  have hstable : (prefixWord ++ tailWord_1613630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613630).length < 2 ^ (prefixWord ++ tailWord_1613630).sum := by decide
  have hdescent : baseEnd_1613630 < baseStart_1613630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613641 : List Nat := [1, 2, 1, 1, 2, 4, 2, 8]
def baseStart_1613641 : Nat := 118140960795 + 1613641 * 2 ^ 59
def prefixEnd_1613641 : Nat := 4983230072969 + 3 ^ 40 * 1613641 * 2
def baseEnd_1613641 : Nat := 122751620266937237906149

theorem tailTrace_1613641 : CollatzResearch.WordTrace tailWord_1613641 prefixEnd_1613641 122751620266937237906149 := by
  unfold tailWord_1613641
  simp only [CollatzResearch.WordTrace]
  refine ⟨58854322347061719787232777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39236214898041146524821851 58854322347061719787232777)
  ·
    refine ⟨44140741760296289840424583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58854322347061719787232777 44140741760296289840424583)
    ·
      refine ⟨66211112640444434760636875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44140741760296289840424583 66211112640444434760636875)
      ·
        refine ⟨99316668960666652140955313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66211112640444434760636875 99316668960666652140955313)
        ·
          refine ⟨74487501720499989105716485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99316668960666652140955313 74487501720499989105716485)
          ·
            refine ⟨13966406572593747957321841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74487501720499989105716485 13966406572593747957321841)
            ·
              refine ⟨10474804929445310967991381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13966406572593747957321841 10474804929445310967991381)
              ·
                refine ⟨122751620266937237906149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10474804929445310967991381 122751620266937237906149)
                ·
                  rfl

theorem cell21_1613641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 8].length) (baseStart_1613641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613641 prefixEnd_1613641 := by exact prefixLift 1613641
  have htrace : WordTrace (prefixWord ++ tailWord_1613641) baseStart_1613641 baseEnd_1613641 := by
    simpa [prefixWord, tailWord_1613641, baseEnd_1613641] using wordTrace_append hprefix tailTrace_1613641
  have hstable : (prefixWord ++ tailWord_1613641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613641).length < 2 ^ (prefixWord ++ tailWord_1613641).sum := by decide
  have hdescent : baseEnd_1613641 < baseStart_1613641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613717 : List Nat := [1, 3, 2, 1, 1, 3, 1, 9]
def baseStart_1613717 : Nat := 118140960795 + 1613717 * 2 ^ 59
def prefixEnd_1613717 : Nat := 4983230072969 + 3 ^ 40 * 1613717 * 2
def baseEnd_1613717 : Nat := 122757401678750823483875

theorem tailTrace_1613717 : CollatzResearch.WordTrace tailWord_1613717 prefixEnd_1613717 122757401678750823483875 := by
  unfold tailWord_1613717
  simp only [CollatzResearch.WordTrace]
  refine ⟨58857094294786384766999405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39238062863190923177999603 58857094294786384766999405)
  ·
    refine ⟨22071410360544894287624777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58857094294786384766999405 22071410360544894287624777)
    ·
      refine ⟨16553557770408670715718583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22071410360544894287624777 16553557770408670715718583)
      ·
        refine ⟨24830336655613006073577875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16553557770408670715718583 24830336655613006073577875)
        ·
          refine ⟨37245504983419509110366813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24830336655613006073577875 37245504983419509110366813)
          ·
            refine ⟨13967064368782315916387555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37245504983419509110366813 13967064368782315916387555)
            ·
              refine ⟨20950596553173473874581333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13967064368782315916387555 20950596553173473874581333)
              ·
                refine ⟨122757401678750823483875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20950596553173473874581333 122757401678750823483875)
                ·
                  rfl

theorem cell21_1613717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 9].length) (baseStart_1613717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613717 prefixEnd_1613717 := by exact prefixLift 1613717
  have htrace : WordTrace (prefixWord ++ tailWord_1613717) baseStart_1613717 baseEnd_1613717 := by
    simpa [prefixWord, tailWord_1613717, baseEnd_1613717] using wordTrace_append hprefix tailTrace_1613717
  have hstable : (prefixWord ++ tailWord_1613717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613717).length < 2 ^ (prefixWord ++ tailWord_1613717).sum := by decide
  have hdescent : baseEnd_1613717 < baseStart_1613717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613788 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 4]
def baseStart_1613788 : Nat := 118140960795 + 1613788 * 2 ^ 59
def prefixEnd_1613788 : Nat := 4983230072969 + 3 ^ 40 * 1613788 * 2
def baseEnd_1613788 : Nat := 368288408203572124768147

theorem tailTrace_1613788 : CollatzResearch.WordTrace tailWord_1613788 prefixEnd_1613788 368288408203572124768147 := by
  unfold tailWord_1613788
  simp only [CollatzResearch.WordTrace]
  refine ⟨29429841938764581946417009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39239789251686109261889345 29429841938764581946417009)
  ·
    refine ⟨22072381454073436459812757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29429841938764581946417009 22072381454073436459812757)
    ·
      refine ⟨1034642880659692334053723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22072381454073436459812757 1034642880659692334053723)
      ·
        refine ⟨1551964320989538501080585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034642880659692334053723 1551964320989538501080585)
        ·
          refine ⟨1163973240742153875810439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1551964320989538501080585 1163973240742153875810439)
          ·
            refine ⟨1745959861113230813715659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163973240742153875810439 1745959861113230813715659)
            ·
              refine ⟨2618939791669846220573489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745959861113230813715659 2618939791669846220573489)
              ·
                refine ⟨1964204843752384665430117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2618939791669846220573489 1964204843752384665430117)
                ·
                  refine ⟨368288408203572124768147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964204843752384665430117 368288408203572124768147)
                  ·
                    rfl

theorem cell21_1613788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_1613788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613788 prefixEnd_1613788 := by exact prefixLift 1613788
  have htrace : WordTrace (prefixWord ++ tailWord_1613788) baseStart_1613788 baseEnd_1613788 := by
    simpa [prefixWord, tailWord_1613788, baseEnd_1613788] using wordTrace_append hprefix tailTrace_1613788
  have hstable : (prefixWord ++ tailWord_1613788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613788).length < 2 ^ (prefixWord ++ tailWord_1613788).sum := by decide
  have hdescent : baseEnd_1613788 < baseStart_1613788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613844 : List Nat := [2, 4, 3, 2, 1, 2, 7]
def baseStart_1613844 : Nat := 118140960795 + 1613844 * 2 ^ 59
def prefixEnd_1613844 : Nat := 4983230072969 + 3 ^ 40 * 1613844 * 2
def baseEnd_1613844 : Nat := 40922354240725385759411

theorem tailTrace_1613844 : CollatzResearch.WordTrace tailWord_1613844 prefixEnd_1613844 40922354240725385759411 := by
  unfold tailWord_1613844
  simp only [CollatzResearch.WordTrace]
  refine ⟨29430863182663142728436293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39241150910217523637915057 29430863182663142728436293)
  ·
    refine ⟨5518286846749339261581805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29430863182663142728436293 5518286846749339261581805)
    ·
      refine ⟨2069357567531002223093177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5518286846749339261581805 2069357567531002223093177)
      ·
        refine ⟨1552018175648251667319883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2069357567531002223093177 1552018175648251667319883)
        ·
          refine ⟨2328027263472377500979825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552018175648251667319883 2328027263472377500979825)
          ·
            refine ⟨1746020447604283125734869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2328027263472377500979825 1746020447604283125734869)
            ·
              refine ⟨40922354240725385759411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1746020447604283125734869 40922354240725385759411)
              ·
                rfl

theorem cell21_1613844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 7].length) (baseStart_1613844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613844 prefixEnd_1613844 := by exact prefixLift 1613844
  have htrace : WordTrace (prefixWord ++ tailWord_1613844) baseStart_1613844 baseEnd_1613844 := by
    simpa [prefixWord, tailWord_1613844, baseEnd_1613844] using wordTrace_append hprefix tailTrace_1613844
  have hstable : (prefixWord ++ tailWord_1613844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613844).length < 2 ^ (prefixWord ++ tailWord_1613844).sum := by decide
  have hdescent : baseEnd_1613844 < baseStart_1613844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613855 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 4]
def baseStart_1613855 : Nat := 118140960795 + 1613855 * 2 ^ 59
def prefixEnd_1613855 : Nat := 4983230072969 + 3 ^ 40 * 1613855 * 2
def baseEnd_1613855 : Nat := 368303698516394897151343

theorem tailTrace_1613855 : CollatzResearch.WordTrace tailWord_1613855 prefixEnd_1613855 368303698516394897151343 := by
  unfold tailWord_1613855
  simp only [CollatzResearch.WordTrace]
  refine ⟨58862127568286434335523019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39241418378857622890348679 58862127568286434335523019)
  ·
    refine ⟨88293191352429651503284529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58862127568286434335523019 88293191352429651503284529)
    ·
      refine ⟨66219893514322238627463397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88293191352429651503284529 66219893514322238627463397)
      ·
        refine ⟨12416230033935419742649387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66219893514322238627463397 12416230033935419742649387)
        ·
          refine ⟨18624345050903129613974081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12416230033935419742649387 18624345050903129613974081)
          ·
            refine ⟨13968258788177347210480561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18624345050903129613974081 13968258788177347210480561)
            ·
              refine ⟨10476194091133010407860421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13968258788177347210480561 10476194091133010407860421)
              ·
                refine ⟨1964286392087439451473829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10476194091133010407860421 1964286392087439451473829)
                ·
                  refine ⟨368303698516394897151343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964286392087439451473829 368303698516394897151343)
                  ·
                    rfl

theorem cell21_1613855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 4].length) (baseStart_1613855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613855 prefixEnd_1613855 := by exact prefixLift 1613855
  have htrace : WordTrace (prefixWord ++ tailWord_1613855) baseStart_1613855 baseEnd_1613855 := by
    simpa [prefixWord, tailWord_1613855, baseEnd_1613855] using wordTrace_append hprefix tailTrace_1613855
  have hstable : (prefixWord ++ tailWord_1613855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613855).length < 2 ^ (prefixWord ++ tailWord_1613855).sum := by decide
  have hdescent : baseEnd_1613855 < baseStart_1613855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613872 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 4]
def baseStart_1613872 : Nat := 118140960795 + 1613872 * 2 ^ 59
def prefixEnd_1613872 : Nat := 4983230072969 + 3 ^ 40 * 1613872 * 2
def baseEnd_1613872 : Nat := 368307578148006645367975

theorem tailTrace_1613872 : CollatzResearch.WordTrace tailWord_1613872 prefixEnd_1613872 368307578148006645367975 := by
  unfold tailWord_1613872
  simp only [CollatzResearch.WordTrace]
  refine ⟨29431373804612423119445935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39241831739483230825927913 29431373804612423119445935)
  ·
    refine ⟨44147060706918634679168903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29431373804612423119445935 44147060706918634679168903)
    ·
      refine ⟨66220591060377952018753355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44147060706918634679168903 66220591060377952018753355)
      ·
        refine ⟨99330886590566928028130033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66220591060377952018753355 99330886590566928028130033)
        ·
          refine ⟨74498164942925196021097525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99330886590566928028130033 74498164942925196021097525)
          ·
            refine ⟨6984202963399237126977893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74498164942925196021097525 6984202963399237126977893)
            ·
              refine ⟨1309538055637356961308355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6984202963399237126977893 1309538055637356961308355)
              ·
                refine ⟨1964307083456035441962533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309538055637356961308355 1964307083456035441962533)
                ·
                  refine ⟨368307578148006645367975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964307083456035441962533 368307578148006645367975)
                  ·
                    rfl

theorem cell21_1613872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_1613872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613872 prefixEnd_1613872 := by exact prefixLift 1613872
  have htrace : WordTrace (prefixWord ++ tailWord_1613872) baseStart_1613872 baseEnd_1613872 := by
    simpa [prefixWord, tailWord_1613872, baseEnd_1613872] using wordTrace_append hprefix tailTrace_1613872
  have hstable : (prefixWord ++ tailWord_1613872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613872).length < 2 ^ (prefixWord ++ tailWord_1613872).sum := by decide
  have hdescent : baseEnd_1613872 < baseStart_1613872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613982 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1613982 : Nat := 118140960795 + 1613982 * 2 ^ 59
def prefixEnd_1613982 : Nat := 4983230072969 + 3 ^ 40 * 1613982 * 2
def baseEnd_1613982 : Nat := 368332681646670898534417

theorem tailTrace_1613982 : CollatzResearch.WordTrace tailWord_1613982 prefixEnd_1613982 368332681646670898534417 := by
  unfold tailWord_1613982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7358344954853291878174525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39244506425884223350264133 7358344954853291878174525)
  ·
    refine ⟨2759379358069984454315447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7358344954853291878174525 2759379358069984454315447)
    ·
      refine ⟨4139069037104976681473171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759379358069984454315447 4139069037104976681473171)
      ·
        refine ⟨6208603555657465022209757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139069037104976681473171 6208603555657465022209757)
        ·
          refine ⟨2328226333371549383328659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6208603555657465022209757 2328226333371549383328659)
          ·
            refine ⟨3492339500057324074992989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328226333371549383328659 3492339500057324074992989)
            ·
              refine ⟨1309627312521496528122371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3492339500057324074992989 1309627312521496528122371)
              ·
                refine ⟨1964440968782244792183557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309627312521496528122371 1964440968782244792183557)
                ·
                  refine ⟨368332681646670898534417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964440968782244792183557 368332681646670898534417)
                  ·
                    rfl

theorem cell21_1613982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1613982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1613982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1613982 prefixEnd_1613982 := by exact prefixLift 1613982
  have htrace : WordTrace (prefixWord ++ tailWord_1613982) baseStart_1613982 baseEnd_1613982 := by
    simpa [prefixWord, tailWord_1613982, baseEnd_1613982] using wordTrace_append hprefix tailTrace_1613982
  have hstable : (prefixWord ++ tailWord_1613982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613982).length < 2 ^ (prefixWord ++ tailWord_1613982).sum := by decide
  have hdescent : baseEnd_1613982 < baseStart_1613982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614083 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 4]
def baseStart_1614083 : Nat := 118140960795 + 1614083 * 2 ^ 59
def prefixEnd_1614083 : Nat := 4983230072969 + 3 ^ 40 * 1614083 * 2
def baseEnd_1614083 : Nat := 368355731222717167350877

theorem tailTrace_1614083 : CollatzResearch.WordTrace tailWord_1614083 prefixEnd_1614083 368355731222717167350877 := by
  unfold tailWord_1614083
  simp only [CollatzResearch.WordTrace]
  refine ⟨58870443411460429274822903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39246962274306952849881935 58870443411460429274822903)
  ·
    refine ⟨88305665117190643912234355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58870443411460429274822903 88305665117190643912234355)
    ·
      refine ⟨132458497675785965868351533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88305665117190643912234355 132458497675785965868351533)
      ·
        refine ⟨49671936628419737200631825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132458497675785965868351533 49671936628419737200631825)
        ·
          refine ⟨37253952471314802900473869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49671936628419737200631825 37253952471314802900473869)
          ·
            refine ⟨13970232176743051087677701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37253952471314802900473869 13970232176743051087677701)
            ·
              refine ⟨2619418533139322078939569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13970232176743051087677701 2619418533139322078939569)
              ·
                refine ⟨1964563899854491559204677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2619418533139322078939569 1964563899854491559204677)
                ·
                  refine ⟨368355731222717167350877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964563899854491559204677 368355731222717167350877)
                  ·
                    rfl

theorem cell21_1614083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 4].length) (baseStart_1614083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614083 prefixEnd_1614083 := by exact prefixLift 1614083
  have htrace : WordTrace (prefixWord ++ tailWord_1614083) baseStart_1614083 baseEnd_1614083 := by
    simpa [prefixWord, tailWord_1614083, baseEnd_1614083] using wordTrace_append hprefix tailTrace_1614083
  have hstable : (prefixWord ++ tailWord_1614083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614083).length < 2 ^ (prefixWord ++ tailWord_1614083).sum := by decide
  have hdescent : baseEnd_1614083 < baseStart_1614083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614097 : List Nat := [1, 2, 2, 1, 1, 5, 3, 6]
def baseStart_1614097 : Nat := 118140960795 + 1614097 * 2 ^ 59
def prefixEnd_1614097 : Nat := 4983230072969 + 3 ^ 40 * 1614097 * 2
def baseEnd_1614097 : Nat := 122786308737818751372505

theorem tailTrace_1614097 : CollatzResearch.WordTrace tailWord_1614097 prefixEnd_1614097 122786308737818751372505 := by
  unfold tailWord_1614097
  simp only [CollatzResearch.WordTrace]
  refine ⟨58870954033409709665832545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39247302688939806443888363 58870954033409709665832545)
  ·
    refine ⟨44153215525057282249374409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58870954033409709665832545 44153215525057282249374409)
    ·
      refine ⟨33114911643792961687030807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44153215525057282249374409 33114911643792961687030807)
      ·
        refine ⟨49672367465689442530546211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33114911643792961687030807 49672367465689442530546211)
        ·
          refine ⟨74508551198534163795819317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49672367465689442530546211 74508551198534163795819317)
          ·
            refine ⟨6985176674862577855858061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74508551198534163795819317 6985176674862577855858061)
            ·
              refine ⟨2619441253073466695946773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6985176674862577855858061 2619441253073466695946773)
              ·
                refine ⟨122786308737818751372505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2619441253073466695946773 122786308737818751372505)
                ·
                  rfl

theorem cell21_1614097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 6].length) (baseStart_1614097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614097 prefixEnd_1614097 := by exact prefixLift 1614097
  have htrace : WordTrace (prefixWord ++ tailWord_1614097) baseStart_1614097 baseEnd_1614097 := by
    simpa [prefixWord, tailWord_1614097, baseEnd_1614097] using wordTrace_append hprefix tailTrace_1614097
  have hstable : (prefixWord ++ tailWord_1614097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614097).length < 2 ^ (prefixWord ++ tailWord_1614097).sum := by decide
  have hdescent : baseEnd_1614097 < baseStart_1614097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614280 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_1614280 : Nat := 118140960795 + 1614280 * 2 ^ 59
def prefixEnd_1614280 : Nat := 4983230072969 + 3 ^ 40 * 1614280 * 2
def baseEnd_1614280 : Nat := 368400689306688602567141

theorem tailTrace_1614280 : CollatzResearch.WordTrace tailWord_1614280 prefixEnd_1614280 368400689306688602567141 := by
  unfold tailWord_1614280
  simp only [CollatzResearch.WordTrace]
  refine ⟨29438814295873365959872147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39251752394497821279829529 29438814295873365959872147)
  ·
    refine ⟨44158221443810048939808221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29438814295873365959872147 44158221443810048939808221)
    ·
      refine ⟨16559333041428768352428083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44158221443810048939808221 16559333041428768352428083)
      ·
        refine ⟨24838999562143152528642125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16559333041428768352428083 24838999562143152528642125)
        ·
          refine ⟨9314624835803682198240797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24838999562143152528642125 9314624835803682198240797)
          ·
            refine ⟨3492984313426380824340299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9314624835803682198240797 3492984313426380824340299)
            ·
              refine ⟨5239476470139571236510449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3492984313426380824340299 5239476470139571236510449)
              ·
                refine ⟨3929607352604678427382837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239476470139571236510449 3929607352604678427382837)
                ·
                  refine ⟨368400689306688602567141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3929607352604678427382837 368400689306688602567141)
                  ·
                    rfl

theorem cell21_1614280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_1614280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614280 prefixEnd_1614280 := by exact prefixLift 1614280
  have htrace : WordTrace (prefixWord ++ tailWord_1614280) baseStart_1614280 baseEnd_1614280 := by
    simpa [prefixWord, tailWord_1614280, baseEnd_1614280] using wordTrace_append hprefix tailTrace_1614280
  have hstable : (prefixWord ++ tailWord_1614280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614280).length < 2 ^ (prefixWord ++ tailWord_1614280).sum := by decide
  have hdescent : baseEnd_1614280 < baseStart_1614280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614297 : List Nat := [1, 2, 1, 2, 4, 1, 4, 3, 3]
def baseStart_1614297 : Nat := 118140960795 + 1614297 * 2 ^ 59
def prefixEnd_1614297 : Nat := 4983230072969 + 3 ^ 40 * 1614297 * 2
def baseEnd_1614297 : Nat := 368404568938300350783773

theorem tailTrace_1614297 : CollatzResearch.WordTrace tailWord_1614297 prefixEnd_1614297 368404568938300350783773 := by
  unfold tailWord_1614297
  simp only [CollatzResearch.WordTrace]
  refine ⟨58878248632685143823113145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39252165755123429215408763 58878248632685143823113145)
  ·
    refine ⟨44158686474513857867334859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58878248632685143823113145 44158686474513857867334859)
    ·
      refine ⟨66238029711770786801002289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44158686474513857867334859 66238029711770786801002289)
      ·
        refine ⟨49678522283828090100751717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66238029711770786801002289 49678522283828090100751717)
        ·
          refine ⟨9314722928217766893890947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49678522283828090100751717 9314722928217766893890947)
          ·
            refine ⟨13972084392326650340836421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9314722928217766893890947 13972084392326650340836421)
            ·
              refine ⟨2619765823561246938906829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13972084392326650340836421 2619765823561246938906829)
              ·
                refine ⟨982412183835467602090061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2619765823561246938906829 982412183835467602090061)
                ·
                  refine ⟨368404568938300350783773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982412183835467602090061 368404568938300350783773)
                  ·
                    rfl

theorem cell21_1614297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 3].length) (baseStart_1614297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614297 prefixEnd_1614297 := by exact prefixLift 1614297
  have htrace : WordTrace (prefixWord ++ tailWord_1614297) baseStart_1614297 baseEnd_1614297 := by
    simpa [prefixWord, tailWord_1614297, baseEnd_1614297] using wordTrace_append hprefix tailTrace_1614297
  have hstable : (prefixWord ++ tailWord_1614297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614297).length < 2 ^ (prefixWord ++ tailWord_1614297).sum := by decide
  have hdescent : baseEnd_1614297 < baseStart_1614297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614339 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 5]
def baseStart_1614339 : Nat := 118140960795 + 1614339 * 2 ^ 59
def prefixEnd_1614339 : Nat := 4983230072969 + 3 ^ 40 * 1614339 * 2
def baseEnd_1614339 : Nat := 368414153910517611083687

theorem tailTrace_1614339 : CollatzResearch.WordTrace tailWord_1614339 prefixEnd_1614339 368414153910517611083687 := by
  unfold tailWord_1614339
  simp only [CollatzResearch.WordTrace]
  refine ⟨58879780498532984996142071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39253186999021989997428047 58879780498532984996142071)
  ·
    refine ⟨88319670747799477494213107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58879780498532984996142071 88319670747799477494213107)
    ·
      refine ⟨132479506121699216241319661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88319670747799477494213107 132479506121699216241319661)
      ·
        refine ⟨49679814795637206090494873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132479506121699216241319661 49679814795637206090494873)
        ·
          refine ⟨37259861096727904567871155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49679814795637206090494873 37259861096727904567871155)
          ·
            refine ⟨55889791645091856851806733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37259861096727904567871155 55889791645091856851806733)
            ·
              refine ⟨20958671866909446319427525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55889791645091856851806733 20958671866909446319427525)
              ·
                refine ⟨3929750975045521184892661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20958671866909446319427525 3929750975045521184892661)
                ·
                  refine ⟨368414153910517611083687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3929750975045521184892661 368414153910517611083687)
                  ·
                    rfl

theorem cell21_1614339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_1614339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614339 prefixEnd_1614339 := by exact prefixLift 1614339
  have htrace : WordTrace (prefixWord ++ tailWord_1614339) baseStart_1614339 baseEnd_1614339 := by
    simpa [prefixWord, tailWord_1614339, baseEnd_1614339] using wordTrace_append hprefix tailTrace_1614339
  have hstable : (prefixWord ++ tailWord_1614339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614339).length < 2 ^ (prefixWord ++ tailWord_1614339).sum := by decide
  have hdescent : baseEnd_1614339 < baseStart_1614339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614359 : List Nat := [1, 1, 3, 6, 2, 1, 7]
def baseStart_1614359 : Nat := 118140960795 + 1614359 * 2 ^ 59
def prefixEnd_1614359 : Nat := 4983230072969 + 3 ^ 40 * 1614359 * 2
def baseEnd_1614359 : Nat := 40935413131444668972257

theorem tailTrace_1614359 : CollatzResearch.WordTrace tailWord_1614359 prefixEnd_1614359 40935413131444668972257 := by
  unfold tailWord_1614359
  simp only [CollatzResearch.WordTrace]
  refine ⟨58880509958460528411870131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39253673305640352274580087 58880509958460528411870131)
  ·
    refine ⟨88320764937690792617805197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58880509958460528411870131 88320764937690792617805197)
    ·
      refine ⟨33120286851634047231676949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88320764937690792617805197 33120286851634047231676949)
      ·
        refine ⟨1552513446170345963984857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33120286851634047231676949 1552513446170345963984857)
        ·
          refine ⟨1164385084627759472988643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552513446170345963984857 1164385084627759472988643)
          ·
            refine ⟨1746577626941639209482965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164385084627759472988643 1746577626941639209482965)
            ·
              refine ⟨40935413131444668972257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1746577626941639209482965 40935413131444668972257)
              ·
                rfl

theorem cell21_1614359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 7].length) (baseStart_1614359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614359 prefixEnd_1614359 := by exact prefixLift 1614359
  have htrace : WordTrace (prefixWord ++ tailWord_1614359) baseStart_1614359 baseEnd_1614359 := by
    simpa [prefixWord, tailWord_1614359, baseEnd_1614359] using wordTrace_append hprefix tailTrace_1614359
  have hstable : (prefixWord ++ tailWord_1614359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614359).length < 2 ^ (prefixWord ++ tailWord_1614359).sum := by decide
  have hdescent : baseEnd_1614359 < baseStart_1614359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614384 : List Nat := [2, 1, 1, 1, 2, 3, 3, 8]
def baseStart_1614384 : Nat := 118140960795 + 1614384 * 2 ^ 59
def prefixEnd_1614384 : Nat := 4983230072969 + 3 ^ 40 * 1614384 * 2
def baseEnd_1614384 : Nat := 122808141174535844277865

theorem tailTrace_1614384 : CollatzResearch.WordTrace tailWord_1614384 prefixEnd_1614384 122808141174535844277865 := by
  unfold tailWord_1614384
  simp only [CollatzResearch.WordTrace]
  refine ⟨29440710891684978840765103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39254281188913305121020137 29440710891684978840765103)
  ·
    refine ⟨44161066337527468261147655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29440710891684978840765103 44161066337527468261147655)
    ·
      refine ⟨66241599506291202391721483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44161066337527468261147655 66241599506291202391721483)
      ·
        refine ⟨99362399259436803587582225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66241599506291202391721483 99362399259436803587582225)
        ·
          refine ⟨74521799444577602690686669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99362399259436803587582225 74521799444577602690686669)
          ·
            refine ⟨27945674791716601009007501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74521799444577602690686669 27945674791716601009007501)
            ·
              refine ⟨10479628046893725378377813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27945674791716601009007501 10479628046893725378377813)
              ·
                refine ⟨122808141174535844277865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10479628046893725378377813 122808141174535844277865)
                ·
                  rfl

theorem cell21_1614384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_1614384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614384 prefixEnd_1614384 := by exact prefixLift 1614384
  have htrace : WordTrace (prefixWord ++ tailWord_1614384) baseStart_1614384 baseEnd_1614384 := by
    simpa [prefixWord, tailWord_1614384, baseEnd_1614384] using wordTrace_append hprefix tailTrace_1614384
  have hstable : (prefixWord ++ tailWord_1614384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614384).length < 2 ^ (prefixWord ++ tailWord_1614384).sum := by decide
  have hdescent : baseEnd_1614384 < baseStart_1614384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614401 : List Nat := [1, 2, 5, 1, 1, 2, 2, 7]
def baseStart_1614401 : Nat := 118140960795 + 1614401 * 2 ^ 59
def prefixEnd_1614401 : Nat := 4983230072969 + 3 ^ 40 * 1614401 * 2
def baseEnd_1614401 : Nat := 122809434385073093683409

theorem tailTrace_1614401 : CollatzResearch.WordTrace tailWord_1614401 prefixEnd_1614401 122809434385073093683409 := by
  unfold tailWord_1614401
  simp only [CollatzResearch.WordTrace]
  refine ⟨58882041824308369584899057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39254694549538913056599371 58882041824308369584899057)
  ·
    refine ⟨44161531368231277188674293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58882041824308369584899057 44161531368231277188674293)
    ·
      refine ⟨4140143565771682236438215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44161531368231277188674293 4140143565771682236438215)
      ·
        refine ⟨6210215348657523354657323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140143565771682236438215 6210215348657523354657323)
        ·
          refine ⟨9315323022986285031985985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6210215348657523354657323 9315323022986285031985985)
          ·
            refine ⟨6986492267239713773989489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9315323022986285031985985 6986492267239713773989489)
            ·
              refine ⟨5239869200429785330492117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6986492267239713773989489 5239869200429785330492117)
              ·
                refine ⟨122809434385073093683409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5239869200429785330492117 122809434385073093683409)
                ·
                  rfl

theorem cell21_1614401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 7].length) (baseStart_1614401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614401 prefixEnd_1614401 := by exact prefixLift 1614401
  have htrace : WordTrace (prefixWord ++ tailWord_1614401) baseStart_1614401 baseEnd_1614401 := by
    simpa [prefixWord, tailWord_1614401, baseEnd_1614401] using wordTrace_append hprefix tailTrace_1614401
  have hstable : (prefixWord ++ tailWord_1614401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614401).length < 2 ^ (prefixWord ++ tailWord_1614401).sum := by decide
  have hdescent : baseEnd_1614401 < baseStart_1614401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614460 : List Nat := [2, 2, 2, 1, 1, 2, 2, 9]
def baseStart_1614460 : Nat := 118140960795 + 1614460 * 2 ^ 59
def prefixEnd_1614460 : Nat := 4983230072969 + 3 ^ 40 * 1614460 * 2
def baseEnd_1614460 : Nat := 122813922586349429855591

theorem tailTrace_1614460 : CollatzResearch.WordTrace tailWord_1614460 prefixEnd_1614460 122813922586349429855591 := by
  unfold tailWord_1614460
  simp only [CollatzResearch.WordTrace]
  refine ⟨29442096865547311330648417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39256129154063081774197889 29442096865547311330648417)
  ·
    refine ⟨22081572649160483497986313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29442096865547311330648417 22081572649160483497986313)
    ·
      refine ⟨16561179486870362623489735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22081572649160483497986313 16561179486870362623489735)
      ·
        refine ⟨24841769230305543935234603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16561179486870362623489735 24841769230305543935234603)
        ·
          refine ⟨37262653845458315902851905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24841769230305543935234603 37262653845458315902851905)
          ·
            refine ⟨27946990384093736927138929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37262653845458315902851905 27946990384093736927138929)
            ·
              refine ⟨20960242788070302695354197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27946990384093736927138929 20960242788070302695354197)
              ·
                refine ⟨122813922586349429855591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20960242788070302695354197 122813922586349429855591)
                ·
                  rfl

theorem cell21_1614460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_1614460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614460 prefixEnd_1614460 := by exact prefixLift 1614460
  have htrace : WordTrace (prefixWord ++ tailWord_1614460) baseStart_1614460 baseEnd_1614460 := by
    simpa [prefixWord, tailWord_1614460, baseEnd_1614460] using wordTrace_append hprefix tailTrace_1614460
  have hstable : (prefixWord ++ tailWord_1614460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614460).length < 2 ^ (prefixWord ++ tailWord_1614460).sum := by decide
  have hdescent : baseEnd_1614460 < baseStart_1614460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614505 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 8]
def baseStart_1614505 : Nat := 118140960795 + 1614505 * 2 ^ 59
def prefixEnd_1614505 : Nat := 4983230072969 + 3 ^ 40 * 1614505 * 2
def baseEnd_1614505 : Nat := 368452037372138211316681

theorem tailTrace_1614505 : CollatzResearch.WordTrace tailWord_1614505 prefixEnd_1614505 368452037372138211316681 := by
  unfold tailWord_1614505
  simp only [CollatzResearch.WordTrace]
  refine ⟨58885835015931595346684969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39257223343954396897789979 58885835015931595346684969)
  ·
    refine ⟨44164376261948696510013727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58885835015931595346684969 44164376261948696510013727)
    ·
      refine ⟨66246564392923044765020591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44164376261948696510013727 66246564392923044765020591)
      ·
        refine ⟨99369846589384567147530887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66246564392923044765020591 99369846589384567147530887)
        ·
          refine ⟨149054769884076850721296331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99369846589384567147530887 149054769884076850721296331)
          ·
            refine ⟨223582154826115276081944497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149054769884076850721296331 223582154826115276081944497)
            ·
              refine ⟨167686616119586457061458373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223582154826115276081944497 167686616119586457061458373)
              ·
                refine ⟨31441240522422460699023445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167686616119586457061458373 31441240522422460699023445)
                ·
                  refine ⟨368452037372138211316681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31441240522422460699023445 368452037372138211316681)
                  ·
                    rfl

theorem cell21_1614505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_1614505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614505 prefixEnd_1614505 := by exact prefixLift 1614505
  have htrace : WordTrace (prefixWord ++ tailWord_1614505) baseStart_1614505 baseEnd_1614505 := by
    simpa [prefixWord, tailWord_1614505, baseEnd_1614505] using wordTrace_append hprefix tailTrace_1614505
  have hstable : (prefixWord ++ tailWord_1614505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614505).length < 2 ^ (prefixWord ++ tailWord_1614505).sum := by decide
  have hdescent : baseEnd_1614505 < baseStart_1614505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614525 : List Nat := [1, 4, 1, 2, 1, 3, 3, 3, 3]
def baseStart_1614525 : Nat := 118140960795 + 1614525 * 2 ^ 59
def prefixEnd_1614525 : Nat := 4983230072969 + 3 ^ 40 * 1614525 * 2
def baseEnd_1614525 : Nat := 368456601644622620983307

theorem tailTrace_1614525 : CollatzResearch.WordTrace tailWord_1614525 prefixEnd_1614525 368456601644622620983307 := by
  unfold tailWord_1614525
  simp only [CollatzResearch.WordTrace]
  refine ⟨58886564475859138762413029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39257709650572759174942019 58886564475859138762413029)
  ·
    refine ⟨11041230839223588517952443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58886564475859138762413029 11041230839223588517952443)
    ·
      refine ⟨16561846258835382776928665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11041230839223588517952443 16561846258835382776928665)
      ·
        refine ⟨12421384694126537082696499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16561846258835382776928665 12421384694126537082696499)
        ·
          refine ⟨18632077041189805624044749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12421384694126537082696499 18632077041189805624044749)
          ·
            refine ⟨6987028890446177109016781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18632077041189805624044749 6987028890446177109016781)
            ·
              refine ⟨2620135833917316415881293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6987028890446177109016781 2620135833917316415881293)
              ·
                refine ⟨982550937718993655955485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2620135833917316415881293 982550937718993655955485)
                ·
                  refine ⟨368456601644622620983307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982550937718993655955485 368456601644622620983307)
                  ·
                    rfl

theorem cell21_1614525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_1614525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614525 prefixEnd_1614525 := by exact prefixLift 1614525
  have htrace : WordTrace (prefixWord ++ tailWord_1614525) baseStart_1614525 baseEnd_1614525 := by
    simpa [prefixWord, tailWord_1614525, baseEnd_1614525] using wordTrace_append hprefix tailTrace_1614525
  have hstable : (prefixWord ++ tailWord_1614525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614525).length < 2 ^ (prefixWord ++ tailWord_1614525).sum := by decide
  have hdescent : baseEnd_1614525 < baseStart_1614525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614536 : List Nat := [2, 1, 3, 1, 2, 3, 9]
def baseStart_1614536 : Nat := 118140960795 + 1614536 * 2 ^ 59
def prefixEnd_1614536 : Nat := 4983230072969 + 3 ^ 40 * 1614536 * 2
def baseEnd_1614536 : Nat := 40939901332721005144439

theorem tailTrace_1614536 : CollatzResearch.WordTrace tailWord_1614536 prefixEnd_1614536 40939901332721005144439 := by
  unfold tailWord_1614536
  simp only [CollatzResearch.WordTrace]
  refine ⟨29443482839409643820531731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39257977119212858427375641 29443482839409643820531731)
  ·
    refine ⟨44165224259114465730797597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29443482839409643820531731 44165224259114465730797597)
    ·
      refine ⟨16561959097167924649049099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44165224259114465730797597 16561959097167924649049099)
      ·
        refine ⟨24842938645751886973573649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16561959097167924649049099 24842938645751886973573649)
        ·
          refine ⟨18632203984313915230180237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24842938645751886973573649 18632203984313915230180237)
          ·
            refine ⟨6987076494117718211317589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18632203984313915230180237 6987076494117718211317589)
            ·
              refine ⟨40939901332721005144439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6987076494117718211317589 40939901332721005144439)
              ·
                rfl

theorem cell21_1614536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 9].length) (baseStart_1614536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614536 prefixEnd_1614536 := by exact prefixLift 1614536
  have htrace : WordTrace (prefixWord ++ tailWord_1614536) baseStart_1614536 baseEnd_1614536 := by
    simpa [prefixWord, tailWord_1614536, baseEnd_1614536] using wordTrace_append hprefix tailTrace_1614536
  have hstable : (prefixWord ++ tailWord_1614536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614536).length < 2 ^ (prefixWord ++ tailWord_1614536).sum := by decide
  have hdescent : baseEnd_1614536 < baseStart_1614536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614542 : List Nat := [4, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_1614542 : Nat := 118140960795 + 1614542 * 2 ^ 59
def prefixEnd_1614542 : Nat := 4983230072969 + 3 ^ 40 * 1614542 * 2
def baseEnd_1614542 : Nat := 368460481276234369199939

theorem tailTrace_1614542 : CollatzResearch.WordTrace tailWord_1614542 prefixEnd_1614542 368460481276234369199939 := by
  unfold tailWord_1614542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7360898064599693833222735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39258123011198367110521253 7360898064599693833222735)
  ·
    refine ⟨11041347096899540749834103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7360898064599693833222735 11041347096899540749834103)
    ·
      refine ⟨16562020645349311124751155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11041347096899540749834103 16562020645349311124751155)
      ·
        refine ⟨24843030968023966687126733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16562020645349311124751155 24843030968023966687126733)
        ·
          refine ⟨9316136613008987507672525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24843030968023966687126733 9316136613008987507672525)
          ·
            refine ⟨3493551229878370315377197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9316136613008987507672525 3493551229878370315377197)
            ·
              refine ⟨1310081711204388868266449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3493551229878370315377197 1310081711204388868266449)
              ·
                refine ⟨982561283403291651199837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310081711204388868266449 982561283403291651199837)
                ·
                  refine ⟨368460481276234369199939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982561283403291651199837 368460481276234369199939)
                  ·
                    rfl

theorem cell21_1614542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_1614542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614542 prefixEnd_1614542 := by exact prefixLift 1614542
  have htrace : WordTrace (prefixWord ++ tailWord_1614542) baseStart_1614542 baseEnd_1614542 := by
    simpa [prefixWord, tailWord_1614542, baseEnd_1614542] using wordTrace_append hprefix tailTrace_1614542
  have hstable : (prefixWord ++ tailWord_1614542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614542).length < 2 ^ (prefixWord ++ tailWord_1614542).sum := by decide
  have hdescent : baseEnd_1614542 < baseStart_1614542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614556 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_1614556 : Nat := 118140960795 + 1614556 * 2 ^ 59
def prefixEnd_1614556 : Nat := 4983230072969 + 3 ^ 40 * 1614556 * 2
def baseEnd_1614556 : Nat := 368463676266973455966577

theorem tailTrace_1614556 : CollatzResearch.WordTrace tailWord_1614556 prefixEnd_1614556 368463676266973455966577 := by
  unfold tailWord_1614556
  simp only [CollatzResearch.WordTrace]
  refine ⟨29443847569373415528395761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39258463425831220704527681 29443847569373415528395761)
  ·
    refine ⟨22082885677030061646296821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29443847569373415528395761 22082885677030061646296821)
    ·
      refine ⟨2070270532221568279340327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22082885677030061646296821 2070270532221568279340327)
      ·
        refine ⟨3105405798332352419010491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070270532221568279340327 3105405798332352419010491)
        ·
          refine ⟨4658108697498528628515737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105405798332352419010491 4658108697498528628515737)
          ·
            refine ⟨3493581523123896471386803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4658108697498528628515737 3493581523123896471386803)
            ·
              refine ⟨5240372284685844707080205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493581523123896471386803 5240372284685844707080205)
              ·
                refine ⟨1965139606757191765155077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5240372284685844707080205 1965139606757191765155077)
                ·
                  refine ⟨368463676266973455966577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1965139606757191765155077 368463676266973455966577)
                  ·
                    rfl

theorem cell21_1614556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_1614556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614556 prefixEnd_1614556 := by exact prefixLift 1614556
  have htrace : WordTrace (prefixWord ++ tailWord_1614556) baseStart_1614556 baseEnd_1614556 := by
    simpa [prefixWord, tailWord_1614556, baseEnd_1614556] using wordTrace_append hprefix tailTrace_1614556
  have hstable : (prefixWord ++ tailWord_1614556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614556).length < 2 ^ (prefixWord ++ tailWord_1614556).sum := by decide
  have hdescent : baseEnd_1614556 < baseStart_1614556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614584 : List Nat := [2, 1, 2, 1, 1, 2, 4, 5, 3]
def baseStart_1614584 : Nat := 118140960795 + 1614584 * 2 ^ 59
def prefixEnd_1614584 : Nat := 4983230072969 + 3 ^ 40 * 1614584 * 2
def baseEnd_1614584 : Nat := 368470066248451629499853

theorem tailTrace_1614584 : CollatzResearch.WordTrace tailWord_1614584 prefixEnd_1614584 368470066248451629499853 := by
  unfold tailWord_1614584
  simp only [CollatzResearch.WordTrace]
  refine ⟨29444358191322695919405403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39259144255096927892540537 29444358191322695919405403)
  ·
    refine ⟨44166537286984043879108105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29444358191322695919405403 44166537286984043879108105)
    ·
      refine ⟨33124902965238032909331079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44166537286984043879108105 33124902965238032909331079)
      ·
        refine ⟨49687354447857049363996619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33124902965238032909331079 49687354447857049363996619)
        ·
          refine ⟨74531031671785574045994929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49687354447857049363996619 74531031671785574045994929)
          ·
            refine ⟨55898273753839180534496197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74531031671785574045994929 55898273753839180534496197)
            ·
              refine ⟨10480926328844846350218037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55898273753839180534496197 10480926328844846350218037)
              ·
                refine ⟨982586843329204345332941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10480926328844846350218037 982586843329204345332941)
                ·
                  refine ⟨368470066248451629499853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982586843329204345332941 368470066248451629499853)
                  ·
                    rfl

theorem cell21_1614584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 3].length) (baseStart_1614584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614584 prefixEnd_1614584 := by exact prefixLift 1614584
  have htrace : WordTrace (prefixWord ++ tailWord_1614584) baseStart_1614584 baseEnd_1614584 := by
    simpa [prefixWord, tailWord_1614584, baseEnd_1614584] using wordTrace_append hprefix tailTrace_1614584
  have hstable : (prefixWord ++ tailWord_1614584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614584).length < 2 ^ (prefixWord ++ tailWord_1614584).sum := by decide
  have hdescent : baseEnd_1614584 < baseStart_1614584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614601 : List Nat := [1, 2, 1, 1, 3, 2, 6, 2, 3]
def baseStart_1614601 : Nat := 118140960795 + 1614601 * 2 ^ 59
def prefixEnd_1614601 : Nat := 4983230072969 + 3 ^ 40 * 1614601 * 2
def baseEnd_1614601 : Nat := 368473945880063377716485

theorem tailTrace_1614601 : CollatzResearch.WordTrace tailWord_1614601 prefixEnd_1614601 368473945880063377716485 := by
  unfold tailWord_1614601
  simp only [CollatzResearch.WordTrace]
  refine ⟨58889336423583803742179657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39259557615722535828119771 58889336423583803742179657)
  ·
    refine ⟨44167002317687852806634743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58889336423583803742179657 44167002317687852806634743)
    ·
      refine ⟨66250503476531779209952115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44167002317687852806634743 66250503476531779209952115)
      ·
        refine ⟨99375755214797668814928173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66250503476531779209952115 99375755214797668814928173)
        ·
          refine ⟨37265908205549125805598065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99375755214797668814928173 37265908205549125805598065)
          ·
            refine ⟨27949431154161844354198549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37265908205549125805598065 27949431154161844354198549)
            ·
              refine ⟨1310129585351336454103057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27949431154161844354198549 1310129585351336454103057)
              ·
                refine ⟨982597189013502340577293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310129585351336454103057 982597189013502340577293)
                ·
                  refine ⟨368473945880063377716485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982597189013502340577293 368473945880063377716485)
                  ·
                    rfl

theorem cell21_1614601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 3].length) (baseStart_1614601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614601 prefixEnd_1614601 := by exact prefixLift 1614601
  have htrace : WordTrace (prefixWord ++ tailWord_1614601) baseStart_1614601 baseEnd_1614601 := by
    simpa [prefixWord, tailWord_1614601, baseEnd_1614601] using wordTrace_append hprefix tailTrace_1614601
  have hstable : (prefixWord ++ tailWord_1614601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614601).length < 2 ^ (prefixWord ++ tailWord_1614601).sum := by decide
  have hdescent : baseEnd_1614601 < baseStart_1614601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614629 : List Nat := [1, 3, 1, 2, 3, 1, 5, 5]
def baseStart_1614629 : Nat := 118140960795 + 1614629 * 2 ^ 59
def prefixEnd_1614629 : Nat := 4983230072969 + 3 ^ 40 * 1614629 * 2
def baseEnd_1614629 : Nat := 122826778620513850416587

theorem tailTrace_1614629 : CollatzResearch.WordTrace tailWord_1614629 prefixEnd_1614629 122826778620513850416587 := by
  unfold tailWord_1614629
  simp only [CollatzResearch.WordTrace]
  refine ⟨58890357667482364524198941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39260238444988243016132627 58890357667482364524198941)
  ·
    refine ⟨22083884125305886696574603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58890357667482364524198941 22083884125305886696574603)
    ·
      refine ⟨33125826187958830044861905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22083884125305886696574603 33125826187958830044861905)
      ·
        refine ⟨24844369640969122533646429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33125826187958830044861905 24844369640969122533646429)
        ·
          refine ⟨9316638615363420950117411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24844369640969122533646429 9316638615363420950117411)
          ·
            refine ⟨13974957923045131425176117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9316638615363420950117411 13974957923045131425176117)
            ·
              refine ⟨1310152305285481071110261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13974957923045131425176117 1310152305285481071110261)
              ·
                refine ⟨122826778620513850416587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1310152305285481071110261 122826778620513850416587)
                ·
                  rfl

theorem cell21_1614629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 5].length) (baseStart_1614629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614629 prefixEnd_1614629 := by exact prefixLift 1614629
  have htrace : WordTrace (prefixWord ++ tailWord_1614629) baseStart_1614629 baseEnd_1614629 := by
    simpa [prefixWord, tailWord_1614629, baseEnd_1614629] using wordTrace_append hprefix tailTrace_1614629
  have hstable : (prefixWord ++ tailWord_1614629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614629).length < 2 ^ (prefixWord ++ tailWord_1614629).sum := by decide
  have hdescent : baseEnd_1614629 < baseStart_1614629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614646 : List Nat := [5, 1, 2, 2, 2, 1, 8]
def baseStart_1614646 : Nat := 118140960795 + 1614646 * 2 ^ 59
def prefixEnd_1614646 : Nat := 4983230072969 + 3 ^ 40 * 1614646 * 2
def baseEnd_1614646 : Nat := 40942690610350366607377

theorem tailTrace_1614646 : CollatzResearch.WordTrace tailWord_1614646 prefixEnd_1614646 40942690610350366607377 := by
  unfold tailWord_1614646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680686106776298526722987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39260651805613850951711861 3680686106776298526722987)
  ·
    refine ⟨5521029160164447790084481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3680686106776298526722987 5521029160164447790084481)
    ·
      refine ⟨4140771870123335842563361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5521029160164447790084481 4140771870123335842563361)
      ·
        refine ⟨3105578902592501881922521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4140771870123335842563361 3105578902592501881922521)
        ·
          refine ⟨2329184176944376411441891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3105578902592501881922521 2329184176944376411441891)
          ·
            refine ⟨3493776265416564617162837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329184176944376411441891 3493776265416564617162837)
            ·
              refine ⟨40942690610350366607377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3493776265416564617162837 40942690610350366607377)
              ·
                rfl

theorem cell21_1614646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 8].length) (baseStart_1614646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614646 prefixEnd_1614646 := by exact prefixLift 1614646
  have htrace : WordTrace (prefixWord ++ tailWord_1614646) baseStart_1614646 baseEnd_1614646 := by
    simpa [prefixWord, tailWord_1614646, baseEnd_1614646] using wordTrace_append hprefix tailTrace_1614646
  have hstable : (prefixWord ++ tailWord_1614646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614646).length < 2 ^ (prefixWord ++ tailWord_1614646).sum := by decide
  have hdescent : baseEnd_1614646 < baseStart_1614646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614688 : List Nat := [2, 1, 1, 3, 3, 1, 3, 7]
def baseStart_1614688 : Nat := 118140960795 + 1614688 * 2 ^ 59
def prefixEnd_1614688 : Nat := 4983230072969 + 3 ^ 40 * 1614688 * 2
def baseEnd_1614688 : Nat := 122831266821790186588769

theorem tailTrace_1614688 : CollatzResearch.WordTrace tailWord_1614688 prefixEnd_1614688 122831266821790186588769 := by
  unfold tailWord_1614688
  simp only [CollatzResearch.WordTrace]
  refine ⟨29446254787134308800298359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39261673049512411733731145 29446254787134308800298359)
  ·
    refine ⟨44169382180701463200447539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29446254787134308800298359 44169382180701463200447539)
    ·
      refine ⟨66254073271052194800671309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44169382180701463200447539 66254073271052194800671309)
      ·
        refine ⟨24845277476644573050251741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66254073271052194800671309 24845277476644573050251741)
        ·
          refine ⟨9316979053741714893844403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24845277476644573050251741 9316979053741714893844403)
          ·
            refine ⟨13975468580612572340766605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9316979053741714893844403 13975468580612572340766605)
            ·
              refine ⟨5240800717729714627787477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13975468580612572340766605 5240800717729714627787477)
              ·
                refine ⟨122831266821790186588769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5240800717729714627787477 122831266821790186588769)
                ·
                  rfl

theorem cell21_1614688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_1614688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614688 prefixEnd_1614688 := by exact prefixLift 1614688
  have htrace : WordTrace (prefixWord ++ tailWord_1614688) baseStart_1614688 baseEnd_1614688 := by
    simpa [prefixWord, tailWord_1614688, baseEnd_1614688] using wordTrace_append hprefix tailTrace_1614688
  have hstable : (prefixWord ++ tailWord_1614688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614688).length < 2 ^ (prefixWord ++ tailWord_1614688).sum := by decide
  have hdescent : baseEnd_1614688 < baseStart_1614688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614719 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 5]
def baseStart_1614719 : Nat := 118140960795 + 1614719 * 2 ^ 59
def prefixEnd_1614719 : Nat := 4983230072969 + 3 ^ 40 * 1614719 * 2
def baseEnd_1614719 : Nat := 368500875087721394749577

theorem tailTrace_1614719 : CollatzResearch.WordTrace tailWord_1614719 prefixEnd_1614719 368500875087721394749577 := by
  unfold tailWord_1614719
  simp only [CollatzResearch.WordTrace]
  refine ⟨58893640237156309894975211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39262426824770873263316807 58893640237156309894975211)
  ·
    refine ⟨88340460355734464842462817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58893640237156309894975211 88340460355734464842462817)
    ·
      refine ⟨66255345266800848631847113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88340460355734464842462817 66255345266800848631847113)
      ·
        refine ⟨49691508950100636473885335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66255345266800848631847113 49691508950100636473885335)
        ·
          refine ⟨74537263425150954710828003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49691508950100636473885335 74537263425150954710828003)
          ·
            refine ⟨111805895137726432066242005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74537263425150954710828003 111805895137726432066242005)
            ·
              refine ⟨2620450667290463251552547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 111805895137726432066242005 2620450667290463251552547)
              ·
                refine ⟨3930676000935694877328821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620450667290463251552547 3930676000935694877328821)
                ·
                  refine ⟨368500875087721394749577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3930676000935694877328821 368500875087721394749577)
                  ·
                    rfl

theorem cell21_1614719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 5].length) (baseStart_1614719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614719 prefixEnd_1614719 := by exact prefixLift 1614719
  have htrace : WordTrace (prefixWord ++ tailWord_1614719) baseStart_1614719 baseEnd_1614719 := by
    simpa [prefixWord, tailWord_1614719, baseEnd_1614719] using wordTrace_append hprefix tailTrace_1614719
  have hstable : (prefixWord ++ tailWord_1614719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614719).length < 2 ^ (prefixWord ++ tailWord_1614719).sum := by decide
  have hdescent : baseEnd_1614719 < baseStart_1614719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614795 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 5]
def baseStart_1614795 : Nat := 118140960795 + 1614795 * 2 ^ 59
def prefixEnd_1614795 : Nat := 4983230072969 + 3 ^ 40 * 1614795 * 2
def baseEnd_1614795 : Nat := 368518219323162151482755

theorem tailTrace_1614795 : CollatzResearch.WordTrace tailWord_1614795 prefixEnd_1614795 368518219323162151482755 := by
  unfold tailWord_1614795
  simp only [CollatzResearch.WordTrace]
  refine ⟨58896412184880974874741839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39264274789920649916494559 58896412184880974874741839)
  ·
    refine ⟨88344618277321462312112759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58896412184880974874741839 88344618277321462312112759)
    ·
      refine ⟨132516927415982193468169139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88344618277321462312112759 132516927415982193468169139)
      ·
        refine ⟨198775391123973290202253709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132516927415982193468169139 198775391123973290202253709)
        ·
          refine ⟨74540771671489983825845141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198775391123973290202253709 74540771671489983825845141)
          ·
            refine ⟨3494098672101092991836491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74540771671489983825845141 3494098672101092991836491)
            ·
              refine ⟨5241148008151639487754737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494098672101092991836491 5241148008151639487754737)
              ·
                refine ⟨3930861006113729615816053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5241148008151639487754737 3930861006113729615816053)
                ·
                  refine ⟨368518219323162151482755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3930861006113729615816053 368518219323162151482755)
                  ·
                    rfl

theorem cell21_1614795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 5].length) (baseStart_1614795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614795 prefixEnd_1614795 := by exact prefixLift 1614795
  have htrace : WordTrace (prefixWord ++ tailWord_1614795) baseStart_1614795 baseEnd_1614795 := by
    simpa [prefixWord, tailWord_1614795, baseEnd_1614795] using wordTrace_append hprefix tailTrace_1614795
  have hstable : (prefixWord ++ tailWord_1614795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614795).length < 2 ^ (prefixWord ++ tailWord_1614795).sum := by decide
  have hdescent : baseEnd_1614795 < baseStart_1614795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614826 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_1614826 : Nat := 118140960795 + 1614826 * 2 ^ 59
def prefixEnd_1614826 : Nat := 4983230072969 + 3 ^ 40 * 1614826 * 2
def baseEnd_1614826 : Nat := 368525293945512986466025

theorem tailTrace_1614826 : CollatzResearch.WordTrace tailWord_1614826 prefixEnd_1614826 368525293945512986466025 := by
  unfold tailWord_1614826
  simp only [CollatzResearch.WordTrace]
  refine ⟨14724385711942166792280083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39265028565179111446080221 14724385711942166792280083)
  ·
    refine ⟨22086578567913250188420125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14724385711942166792280083 22086578567913250188420125)
    ·
      refine ⟨8282466962967468820657547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22086578567913250188420125 8282466962967468820657547)
      ·
        refine ⟨12423700444451203230986321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8282466962967468820657547 12423700444451203230986321)
        ·
          refine ⟨9317775333338402423239741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12423700444451203230986321 9317775333338402423239741)
          ·
            refine ⟨3494165750001900908714903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9317775333338402423239741 3494165750001900908714903)
            ·
              refine ⟨5241248625002851363072355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494165750001900908714903 5241248625002851363072355)
              ·
                refine ⟨7861872937504277044608533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241248625002851363072355 7861872937504277044608533)
                ·
                  refine ⟨368525293945512986466025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7861872937504277044608533 368525293945512986466025)
                  ·
                    rfl

theorem cell21_1614826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_1614826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614826 prefixEnd_1614826 := by exact prefixLift 1614826
  have htrace : WordTrace (prefixWord ++ tailWord_1614826) baseStart_1614826 baseEnd_1614826 := by
    simpa [prefixWord, tailWord_1614826, baseEnd_1614826] using wordTrace_append hprefix tailTrace_1614826
  have hstable : (prefixWord ++ tailWord_1614826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614826).length < 2 ^ (prefixWord ++ tailWord_1614826).sum := by decide
  have hdescent : baseEnd_1614826 < baseStart_1614826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614885 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 6]
def baseStart_1614885 : Nat := 118140960795 + 1614885 * 2 ^ 59
def prefixEnd_1614885 : Nat := 4983230072969 + 3 ^ 40 * 1614885 * 2
def baseEnd_1614885 : Nat := 368538758549341994982571

theorem tailTrace_1614885 : CollatzResearch.WordTrace tailWord_1614885 prefixEnd_1614885 368538758549341994982571 := by
  unfold tailWord_1614885
  simp only [CollatzResearch.WordTrace]
  refine ⟨58899694754554920245518109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39266463169703280163678739 58899694754554920245518109)
  ·
    refine ⟨22087385532958095092069291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58899694754554920245518109 22087385532958095092069291)
    ·
      refine ⟨33131078299437142638103937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22087385532958095092069291 33131078299437142638103937)
      ·
        refine ⟨24848308724577856978577953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33131078299437142638103937 24848308724577856978577953)
        ·
          refine ⟨18636231543433392733933465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24848308724577856978577953 18636231543433392733933465)
          ·
            refine ⟨13977173657575044550450099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18636231543433392733933465 13977173657575044550450099)
            ·
              refine ⟨20965760486362566825675149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13977173657575044550450099 20965760486362566825675149)
              ·
                refine ⟨7862160182385962559628181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20965760486362566825675149 7862160182385962559628181)
                ·
                  refine ⟨368538758549341994982571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7862160182385962559628181 368538758549341994982571)
                  ·
                    rfl

theorem cell21_1614885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_1614885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614885 prefixEnd_1614885 := by exact prefixLift 1614885
  have htrace : WordTrace (prefixWord ++ tailWord_1614885) baseStart_1614885 baseEnd_1614885 := by
    simpa [prefixWord, tailWord_1614885, baseEnd_1614885] using wordTrace_append hprefix tailTrace_1614885
  have hstable : (prefixWord ++ tailWord_1614885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614885).length < 2 ^ (prefixWord ++ tailWord_1614885).sum := by decide
  have hdescent : baseEnd_1614885 < baseStart_1614885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614981 : List Nat := [1, 3, 1, 1, 6, 1, 2, 3, 3]
def baseStart_1614981 : Nat := 118140960795 + 1614981 * 2 ^ 59
def prefixEnd_1614981 : Nat := 4983230072969 + 3 ^ 40 * 1614981 * 2
def baseEnd_1614981 : Nat := 368560667057267161382375

theorem tailTrace_1614981 : CollatzResearch.WordTrace tailWord_1614981 prefixEnd_1614981 368560667057267161382375 := by
  unfold tailWord_1614981
  simp only [CollatzResearch.WordTrace]
  refine ⟨58903196162207128641012797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39268797441471419094008531 58903196162207128641012797)
  ·
    refine ⟨22088698560827673240379799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58903196162207128641012797 22088698560827673240379799)
    ·
      refine ⟨33133047841241509860569699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22088698560827673240379799 33133047841241509860569699)
      ·
        refine ⟨49699571761862264790854549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33133047841241509860569699 49699571761862264790854549)
        ·
          refine ⟨2329667426337293662071307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49699571761862264790854549 2329667426337293662071307)
          ·
            refine ⟨3494501139505940493106961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329667426337293662071307 3494501139505940493106961)
            ·
              refine ⟨2620875854629455369830221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494501139505940493106961 2620875854629455369830221)
              ·
                refine ⟨982828445486045763686333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2620875854629455369830221 982828445486045763686333)
                ·
                  refine ⟨368560667057267161382375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982828445486045763686333 368560667057267161382375)
                  ·
                    rfl

theorem cell21_1614981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_1614981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1614981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1614981 prefixEnd_1614981 := by exact prefixLift 1614981
  have htrace : WordTrace (prefixWord ++ tailWord_1614981) baseStart_1614981 baseEnd_1614981 := by
    simpa [prefixWord, tailWord_1614981, baseEnd_1614981] using wordTrace_append hprefix tailTrace_1614981
  have hstable : (prefixWord ++ tailWord_1614981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614981).length < 2 ^ (prefixWord ++ tailWord_1614981).sum := by decide
  have hdescent : baseEnd_1614981 < baseStart_1614981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615037 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1615037 : Nat := 118140960795 + 1615037 * 2 ^ 59
def prefixEnd_1615037 : Nat := 4983230072969 + 3 ^ 40 * 1615037 * 2
def baseEnd_1615037 : Nat := 368573447020223508448927

theorem tailTrace_1615037 : CollatzResearch.WordTrace tailWord_1615037 prefixEnd_1615037 368573447020223508448927 := by
  unfold tailWord_1615037
  simp only [CollatzResearch.WordTrace]
  refine ⟨58905238650004250205051365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39270159100002833470034243 58905238650004250205051365)
  ·
    refine ⟨11044732246875796913447131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58905238650004250205051365 11044732246875796913447131)
    ·
      refine ⟨16567098370313695370170697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11044732246875796913447131 16567098370313695370170697)
      ·
        refine ⟨12425323777735271527628023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16567098370313695370170697 12425323777735271527628023)
        ·
          refine ⟨18637985666602907291442035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12425323777735271527628023 18637985666602907291442035)
          ·
            refine ⟨27956978499904360937163053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18637985666602907291442035 27956978499904360937163053)
            ·
              refine ⟨10483866937464135351436145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27956978499904360937163053 10483866937464135351436145)
              ·
                refine ⟨7862900203098101513577109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10483866937464135351436145 7862900203098101513577109)
                ·
                  refine ⟨368573447020223508448927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7862900203098101513577109 368573447020223508448927)
                  ·
                    rfl

theorem cell21_1615037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1615037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615037 prefixEnd_1615037 := by exact prefixLift 1615037
  have htrace : WordTrace (prefixWord ++ tailWord_1615037) baseStart_1615037 baseEnd_1615037 := by
    simpa [prefixWord, tailWord_1615037, baseEnd_1615037] using wordTrace_append hprefix tailTrace_1615037
  have hstable : (prefixWord ++ tailWord_1615037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615037).length < 2 ^ (prefixWord ++ tailWord_1615037).sum := by decide
  have hdescent : baseEnd_1615037 < baseStart_1615037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615116 : List Nat := [2, 2, 1, 2, 2, 4, 1, 4, 3]
def baseStart_1615116 : Nat := 118140960795 + 1615116 * 2 ^ 59
def prefixEnd_1615116 : Nat := 4983230072969 + 3 ^ 40 * 1615116 * 2
def baseEnd_1615116 : Nat := 368591475896536926632099

theorem tailTrace_1615116 : CollatzResearch.WordTrace tailWord_1615116 prefixEnd_1615116 368591475896536926632099 := by
  unfold tailWord_1615116
  simp only [CollatzResearch.WordTrace]
  refine ⟨29454060008359023348588601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39272080011145364464784801 29454060008359023348588601)
  ·
    refine ⟨22090545006269267511441451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29454060008359023348588601 22090545006269267511441451)
    ·
      refine ⟨33135817509403901267162177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22090545006269267511441451 33135817509403901267162177)
      ·
        refine ⟨24851863132052925950371633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33135817509403901267162177 24851863132052925950371633)
        ·
          refine ⟨18638897349039694462778725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24851863132052925950371633 18638897349039694462778725)
          ·
            refine ⟨3494793252944942711771011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18638897349039694462778725 3494793252944942711771011)
            ·
              refine ⟨5242189879417414067656517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494793252944942711771011 5242189879417414067656517)
              ·
                refine ⟨982910602390765137685597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5242189879417414067656517 982910602390765137685597)
                ·
                  refine ⟨368591475896536926632099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982910602390765137685597 368591475896536926632099)
                  ·
                    rfl

theorem cell21_1615116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_1615116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615116 prefixEnd_1615116 := by exact prefixLift 1615116
  have htrace : WordTrace (prefixWord ++ tailWord_1615116) baseStart_1615116 baseEnd_1615116 := by
    simpa [prefixWord, tailWord_1615116, baseEnd_1615116] using wordTrace_append hprefix tailTrace_1615116
  have hstable : (prefixWord ++ tailWord_1615116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615116).length < 2 ^ (prefixWord ++ tailWord_1615116).sum := by decide
  have hdescent : baseEnd_1615116 < baseStart_1615116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615130 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_1615130 : Nat := 118140960795 + 1615130 * 2 ^ 59
def prefixEnd_1615130 : Nat := 4983230072969 + 3 ^ 40 * 1615130 * 2
def baseEnd_1615130 : Nat := 368594670887276013398737

theorem tailTrace_1615130 : CollatzResearch.WordTrace tailWord_1615130 prefixEnd_1615130 368594670887276013398737 := by
  unfold tailWord_1615130
  simp only [CollatzResearch.WordTrace]
  refine ⟨14727157659666831772046711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39272420425778218058791229 14727157659666831772046711)
  ·
    refine ⟨22090736489500247658070067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14727157659666831772046711 22090736489500247658070067)
    ·
      refine ⟨33136104734250371487105101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22090736489500247658070067 33136104734250371487105101)
      ·
        refine ⟨12426039275343889307664413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33136104734250371487105101 12426039275343889307664413)
        ·
          refine ⟨4659764728253958490374155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12426039275343889307664413 4659764728253958490374155)
          ·
            refine ⟨6989647092380937735561233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659764728253958490374155 6989647092380937735561233)
            ·
              refine ⟨5242235319285703301670925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6989647092380937735561233 5242235319285703301670925)
              ·
                refine ⟨1965838244732138738126597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5242235319285703301670925 1965838244732138738126597)
                ·
                  refine ⟨368594670887276013398737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1965838244732138738126597 368594670887276013398737)
                  ·
                    rfl

theorem cell21_1615130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_1615130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615130 prefixEnd_1615130 := by exact prefixLift 1615130
  have htrace : WordTrace (prefixWord ++ tailWord_1615130) baseStart_1615130 baseEnd_1615130 := by
    simpa [prefixWord, tailWord_1615130, baseEnd_1615130] using wordTrace_append hprefix tailTrace_1615130
  have hstable : (prefixWord ++ tailWord_1615130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615130).length < 2 ^ (prefixWord ++ tailWord_1615130).sum := by decide
  have hdescent : baseEnd_1615130 < baseStart_1615130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615175 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 5]
def baseStart_1615175 : Nat := 118140960795 + 1615175 * 2 ^ 59
def prefixEnd_1615175 : Nat := 4983230072969 + 3 ^ 40 * 1615175 * 2
def baseEnd_1615175 : Nat := 368604940500365935148645

theorem tailTrace_1615175 : CollatzResearch.WordTrace tailWord_1615175 prefixEnd_1615175 368604940500365935148645 := by
  unfold tailWord_1615175
  simp only [CollatzResearch.WordTrace]
  refine ⟨58910271923504299773574979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39273514615669533182383319 58910271923504299773574979)
  ·
    refine ⟨88365407885256449660362469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58910271923504299773574979 88365407885256449660362469)
    ·
      refine ⟨16568513978485584311317963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88365407885256449660362469 16568513978485584311317963)
      ·
        refine ⟨24852770967728376466976945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16568513978485584311317963 24852770967728376466976945)
        ·
          refine ⟨18639578225796282350232709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24852770967728376466976945 18639578225796282350232709)
          ·
            refine ⟨3494920917336802940668633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18639578225796282350232709 3494920917336802940668633)
            ·
              refine ⟨2621190688002602205501475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494920917336802940668633 2621190688002602205501475)
              ·
                refine ⟨3931786032003903308252213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621190688002602205501475 3931786032003903308252213)
                ·
                  refine ⟨368604940500365935148645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3931786032003903308252213 368604940500365935148645)
                  ·
                    rfl

theorem cell21_1615175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 5].length) (baseStart_1615175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615175 prefixEnd_1615175 := by exact prefixLift 1615175
  have htrace : WordTrace (prefixWord ++ tailWord_1615175) baseStart_1615175 baseEnd_1615175 := by
    simpa [prefixWord, tailWord_1615175, baseEnd_1615175] using wordTrace_append hprefix tailTrace_1615175
  have hstable : (prefixWord ++ tailWord_1615175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615175).length < 2 ^ (prefixWord ++ tailWord_1615175).sum := by decide
  have hdescent : baseEnd_1615175 < baseStart_1615175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615181 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1615181 : Nat := 118140960795 + 1615181 * 2 ^ 59
def prefixEnd_1615181 : Nat := 4983230072969 + 3 ^ 40 * 1615181 * 2
def baseEnd_1615181 : Nat := 368606309782111258048633

theorem tailTrace_1615181 : CollatzResearch.WordTrace tailWord_1615181 prefixEnd_1615181 368606309782111258048633 := by
  unfold tailWord_1615181
  simp only [CollatzResearch.WordTrace]
  refine ⟨58910490761482562798293397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39273660507655041865528931 58910490761482562798293397)
  ·
    refine ⟨2761429254444495131170003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58910490761482562798293397 2761429254444495131170003)
    ·
      refine ⟨4142143881666742696755005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2761429254444495131170003 4142143881666742696755005)
      ·
        refine ⟨1553303955625028511283127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4142143881666742696755005 1553303955625028511283127)
        ·
          refine ⟨2329955933437542766924691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553303955625028511283127 2329955933437542766924691)
          ·
            refine ⟨3494933900156314150387037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329955933437542766924691 3494933900156314150387037)
            ·
              refine ⟨1310600212558617806395139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3494933900156314150387037 1310600212558617806395139)
              ·
                refine ⟨1965900318837926709592709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310600212558617806395139 1965900318837926709592709)
                ·
                  refine ⟨368606309782111258048633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1965900318837926709592709 368606309782111258048633)
                  ·
                    rfl

theorem cell21_1615181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1615181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615181 prefixEnd_1615181 := by exact prefixLift 1615181
  have htrace : WordTrace (prefixWord ++ tailWord_1615181) baseStart_1615181 baseEnd_1615181 := by
    simpa [prefixWord, tailWord_1615181, baseEnd_1615181] using wordTrace_append hprefix tailTrace_1615181
  have hstable : (prefixWord ++ tailWord_1615181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615181).length < 2 ^ (prefixWord ++ tailWord_1615181).sum := by decide
  have hdescent : baseEnd_1615181 < baseStart_1615181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615285 : List Nat := [1, 3, 3, 2, 2, 1, 4, 2, 3]
def baseStart_1615285 : Nat := 118140960795 + 1615285 * 2 ^ 59
def prefixEnd_1615285 : Nat := 4983230072969 + 3 ^ 40 * 1615285 * 2
def baseEnd_1615285 : Nat := 368630043999030188315087

theorem tailTrace_1615285 : CollatzResearch.WordTrace tailWord_1615285 prefixEnd_1615285 368630043999030188315087 := by
  unfold tailWord_1615285
  simp only [CollatzResearch.WordTrace]
  refine ⟨58914283953105788560079309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39276189302070525706719539 58914283953105788560079309)
  ·
    refine ⟨22092856482414670710029741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58914283953105788560079309 22092856482414670710029741)
    ·
      refine ⟨8284821180905501516261153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22092856482414670710029741 8284821180905501516261153)
      ·
        refine ⟨6213615885679126137195865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8284821180905501516261153 6213615885679126137195865)
        ·
          refine ⟨4660211914259344602896899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6213615885679126137195865 4660211914259344602896899)
          ·
            refine ⟨6990317871389016904345349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660211914259344602896899 6990317871389016904345349)
            ·
              refine ⟨1310684600885440669564753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6990317871389016904345349 1310684600885440669564753)
              ·
                refine ⟨983013450664080502173565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310684600885440669564753 983013450664080502173565)
                ·
                  refine ⟨368630043999030188315087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983013450664080502173565 368630043999030188315087)
                  ·
                    rfl

theorem cell21_1615285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_1615285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615285 prefixEnd_1615285 := by exact prefixLift 1615285
  have htrace : WordTrace (prefixWord ++ tailWord_1615285) baseStart_1615285 baseEnd_1615285 := by
    simpa [prefixWord, tailWord_1615285, baseEnd_1615285] using wordTrace_append hprefix tailTrace_1615285
  have hstable : (prefixWord ++ tailWord_1615285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615285).length < 2 ^ (prefixWord ++ tailWord_1615285).sum := by decide
  have hdescent : baseEnd_1615285 < baseStart_1615285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615310 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_1615310 : Nat := 118140960795 + 1615310 * 2 ^ 59
def prefixEnd_1615310 : Nat := 4983230072969 + 3 ^ 40 * 1615310 * 2
def baseEnd_1615310 : Nat := 368635749339635700398369

theorem tailTrace_1615310 : CollatzResearch.WordTrace tailWord_1615310 prefixEnd_1615310 368635749339635700398369 := by
  unfold tailWord_1615310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7364399472251902228717423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39276797185343478553159589 7364399472251902228717423)
  ·
    refine ⟨11046599208377853343076135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7364399472251902228717423 11046599208377853343076135)
    ·
      refine ⟨16569898812566780014614203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11046599208377853343076135 16569898812566780014614203)
      ·
        refine ⟨24854848218850170021921305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16569898812566780014614203 24854848218850170021921305)
        ·
          refine ⟨18641136164137627516440979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24854848218850170021921305 18641136164137627516440979)
          ·
            refine ⟨27961704246206441274661469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18641136164137627516440979 27961704246206441274661469)
            ·
              refine ⟨10485639092327415477998051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27961704246206441274661469 10485639092327415477998051)
              ·
                refine ⟨15728458638491123216997077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10485639092327415477998051 15728458638491123216997077)
                ·
                  refine ⟨368635749339635700398369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15728458638491123216997077 368635749339635700398369)
                  ·
                    rfl

theorem cell21_1615310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_1615310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615310 prefixEnd_1615310 := by exact prefixLift 1615310
  have htrace : WordTrace (prefixWord ++ tailWord_1615310) baseStart_1615310 baseEnd_1615310 := by
    simpa [prefixWord, tailWord_1615310, baseEnd_1615310] using wordTrace_append hprefix tailTrace_1615310
  have hstable : (prefixWord ++ tailWord_1615310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615310).length < 2 ^ (prefixWord ++ tailWord_1615310).sum := by decide
  have hdescent : baseEnd_1615310 < baseStart_1615310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615372 : List Nat := [2, 2, 1, 2, 5, 1, 1, 7]
def baseStart_1615372 : Nat := 118140960795 + 1615372 * 2 ^ 59
def prefixEnd_1615372 : Nat := 4983230072969 + 3 ^ 40 * 1615372 * 2
def baseEnd_1615372 : Nat := 122883299528112456788303

theorem tailTrace_1615372 : CollatzResearch.WordTrace tailWord_1615372 prefixEnd_1615372 122883299528112456788303 := by
  unfold tailWord_1615372
  simp only [CollatzResearch.WordTrace]
  refine ⟨29458728551895301209248185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39278304735860401612330913 29458728551895301209248185)
  ·
    refine ⟨22094046413921475906936139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29458728551895301209248185 22094046413921475906936139)
    ·
      refine ⟨33141069620882213860404209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22094046413921475906936139 33141069620882213860404209)
      ·
        refine ⟨24855802215661660395303157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33141069620882213860404209 24855802215661660395303157)
        ·
          refine ⟨2330231457718280662059671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24855802215661660395303157 2330231457718280662059671)
          ·
            refine ⟨3495347186577420993089507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330231457718280662059671 3495347186577420993089507)
            ·
              refine ⟨5243020779866131489634261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495347186577420993089507 5243020779866131489634261)
              ·
                refine ⟨122883299528112456788303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5243020779866131489634261 122883299528112456788303)
                ·
                  rfl

theorem cell21_1615372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_1615372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615372 prefixEnd_1615372 := by exact prefixLift 1615372
  have htrace : WordTrace (prefixWord ++ tailWord_1615372) baseStart_1615372 baseEnd_1615372 := by
    simpa [prefixWord, tailWord_1615372, baseEnd_1615372] using wordTrace_append hprefix tailTrace_1615372
  have hstable : (prefixWord ++ tailWord_1615372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615372).length < 2 ^ (prefixWord ++ tailWord_1615372).sum := by decide
  have hdescent : baseEnd_1615372 < baseStart_1615372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615538 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_1615538 : Nat := 118140960795 + 1615538 * 2 ^ 59
def prefixEnd_1615538 : Nat := 4983230072969 + 3 ^ 40 * 1615538 * 2
def baseEnd_1615538 : Nat := 368687782045957970597903

theorem tailTrace_1615538 : CollatzResearch.WordTrace tailWord_1615538 prefixEnd_1615538 368687782045957970597903 := by
  unfold tailWord_1615538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14730877905297303192259817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39282341080792808512692845 14730877905297303192259817)
  ·
    refine ⟨11048158428972977394194863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14730877905297303192259817 11048158428972977394194863)
    ·
      refine ⟨16572237643459466091292295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11048158428972977394194863 16572237643459466091292295)
      ·
        refine ⟨24858356465189199136938443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16572237643459466091292295 24858356465189199136938443)
        ·
          refine ⟨37287534697783798705407665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24858356465189199136938443 37287534697783798705407665)
          ·
            refine ⟨27965651023337849029055749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37287534697783798705407665 27965651023337849029055749)
            ·
              refine ⟨5243559566875846692947953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27965651023337849029055749 5243559566875846692947953)
              ·
                refine ⟨3932669675156885019710965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5243559566875846692947953 3932669675156885019710965)
                ·
                  refine ⟨368687782045957970597903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3932669675156885019710965 368687782045957970597903)
                  ·
                    rfl

theorem cell21_1615538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_1615538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615538 prefixEnd_1615538 := by exact prefixLift 1615538
  have htrace : WordTrace (prefixWord ++ tailWord_1615538) baseStart_1615538 baseEnd_1615538 := by
    simpa [prefixWord, tailWord_1615538, baseEnd_1615538] using wordTrace_append hprefix tailTrace_1615538
  have hstable : (prefixWord ++ tailWord_1615538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615538).length < 2 ^ (prefixWord ++ tailWord_1615538).sum := by decide
  have hdescent : baseEnd_1615538 < baseStart_1615538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615552 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_1615552 : Nat := 118140960795 + 1615552 * 2 ^ 59
def prefixEnd_1615552 : Nat := 4983230072969 + 3 ^ 40 * 1615552 * 2
def baseEnd_1615552 : Nat := 368690977036697057364541

theorem tailTrace_1615552 : CollatzResearch.WordTrace tailWord_1615552 prefixEnd_1615552 368690977036697057364541 := by
  unfold tailWord_1615552
  simp only [CollatzResearch.WordTrace]
  refine ⟨29462011121569246580024455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39282681495425662106699273 29462011121569246580024455)
  ·
    refine ⟨44193016682353869870036683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29462011121569246580024455 44193016682353869870036683)
    ·
      refine ⟨66289525023530804805055025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44193016682353869870036683 66289525023530804805055025)
      ·
        refine ⟨49717143767648103603791269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66289525023530804805055025 49717143767648103603791269)
        ·
          refine ⟨9321964456434019425710863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49717143767648103603791269 9321964456434019425710863)
          ·
            refine ⟨13982946684651029138566295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9321964456434019425710863 13982946684651029138566295)
            ·
              refine ⟨20974420026976543707849443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13982946684651029138566295 20974420026976543707849443)
              ·
                refine ⟨31461630040464815561774165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20974420026976543707849443 31461630040464815561774165)
                ·
                  refine ⟨368690977036697057364541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31461630040464815561774165 368690977036697057364541)
                  ·
                    rfl

theorem cell21_1615552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_1615552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615552 prefixEnd_1615552 := by exact prefixLift 1615552
  have htrace : WordTrace (prefixWord ++ tailWord_1615552) baseStart_1615552 baseEnd_1615552 := by
    simpa [prefixWord, tailWord_1615552, baseEnd_1615552] using wordTrace_append hprefix tailTrace_1615552
  have hstable : (prefixWord ++ tailWord_1615552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615552).length < 2 ^ (prefixWord ++ tailWord_1615552).sum := by decide
  have hdescent : baseEnd_1615552 < baseStart_1615552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615558 : List Nat := [6, 1, 2, 1, 1, 3, 7]
def baseStart_1615558 : Nat := 118140960795 + 1615558 * 2 ^ 59
def prefixEnd_1615558 : Nat := 4983230072969 + 3 ^ 40 * 1615558 * 2
def baseEnd_1615558 : Nat := 40965816257604708918281

theorem tailTrace_1615558 : CollatzResearch.WordTrace tailWord_1615558 prefixEnd_1615558 40965816257604708918281 := by
  unfold tailWord_1615558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1841382533784898630773979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39282827387411170789844885 1841382533784898630773979)
  ·
    refine ⟨2762073800677347946160969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1841382533784898630773979 2762073800677347946160969)
    ·
      refine ⟨2071555350508010959620727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2762073800677347946160969 2071555350508010959620727)
      ·
        refine ⟨3107333025762016439431091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2071555350508010959620727 3107333025762016439431091)
        ·
          refine ⟨4660999538643024659146637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107333025762016439431091 4660999538643024659146637)
          ·
            refine ⟨1747874826991134247179989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4660999538643024659146637 1747874826991134247179989)
            ·
              refine ⟨40965816257604708918281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1747874826991134247179989 40965816257604708918281)
              ·
                rfl

theorem cell21_1615558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 7].length) (baseStart_1615558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615558 prefixEnd_1615558 := by exact prefixLift 1615558
  have htrace : WordTrace (prefixWord ++ tailWord_1615558) baseStart_1615558 baseEnd_1615558 := by
    simpa [prefixWord, tailWord_1615558, baseEnd_1615558] using wordTrace_append hprefix tailTrace_1615558
  have hstable : (prefixWord ++ tailWord_1615558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615558).length < 2 ^ (prefixWord ++ tailWord_1615558).sum := by decide
  have hdescent : baseEnd_1615558 < baseStart_1615558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615572 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1615572 : Nat := 118140960795 + 1615572 * 2 ^ 59
def prefixEnd_1615572 : Nat := 4983230072969 + 3 ^ 40 * 1615572 * 2
def baseEnd_1615572 : Nat := 368695541309181467031167

theorem tailTrace_1615572 : CollatzResearch.WordTrace tailWord_1615572 prefixEnd_1615572 368695541309181467031167 := by
  unfold tailWord_1615572
  simp only [CollatzResearch.WordTrace]
  refine ⟨29462375851533018287888485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39283167802044024383851313 29462375851533018287888485)
  ·
    refine ⟨5524195472162440928979091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29462375851533018287888485 5524195472162440928979091)
    ·
      refine ⟨8286293208243661393468637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5524195472162440928979091 8286293208243661393468637)
      ·
        refine ⟨3107359953091373022550739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8286293208243661393468637 3107359953091373022550739)
        ·
          refine ⟨4661039929637059533826109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107359953091373022550739 4661039929637059533826109)
          ·
            refine ⟨1747889973613897325184791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4661039929637059533826109 1747889973613897325184791)
            ·
              refine ⟨2621834960420845987777187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747889973613897325184791 2621834960420845987777187)
              ·
                refine ⟨3932752440631268981665781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621834960420845987777187 3932752440631268981665781)
                ·
                  refine ⟨368695541309181467031167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3932752440631268981665781 368695541309181467031167)
                  ·
                    rfl

theorem cell21_1615572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1615572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615572 prefixEnd_1615572 := by exact prefixLift 1615572
  have htrace : WordTrace (prefixWord ++ tailWord_1615572) baseStart_1615572 baseEnd_1615572 := by
    simpa [prefixWord, tailWord_1615572, baseEnd_1615572] using wordTrace_append hprefix tailTrace_1615572
  have hstable : (prefixWord ++ tailWord_1615572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615572).length < 2 ^ (prefixWord ++ tailWord_1615572).sum := by decide
  have hdescent : baseEnd_1615572 < baseStart_1615572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615583 : List Nat := [1, 1, 2, 3, 2, 2, 4, 6]
def baseStart_1615583 : Nat := 118140960795 + 1615583 * 2 ^ 59
def prefixEnd_1615583 : Nat := 4983230072969 + 3 ^ 40 * 1615583 * 2
def baseEnd_1615583 : Nat := 122899350553015964115937

theorem tailTrace_1615583 : CollatzResearch.WordTrace tailWord_1615583 prefixEnd_1615583 122899350553015964115937 := by
  unfold tailWord_1615583
  simp only [CollatzResearch.WordTrace]
  refine ⟨58925152906026185454427403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39283435270684123636284935 58925152906026185454427403)
  ·
    refine ⟨88387729359039278181641105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58925152906026185454427403 88387729359039278181641105)
    ·
      refine ⟨66290797019279458636230829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88387729359039278181641105 66290797019279458636230829)
      ·
        refine ⟨24859048882229796988586561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66290797019279458636230829 24859048882229796988586561)
        ·
          refine ⟨18644286661672347741439921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24859048882229796988586561 18644286661672347741439921)
          ·
            refine ⟨13983214996254260806079941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18644286661672347741439921 13983214996254260806079941)
            ·
              refine ⟨2621852811797673901139989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13983214996254260806079941 2621852811797673901139989)
              ·
                refine ⟨122899350553015964115937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2621852811797673901139989 122899350553015964115937)
                ·
                  rfl

theorem cell21_1615583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 6].length) (baseStart_1615583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615583 prefixEnd_1615583 := by exact prefixLift 1615583
  have htrace : WordTrace (prefixWord ++ tailWord_1615583) baseStart_1615583 baseEnd_1615583 := by
    simpa [prefixWord, tailWord_1615583, baseEnd_1615583] using wordTrace_append hprefix tailTrace_1615583
  have hstable : (prefixWord ++ tailWord_1615583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615583).length < 2 ^ (prefixWord ++ tailWord_1615583).sum := by decide
  have hdescent : baseEnd_1615583 < baseStart_1615583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615628 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_1615628 : Nat := 118140960795 + 1615628 * 2 ^ 59
def prefixEnd_1615628 : Nat := 4983230072969 + 3 ^ 40 * 1615628 * 2
def baseEnd_1615628 : Nat := 368708321272137814097719

theorem tailTrace_1615628 : CollatzResearch.WordTrace tailWord_1615628 prefixEnd_1615628 368708321272137814097719 := by
  unfold tailWord_1615628
  simp only [CollatzResearch.WordTrace]
  refine ⟨29463397095431579069907769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39284529460575438759877025 29463397095431579069907769)
  ·
    refine ⟨22097547821573684302430827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29463397095431579069907769 22097547821573684302430827)
    ·
      refine ⟨33146321732360526453646241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22097547821573684302430827 33146321732360526453646241)
      ·
        refine ⟨24859741299270394840234681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33146321732360526453646241 24859741299270394840234681)
        ·
          refine ⟨18644805974452796130176011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24859741299270394840234681 18644805974452796130176011)
          ·
            refine ⟨27967208961679194195264017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18644805974452796130176011 27967208961679194195264017)
            ·
              refine ⟨20975406721259395646448013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27967208961679194195264017 20975406721259395646448013)
              ·
                refine ⟨7865777520472273367418005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20975406721259395646448013 7865777520472273367418005)
                ·
                  refine ⟨368708321272137814097719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7865777520472273367418005 368708321272137814097719)
                  ·
                    rfl

theorem cell21_1615628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_1615628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615628 prefixEnd_1615628 := by exact prefixLift 1615628
  have htrace : WordTrace (prefixWord ++ tailWord_1615628) baseStart_1615628 baseEnd_1615628 := by
    simpa [prefixWord, tailWord_1615628, baseEnd_1615628] using wordTrace_append hprefix tailTrace_1615628
  have hstable : (prefixWord ++ tailWord_1615628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615628).length < 2 ^ (prefixWord ++ tailWord_1615628).sum := by decide
  have hdescent : baseEnd_1615628 < baseStart_1615628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615679 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 4]
def baseStart_1615679 : Nat := 118140960795 + 1615679 * 2 ^ 59
def prefixEnd_1615679 : Nat := 4983230072969 + 3 ^ 40 * 1615679 * 2
def baseEnd_1615679 : Nat := 368719960166973058747615

theorem tailTrace_1615679 : CollatzResearch.WordTrace tailWord_1615679 prefixEnd_1615679 368719960166973058747615 := by
  unfold tailWord_1615679
  simp only [CollatzResearch.WordTrace]
  refine ⟨58928654313678393849922091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39285769542452262566614727 58928654313678393849922091)
  ·
    refine ⟨88392981470517590774883137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58928654313678393849922091 88392981470517590774883137)
    ·
      refine ⟨66294736102888193081162353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88392981470517590774883137 66294736102888193081162353)
      ·
        refine ⟨49721052077166144810871765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66294736102888193081162353 49721052077166144810871765)
        ·
          refine ⟨1165337158058581519004807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49721052077166144810871765 1165337158058581519004807)
          ·
            refine ⟨1748005737087872278507211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165337158058581519004807 1748005737087872278507211)
            ·
              refine ⟨2622008605631808417760817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748005737087872278507211 2622008605631808417760817)
              ·
                refine ⟨1966506454223856313320613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2622008605631808417760817 1966506454223856313320613)
                ·
                  refine ⟨368719960166973058747615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1966506454223856313320613 368719960166973058747615)
                  ·
                    rfl

theorem cell21_1615679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 4].length) (baseStart_1615679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615679 prefixEnd_1615679 := by exact prefixLift 1615679
  have htrace : WordTrace (prefixWord ++ tailWord_1615679) baseStart_1615679 baseEnd_1615679 := by
    simpa [prefixWord, tailWord_1615679, baseEnd_1615679] using wordTrace_append hprefix tailTrace_1615679
  have hstable : (prefixWord ++ tailWord_1615679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615679).length < 2 ^ (prefixWord ++ tailWord_1615679).sum := by decide
  have hdescent : baseEnd_1615679 < baseStart_1615679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615690 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_1615690 : Nat := 118140960795 + 1615690 * 2 ^ 59
def prefixEnd_1615690 : Nat := 4983230072969 + 3 ^ 40 * 1615690 * 2
def baseEnd_1615690 : Nat := 368722470516839484064259

theorem tailTrace_1615690 : CollatzResearch.WordTrace tailWord_1615690 prefixEnd_1615690 368722470516839484064259 := by
  unfold tailWord_1615690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14732263879159635682143131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39286037011092361819048349 14732263879159635682143131)
  ·
    refine ⟨22098395818739453523214697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14732263879159635682143131 22098395818739453523214697)
    ·
      refine ⟨16573796864054590142411023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22098395818739453523214697 16573796864054590142411023)
      ·
        refine ⟨24860695296081885213616535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16573796864054590142411023 24860695296081885213616535)
        ·
          refine ⟨37291042944122827820424803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24860695296081885213616535 37291042944122827820424803)
          ·
            refine ⟨55936564416184241730637205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37291042944122827820424803 55936564416184241730637205)
            ·
              refine ⟨2622026457008636331123619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55936564416184241730637205 2622026457008636331123619)
              ·
                refine ⟨3933039685512954496685429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622026457008636331123619 3933039685512954496685429)
                ·
                  refine ⟨368722470516839484064259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3933039685512954496685429 368722470516839484064259)
                  ·
                    rfl

theorem cell21_1615690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_1615690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615690 prefixEnd_1615690 := by exact prefixLift 1615690
  have htrace : WordTrace (prefixWord ++ tailWord_1615690) baseStart_1615690 baseEnd_1615690 := by
    simpa [prefixWord, tailWord_1615690, baseEnd_1615690] using wordTrace_append hprefix tailTrace_1615690
  have hstable : (prefixWord ++ tailWord_1615690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615690).length < 2 ^ (prefixWord ++ tailWord_1615690).sum := by decide
  have hdescent : baseEnd_1615690 < baseStart_1615690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615724 : List Nat := [2, 2, 1, 1, 4, 4, 1, 3, 3]
def baseStart_1615724 : Nat := 118140960795 + 1615724 * 2 ^ 59
def prefixEnd_1615724 : Nat := 4983230072969 + 3 ^ 40 * 1615724 * 2
def baseEnd_1615724 : Nat := 368730229780062980497523

theorem tailTrace_1615724 : CollatzResearch.WordTrace tailWord_1615724 prefixEnd_1615724 368730229780062980497523 := by
  unfold tailWord_1615724
  simp only [CollatzResearch.WordTrace]
  refine ⟨29465147799257683267655113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39286863732343577690206817 29465147799257683267655113)
  ·
    refine ⟨22098860849443262450741335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29465147799257683267655113 22098860849443262450741335)
    ·
      refine ⟨33148291274164893676112003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22098860849443262450741335 33148291274164893676112003)
      ·
        refine ⟨49722436911247340514168005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33148291274164893676112003 49722436911247340514168005)
        ·
          refine ⟨9322956920858876346406501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49722436911247340514168005 9322956920858876346406501)
          ·
            refine ⟨1748054422661039314951219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9322956920858876346406501 1748054422661039314951219)
            ·
              refine ⟨2622081633991558972426829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748054422661039314951219 2622081633991558972426829)
              ·
                refine ⟨983280612746834614660061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2622081633991558972426829 983280612746834614660061)
                ·
                  refine ⟨368730229780062980497523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983280612746834614660061 368730229780062980497523)
                  ·
                    rfl

theorem cell21_1615724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_1615724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615724 prefixEnd_1615724 := by exact prefixLift 1615724
  have htrace : WordTrace (prefixWord ++ tailWord_1615724) baseStart_1615724 baseEnd_1615724 := by
    simpa [prefixWord, tailWord_1615724, baseEnd_1615724] using wordTrace_append hprefix tailTrace_1615724
  have hstable : (prefixWord ++ tailWord_1615724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615724).length < 2 ^ (prefixWord ++ tailWord_1615724).sum := by decide
  have hdescent : baseEnd_1615724 < baseStart_1615724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615752 : List Nat := [2, 1, 3, 3, 3, 1, 2, 6]
def baseStart_1615752 : Nat := 118140960795 + 1615752 * 2 ^ 59
def prefixEnd_1615752 : Nat := 4983230072969 + 3 ^ 40 * 1615752 * 2
def baseEnd_1615752 : Nat := 122912206587180384676933

theorem tailTrace_1615752 : CollatzResearch.WordTrace tailWord_1615752 prefixEnd_1615752 122912206587180384676933 := by
  unfold tailWord_1615752
  simp only [CollatzResearch.WordTrace]
  refine ⟨29465658421206963658664755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39287544561609284878219673 29465658421206963658664755)
  ·
    refine ⟨44198487631810445487997133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29465658421206963658664755 44198487631810445487997133)
    ·
      refine ⟨16574432861928917057998925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44198487631810445487997133 16574432861928917057998925)
      ·
        refine ⟨6215412323223343896749597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16574432861928917057998925 6215412323223343896749597)
        ·
          refine ⟨2330779621208753961281099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6215412323223343896749597 2330779621208753961281099)
          ·
            refine ⟨3496169431813130941921649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330779621208753961281099 3496169431813130941921649)
            ·
              refine ⟨2622127073859848206441237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3496169431813130941921649 2622127073859848206441237)
              ·
                refine ⟨122912206587180384676933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2622127073859848206441237 122912206587180384676933)
                ·
                  rfl

theorem cell21_1615752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_1615752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615752 prefixEnd_1615752 := by exact prefixLift 1615752
  have htrace : WordTrace (prefixWord ++ tailWord_1615752) baseStart_1615752 baseEnd_1615752 := by
    simpa [prefixWord, tailWord_1615752, baseEnd_1615752] using wordTrace_append hprefix tailTrace_1615752
  have hstable : (prefixWord ++ tailWord_1615752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615752).length < 2 ^ (prefixWord ++ tailWord_1615752).sum := by decide
  have hdescent : baseEnd_1615752 < baseStart_1615752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615797 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 4]
def baseStart_1615797 : Nat := 118140960795 + 1615797 * 2 ^ 59
def prefixEnd_1615797 : Nat := 4983230072969 + 3 ^ 40 * 1615797 * 2
def baseEnd_1615797 : Nat := 368746889374631075780707

theorem tailTrace_1615797 : CollatzResearch.WordTrace tailWord_1615797 prefixEnd_1615797 368746889374631075780707 := by
  unfold tailWord_1615797
  simp only [CollatzResearch.WordTrace]
  refine ⟨58932958127250900002717645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39288638751500600001811763 58932958127250900002717645)
  ·
    refine ⟨22099859297719087501019117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58932958127250900002717645 22099859297719087501019117)
    ·
      refine ⟨8287447236644657812882169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22099859297719087501019117 8287447236644657812882169)
      ·
        refine ⟨6215585427483493359661627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8287447236644657812882169 6215585427483493359661627)
        ·
          refine ⟨9323378141225240039492441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215585427483493359661627 9323378141225240039492441)
          ·
            refine ⟨6992533605918930029619331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9323378141225240039492441 6992533605918930029619331)
            ·
              refine ⟨10488800408878395044428997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6992533605918930029619331 10488800408878395044428997)
              ·
                refine ⟨1966650076664699070830437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10488800408878395044428997 1966650076664699070830437)
                ·
                  refine ⟨368746889374631075780707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1966650076664699070830437 368746889374631075780707)
                  ·
                    rfl

theorem cell21_1615797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_1615797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615797 prefixEnd_1615797 := by exact prefixLift 1615797
  have htrace : WordTrace (prefixWord ++ tailWord_1615797) baseStart_1615797 baseEnd_1615797 := by
    simpa [prefixWord, tailWord_1615797, baseEnd_1615797] using wordTrace_append hprefix tailTrace_1615797
  have hstable : (prefixWord ++ tailWord_1615797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615797).length < 2 ^ (prefixWord ++ tailWord_1615797).sum := by decide
  have hdescent : baseEnd_1615797 < baseStart_1615797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615828 : List Nat := [2, 4, 1, 2, 1, 1, 5, 5]
def baseStart_1615828 : Nat := 118140960795 + 1615828 * 2 ^ 59
def prefixEnd_1615828 : Nat := 4983230072969 + 3 ^ 40 * 1615828 * 2
def baseEnd_1615828 : Nat := 122917987998993970254659

theorem tailTrace_1615828 : CollatzResearch.WordTrace tailWord_1615828 prefixEnd_1615828 122917987998993970254659 := by
  unfold tailWord_1615828
  simp only [CollatzResearch.WordTrace]
  refine ⟨29467044395069296148548069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39289392526759061531397425 29467044395069296148548069)
  ·
    refine ⟨5525070824075493027852763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29467044395069296148548069 5525070824075493027852763)
    ·
      refine ⟨8287606236113239541779145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5525070824075493027852763 8287606236113239541779145)
      ·
        refine ⟨6215704677084929656334359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8287606236113239541779145 6215704677084929656334359)
        ·
          refine ⟨9323557015627394484501539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215704677084929656334359 9323557015627394484501539)
          ·
            refine ⟨13985335523441091726752309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9323557015627394484501539 13985335523441091726752309)
            ·
              refine ⟨1311125205322602349383029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13985335523441091726752309 1311125205322602349383029)
              ·
                refine ⟨122917987998993970254659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1311125205322602349383029 122917987998993970254659)
                ·
                  rfl

theorem cell21_1615828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_1615828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615828 prefixEnd_1615828 := by exact prefixLift 1615828
  have htrace : WordTrace (prefixWord ++ tailWord_1615828) baseStart_1615828 baseEnd_1615828 := by
    simpa [prefixWord, tailWord_1615828, baseEnd_1615828] using wordTrace_append hprefix tailTrace_1615828
  have hstable : (prefixWord ++ tailWord_1615828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615828).length < 2 ^ (prefixWord ++ tailWord_1615828).sum := by decide
  have hdescent : baseEnd_1615828 < baseStart_1615828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615893 : List Nat := [1, 3, 2, 1, 6, 1, 1, 3, 3]
def baseStart_1615893 : Nat := 118140960795 + 1615893 * 2 ^ 59
def prefixEnd_1615893 : Nat := 4983230072969 + 3 ^ 40 * 1615893 * 2
def baseEnd_1615893 : Nat := 368768797882556242180511

theorem tailTrace_1615893 : CollatzResearch.WordTrace tailWord_1615893 prefixEnd_1615893 368768797882556242180511 := by
  unfold tailWord_1615893
  simp only [CollatzResearch.WordTrace]
  refine ⟨58936459534903108398212333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39290973023268738932141555 58936459534903108398212333)
  ·
    refine ⟨22101172325588665649329625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58936459534903108398212333 22101172325588665649329625)
    ·
      refine ⟨16575879244191499236997219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22101172325588665649329625 16575879244191499236997219)
      ·
        refine ⟨24863818866287248855495829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16575879244191499236997219 24863818866287248855495829)
        ·
          refine ⟨1165491509357214790101367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24863818866287248855495829 1165491509357214790101367)
          ·
            refine ⟨1748237264035822185152051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165491509357214790101367 1748237264035822185152051)
            ·
              refine ⟨2622355896053733277728077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748237264035822185152051 2622355896053733277728077)
              ·
                refine ⟨983383461020149979148029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2622355896053733277728077 983383461020149979148029)
                ·
                  refine ⟨368768797882556242180511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983383461020149979148029 368768797882556242180511)
                  ·
                    rfl

theorem cell21_1615893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_1615893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615893 prefixEnd_1615893 := by exact prefixLift 1615893
  have htrace : WordTrace (prefixWord ++ tailWord_1615893) baseStart_1615893 baseEnd_1615893 := by
    simpa [prefixWord, tailWord_1615893, baseEnd_1615893] using wordTrace_append hprefix tailTrace_1615893
  have hstable : (prefixWord ++ tailWord_1615893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615893).length < 2 ^ (prefixWord ++ tailWord_1615893).sum := by decide
  have hdescent : baseEnd_1615893 < baseStart_1615893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615924 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1615924 : Nat := 118140960795 + 1615924 * 2 ^ 59
def prefixEnd_1615924 : Nat := 4983230072969 + 3 ^ 40 * 1615924 * 2
def baseEnd_1615924 : Nat := 368775872504907077163781

theorem tailTrace_1615924 : CollatzResearch.WordTrace tailWord_1615924 prefixEnd_1615924 368775872504907077163781 := by
  unfold tailWord_1615924
  simp only [CollatzResearch.WordTrace]
  refine ⟨29468795098895400346295413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39291726798527200461727217 29468795098895400346295413)
  ·
    refine ⟨2762699540521443782465195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29468795098895400346295413 2762699540521443782465195)
    ·
      refine ⟨4144049310782165673697793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2762699540521443782465195 4144049310782165673697793)
      ·
        refine ⟨3108036983086624255273345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4144049310782165673697793 3108036983086624255273345)
        ·
          refine ⟨2331027737314968191455009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3108036983086624255273345 2331027737314968191455009)
          ·
            refine ⟨1748270802986226143591257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2331027737314968191455009 1748270802986226143591257)
            ·
              refine ⟨1311203102239669607693443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748270802986226143591257 1311203102239669607693443)
              ·
                refine ⟨1966804653359504411540165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311203102239669607693443 1966804653359504411540165)
                ·
                  refine ⟨368775872504907077163781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1966804653359504411540165 368775872504907077163781)
                  ·
                    rfl

theorem cell21_1615924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1615924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615924 prefixEnd_1615924 := by exact prefixLift 1615924
  have htrace : WordTrace (prefixWord ++ tailWord_1615924) baseStart_1615924 baseEnd_1615924 := by
    simpa [prefixWord, tailWord_1615924, baseEnd_1615924] using wordTrace_append hprefix tailTrace_1615924
  have hstable : (prefixWord ++ tailWord_1615924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615924).length < 2 ^ (prefixWord ++ tailWord_1615924).sum := by decide
  have hdescent : baseEnd_1615924 < baseStart_1615924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615977 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 5]
def baseStart_1615977 : Nat := 118140960795 + 1615977 * 2 ^ 59
def prefixEnd_1615977 : Nat := 4983230072969 + 3 ^ 40 * 1615977 * 2
def baseEnd_1615977 : Nat := 368787967826990762780339

theorem tailTrace_1615977 : CollatzResearch.WordTrace tailWord_1615977 prefixEnd_1615977 368787967826990762780339 := by
  unfold tailWord_1615977
  simp only [CollatzResearch.WordTrace]
  refine ⟨58939523266598790744270185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39293015511065860496180123 58939523266598790744270185)
  ·
    refine ⟨44204642449949093058202639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58939523266598790744270185 44204642449949093058202639)
    ·
      refine ⟨66306963674923639587303959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44204642449949093058202639 66306963674923639587303959)
      ·
        refine ⟨99460445512385459380955939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66306963674923639587303959 99460445512385459380955939)
        ·
          refine ⟨149190668268578189071433909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99460445512385459380955939 149190668268578189071433909)
          ·
            refine ⟨13986625150179205225446929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149190668268578189071433909 13986625150179205225446929)
            ·
              refine ⟨10489968862634403919085197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13986625150179205225446929 10489968862634403919085197)
              ·
                refine ⟨3933738323487901469656949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10489968862634403919085197 3933738323487901469656949)
                ·
                  refine ⟨368787967826990762780339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3933738323487901469656949 368787967826990762780339)
                  ·
                    rfl

theorem cell21_1615977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_1615977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1615977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1615977 prefixEnd_1615977 := by exact prefixLift 1615977
  have htrace : WordTrace (prefixWord ++ tailWord_1615977) baseStart_1615977 baseEnd_1615977 := by
    simpa [prefixWord, tailWord_1615977, baseEnd_1615977] using wordTrace_append hprefix tailTrace_1615977
  have hstable : (prefixWord ++ tailWord_1615977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615977).length < 2 ^ (prefixWord ++ tailWord_1615977).sum := by decide
  have hdescent : baseEnd_1615977 < baseStart_1615977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616101 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 4]
def baseStart_1616101 : Nat := 118140960795 + 1616101 * 2 ^ 59
def prefixEnd_1616101 : Nat := 4983230072969 + 3 ^ 40 * 1616101 * 2
def baseEnd_1616101 : Nat := 368816266316394102713419

theorem tailTrace_1616101 : CollatzResearch.WordTrace tailWord_1616101 prefixEnd_1616101 368816266316394102713419 := by
  unfold tailWord_1616101
  simp only [CollatzResearch.WordTrace]
  refine ⟨58944045918149559921784157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39296030612099706614522771 58944045918149559921784157)
  ·
    refine ⟨22104017219306084970669059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58944045918149559921784157 22104017219306084970669059)
    ·
      refine ⟨33156025828959127456003589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22104017219306084970669059 33156025828959127456003589)
      ·
        refine ⟨6216754842929836398000673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33156025828959127456003589 6216754842929836398000673)
        ·
          refine ⟨4662566132197377298500505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6216754842929836398000673 4662566132197377298500505)
          ·
            refine ⟨3496924599148032973875379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4662566132197377298500505 3496924599148032973875379)
            ·
              refine ⟨5245386898722049460813069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496924599148032973875379 5245386898722049460813069)
              ·
                refine ⟨1967020087020768547804901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5245386898722049460813069 1967020087020768547804901)
                ·
                  refine ⟨368816266316394102713419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1967020087020768547804901 368816266316394102713419)
                  ·
                    rfl

theorem cell21_1616101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_1616101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616101 prefixEnd_1616101 := by exact prefixLift 1616101
  have htrace : WordTrace (prefixWord ++ tailWord_1616101) baseStart_1616101 baseEnd_1616101 := by
    simpa [prefixWord, tailWord_1616101, baseEnd_1616101] using wordTrace_append hprefix tailTrace_1616101
  have hstable : (prefixWord ++ tailWord_1616101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616101).length < 2 ^ (prefixWord ++ tailWord_1616101).sum := by decide
  have hdescent : baseEnd_1616101 < baseStart_1616101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616143 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 6]
def baseStart_1616143 : Nat := 118140960795 + 1616143 * 2 ^ 59
def prefixEnd_1616143 : Nat := 4983230072969 + 3 ^ 40 * 1616143 * 2
def baseEnd_1616143 : Nat := 368825851288611363013333

theorem tailTrace_1616143 : CollatzResearch.WordTrace tailWord_1616143 prefixEnd_1616143 368825851288611363013333 := by
  unfold tailWord_1616143
  simp only [CollatzResearch.WordTrace]
  refine ⟨58945577783997401094813083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39297051855998267396542055 58945577783997401094813083)
  ·
    refine ⟨88418366675996101642219625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58945577783997401094813083 88418366675996101642219625)
    ·
      refine ⟨66313775006997076231664719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88418366675996101642219625 66313775006997076231664719)
      ·
        refine ⟨99470662510495614347497079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66313775006997076231664719 99470662510495614347497079)
        ·
          refine ⟨149205993765743421521245619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99470662510495614347497079 149205993765743421521245619)
          ·
            refine ⟨223808990648615132281868429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149205993765743421521245619 223808990648615132281868429)
            ·
              refine ⟨83928371493230674605700661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223808990648615132281868429 83928371493230674605700661)
              ·
                refine ⟨7868284827490375744284437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83928371493230674605700661 7868284827490375744284437)
                ·
                  refine ⟨368825851288611363013333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7868284827490375744284437 368825851288611363013333)
                  ·
                    rfl

theorem cell21_1616143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_1616143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616143 prefixEnd_1616143 := by exact prefixLift 1616143
  have htrace : WordTrace (prefixWord ++ tailWord_1616143) baseStart_1616143 baseEnd_1616143 := by
    simpa [prefixWord, tailWord_1616143, baseEnd_1616143] using wordTrace_append hprefix tailTrace_1616143
  have hstable : (prefixWord ++ tailWord_1616143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616143).length < 2 ^ (prefixWord ++ tailWord_1616143).sum := by decide
  have hdescent : baseEnd_1616143 < baseStart_1616143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616180 : List Nat := [2, 5, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1616180 : Nat := 118140960795 + 1616180 * 2 ^ 59
def prefixEnd_1616180 : Nat := 4983230072969 + 3 ^ 40 * 1616180 * 2
def baseEnd_1616180 : Nat := 368834295192707520896591

theorem tailTrace_1616180 : CollatzResearch.WordTrace tailWord_1616180 prefixEnd_1616180 368834295192707520896591 := by
  unfold tailWord_1616180
  simp only [CollatzResearch.WordTrace]
  refine ⟨29473463642431678206954997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39297951523242237609273329 29473463642431678206954997)
  ·
    refine ⟨2763137216477969831902031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29473463642431678206954997 2763137216477969831902031)
    ·
      refine ⟨4144705824716954747853047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2763137216477969831902031 4144705824716954747853047)
      ·
        refine ⟨6217058737075432121779571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144705824716954747853047 6217058737075432121779571)
        ·
          refine ⟨9325588105613148182669357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217058737075432121779571 9325588105613148182669357)
          ·
            refine ⟨3497095539604930568501009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9325588105613148182669357 3497095539604930568501009)
            ·
              refine ⟨2622821654703697926375757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3497095539604930568501009 2622821654703697926375757)
              ·
                refine ⟨983558120513886722390909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2622821654703697926375757 983558120513886722390909)
                ·
                  refine ⟨368834295192707520896591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983558120513886722390909 368834295192707520896591)
                  ·
                    rfl

theorem cell21_1616180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1616180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616180 prefixEnd_1616180 := by exact prefixLift 1616180
  have htrace : WordTrace (prefixWord ++ tailWord_1616180) baseStart_1616180 baseEnd_1616180 := by
    simpa [prefixWord, tailWord_1616180, baseEnd_1616180] using wordTrace_append hprefix tailTrace_1616180
  have hstable : (prefixWord ++ tailWord_1616180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616180).length < 2 ^ (prefixWord ++ tailWord_1616180).sum := by decide
  have hdescent : baseEnd_1616180 < baseStart_1616180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616270 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_1616270 : Nat := 118140960795 + 1616270 * 2 ^ 59
def prefixEnd_1616270 : Nat := 4983230072969 + 3 ^ 40 * 1616270 * 2
def baseEnd_1616270 : Nat := 368854834418887364396407

theorem tailTrace_1616270 : CollatzResearch.WordTrace tailWord_1616270 prefixEnd_1616270 368854834418887364396407 := by
  unfold tailWord_1616270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7368776231817162723085783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39300139903024867856457509 7368776231817162723085783)
  ·
    refine ⟨11053164347725744084628675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7368776231817162723085783 11053164347725744084628675)
    ·
      refine ⟨16579746521588616126943013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11053164347725744084628675 16579746521588616126943013)
      ·
        refine ⟨3108702472797865523801815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16579746521588616126943013 3108702472797865523801815)
        ·
          refine ⟨4663053709196798285702723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108702472797865523801815 4663053709196798285702723)
          ·
            refine ⟨6994580563795197428554085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663053709196798285702723 6994580563795197428554085)
            ·
              refine ⟨1311483855711599517853891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6994580563795197428554085 1311483855711599517853891)
              ·
                refine ⟨1967225783567399276780837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311483855711599517853891 1967225783567399276780837)
                ·
                  refine ⟨368854834418887364396407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1967225783567399276780837 368854834418887364396407)
                  ·
                    rfl

theorem cell21_1616270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_1616270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616270 prefixEnd_1616270 := by exact prefixLift 1616270
  have htrace : WordTrace (prefixWord ++ tailWord_1616270) baseStart_1616270 baseEnd_1616270 := by
    simpa [prefixWord, tailWord_1616270, baseEnd_1616270] using wordTrace_append hprefix tailTrace_1616270
  have hstable : (prefixWord ++ tailWord_1616270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616270).length < 2 ^ (prefixWord ++ tailWord_1616270).sum := by decide
  have hdescent : baseEnd_1616270 < baseStart_1616270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616371 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 6]
def baseStart_1616371 : Nat := 118140960795 + 1616371 * 2 ^ 59
def prefixEnd_1616371 : Nat := 4983230072969 + 3 ^ 40 * 1616371 * 2
def baseEnd_1616371 : Nat := 368877883994933633212867

theorem tailTrace_1616371 : CollatzResearch.WordTrace tailWord_1616371 prefixEnd_1616371 368877883994933633212867 := by
  unfold tailWord_1616371
  simp only [CollatzResearch.WordTrace]
  refine ⟨58953893627171396034112967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39302595751447597356075311 58953893627171396034112967)
  ·
    refine ⟨88430840440757094051169451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58953893627171396034112967 88430840440757094051169451)
    ·
      refine ⟨132646260661135641076754177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88430840440757094051169451 132646260661135641076754177)
      ·
        refine ⟨99484695495851730807565633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132646260661135641076754177 99484695495851730807565633)
        ·
          refine ⟨74613521621888798105674225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99484695495851730807565633 74613521621888798105674225)
          ·
            refine ⟨55960141216416598579255669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74613521621888798105674225 55960141216416598579255669)
            ·
              refine ⟨5246263239039056116805219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55960141216416598579255669 5246263239039056116805219)
              ·
                refine ⟨7869394858558584175207829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246263239039056116805219 7869394858558584175207829)
                ·
                  refine ⟨368877883994933633212867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7869394858558584175207829 368877883994933633212867)
                  ·
                    rfl

theorem cell21_1616371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_1616371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616371 prefixEnd_1616371 := by exact prefixLift 1616371
  have htrace : WordTrace (prefixWord ++ tailWord_1616371) baseStart_1616371 baseEnd_1616371 := by
    simpa [prefixWord, tailWord_1616371, baseEnd_1616371] using wordTrace_append hprefix tailTrace_1616371
  have hstable : (prefixWord ++ tailWord_1616371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616371).length < 2 ^ (prefixWord ++ tailWord_1616371).sum := by decide
  have hdescent : baseEnd_1616371 < baseStart_1616371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616374 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1616374 : Nat := 118140960795 + 1616374 * 2 ^ 59
def prefixEnd_1616374 : Nat := 4983230072969 + 3 ^ 40 * 1616374 * 2
def baseEnd_1616374 : Nat := 368878568635806294662861

theorem tailTrace_1616374 : CollatzResearch.WordTrace tailWord_1616374 prefixEnd_1616374 368878568635806294662861 := by
  unfold tailWord_1616374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3684625190385032971654511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39302668697440351697648117 3684625190385032971654511)
  ·
    refine ⟨5526937785577549457481767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3684625190385032971654511 5526937785577549457481767)
    ·
      refine ⟨8290406678366324186222651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5526937785577549457481767 8290406678366324186222651)
      ·
        refine ⟨12435610017549486279333977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8290406678366324186222651 12435610017549486279333977)
        ·
          refine ⟨9326707513162114709500483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12435610017549486279333977 9326707513162114709500483)
          ·
            refine ⟨13990061269743172064250725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9326707513162114709500483 13990061269743172064250725)
            ·
              refine ⟨2623136488076844762047011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13990061269743172064250725 2623136488076844762047011)
              ·
                refine ⟨3934704732115267143070517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623136488076844762047011 3934704732115267143070517)
                ·
                  refine ⟨368878568635806294662861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3934704732115267143070517 368878568635806294662861)
                  ·
                    rfl

theorem cell21_1616374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1616374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616374 prefixEnd_1616374 := by exact prefixLift 1616374
  have htrace : WordTrace (prefixWord ++ tailWord_1616374) baseStart_1616374 baseEnd_1616374 := by
    simpa [prefixWord, tailWord_1616374, baseEnd_1616374] using wordTrace_append hprefix tailTrace_1616374
  have hstable : (prefixWord ++ tailWord_1616374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616374).length < 2 ^ (prefixWord ++ tailWord_1616374).sum := by decide
  have hdescent : baseEnd_1616374 < baseStart_1616374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616433 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 5]
def baseStart_1616433 : Nat := 118140960795 + 1616433 * 2 ^ 59
def prefixEnd_1616433 : Nat := 4983230072969 + 3 ^ 40 * 1616433 * 2
def baseEnd_1616433 : Nat := 368892033239635303179407

theorem tailTrace_1616433 : CollatzResearch.WordTrace tailWord_1616433 prefixEnd_1616433 368892033239635303179407 := by
  unfold tailWord_1616433
  simp only [CollatzResearch.WordTrace]
  refine ⟨58956154952946780622869953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39304103301964520415246635 58956154952946780622869953)
  ·
    refine ⟨44217116214710085467152465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58956154952946780622869953 44217116214710085467152465)
    ·
      refine ⟨33162837161032564100364349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44217116214710085467152465 33162837161032564100364349)
      ·
        refine ⟨12436063935387211537636631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33162837161032564100364349 12436063935387211537636631)
        ·
          refine ⟨18654095903080817306454947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12436063935387211537636631 18654095903080817306454947)
          ·
            refine ⟨27981143854621225959682421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18654095903080817306454947 27981143854621225959682421)
            ·
              refine ⟨2623232236370739933720227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27981143854621225959682421 2623232236370739933720227)
              ·
                refine ⟨3934848354556109900580341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623232236370739933720227 3934848354556109900580341)
                ·
                  refine ⟨368892033239635303179407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3934848354556109900580341 368892033239635303179407)
                  ·
                    rfl

theorem cell21_1616433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_1616433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616433 prefixEnd_1616433 := by exact prefixLift 1616433
  have htrace : WordTrace (prefixWord ++ tailWord_1616433) baseStart_1616433 baseEnd_1616433 := by
    simpa [prefixWord, tailWord_1616433, baseEnd_1616433] using wordTrace_append hprefix tailTrace_1616433
  have hstable : (prefixWord ++ tailWord_1616433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616433).length < 2 ^ (prefixWord ++ tailWord_1616433).sum := by decide
  have hdescent : baseEnd_1616433 < baseStart_1616433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616537 : List Nat := [1, 2, 1, 2, 1, 2, 12]
def baseStart_1616537 : Nat := 118140960795 + 1616537 * 2 ^ 59
def prefixEnd_1616537 : Nat := 4983230072969 + 3 ^ 40 * 1616537 * 2
def baseEnd_1616537 : Nat := 40990640828506025938429

theorem tailTrace_1616537 : CollatzResearch.WordTrace tailWord_1616537 prefixEnd_1616537 40990640828506025938429 := by
  unfold tailWord_1616537
  simp only [CollatzResearch.WordTrace]
  refine ⟨58959948144570006384655865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39306632096380004256437243 58959948144570006384655865)
  ·
    refine ⟨44219961108427504788491899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58959948144570006384655865 44219961108427504788491899)
    ·
      refine ⟨66329941662641257182737849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44219961108427504788491899 66329941662641257182737849)
      ·
        refine ⟨49747456246980942887053387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66329941662641257182737849 49747456246980942887053387)
        ·
          refine ⟨74621184370471414330580081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49747456246980942887053387 74621184370471414330580081)
          ·
            refine ⟨55965888277853560747935061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74621184370471414330580081 55965888277853560747935061)
            ·
              refine ⟨40990640828506025938429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 55965888277853560747935061 40990640828506025938429)
              ·
                rfl

theorem cell21_1616537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 12].length) (baseStart_1616537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616537 prefixEnd_1616537 := by exact prefixLift 1616537
  have htrace : WordTrace (prefixWord ++ tailWord_1616537) baseStart_1616537 baseEnd_1616537 := by
    simpa [prefixWord, tailWord_1616537, baseEnd_1616537] using wordTrace_append hprefix tailTrace_1616537
  have hstable : (prefixWord ++ tailWord_1616537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616537).length < 2 ^ (prefixWord ++ tailWord_1616537).sum := by decide
  have hdescent : baseEnd_1616537 < baseStart_1616537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616540 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_1616540 : Nat := 118140960795 + 1616540 * 2 ^ 59
def prefixEnd_1616540 : Nat := 4983230072969 + 3 ^ 40 * 1616540 * 2
def baseEnd_1616540 : Nat := 368916452097426894895855

theorem tailTrace_1616540 : CollatzResearch.WordTrace tailWord_1616540 prefixEnd_1616540 368916452097426894895855 := by
  unfold tailWord_1616540
  simp only [CollatzResearch.WordTrace]
  refine ⟨29480028781779568948507537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39306705042372758598010049 29480028781779568948507537)
  ·
    refine ⟨22110021586334676711380653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29480028781779568948507537 22110021586334676711380653)
    ·
      refine ⟨8291258094875503766767745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22110021586334676711380653 8291258094875503766767745)
      ·
        refine ⟨6218443571156627825075809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8291258094875503766767745 6218443571156627825075809)
        ·
          refine ⟨4663832678367470868806857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6218443571156627825075809 4663832678367470868806857)
          ·
            refine ⟨3497874508775603151605143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4663832678367470868806857 3497874508775603151605143)
            ·
              refine ⟨5246811763163404727407715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497874508775603151605143 5246811763163404727407715)
              ·
                refine ⟨7870217644745107091111573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246811763163404727407715 7870217644745107091111573)
                ·
                  refine ⟨368916452097426894895855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7870217644745107091111573 368916452097426894895855)
                  ·
                    rfl

theorem cell21_1616540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_1616540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616540 prefixEnd_1616540 := by exact prefixLift 1616540
  have htrace : WordTrace (prefixWord ++ tailWord_1616540) baseStart_1616540 baseEnd_1616540 := by
    simpa [prefixWord, tailWord_1616540, baseEnd_1616540] using wordTrace_append hprefix tailTrace_1616540
  have hstable : (prefixWord ++ tailWord_1616540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616540).length < 2 ^ (prefixWord ++ tailWord_1616540).sum := by decide
  have hdescent : baseEnd_1616540 < baseStart_1616540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616577 : List Nat := [1, 2, 6, 2, 1, 2, 1, 3, 3]
def baseStart_1616577 : Nat := 118140960795 + 1616577 * 2 ^ 59
def prefixEnd_1616577 : Nat := 4983230072969 + 3 ^ 40 * 1616577 * 2
def baseEnd_1616577 : Nat := 368924896001523052779113

theorem tailTrace_1616577 : CollatzResearch.WordTrace tailWord_1616577 prefixEnd_1616577 368924896001523052779113 := by
  unfold tailWord_1616577
  simp only [CollatzResearch.WordTrace]
  refine ⟨58961407064425093216111985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39307604709616728810741323 58961407064425093216111985)
  ·
    refine ⟨44221055298318819912083989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58961407064425093216111985 44221055298318819912083989)
    ·
      refine ⟨2072861967108694683378937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44221055298318819912083989 2072861967108694683378937)
      ·
        refine ⟨1554646475331521012534203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2072861967108694683378937 1554646475331521012534203)
        ·
          refine ⟨2331969712997281518801305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554646475331521012534203 2331969712997281518801305)
          ·
            refine ⟨1748977284747961139100979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2331969712997281518801305 1748977284747961139100979)
            ·
              refine ⟨2623465927121941708651469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748977284747961139100979 2623465927121941708651469)
              ·
                refine ⟨983799722670728140744301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2623465927121941708651469 983799722670728140744301)
                ·
                  refine ⟨368924896001523052779113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983799722670728140744301 368924896001523052779113)
                  ·
                    rfl

theorem cell21_1616577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 3].length) (baseStart_1616577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616577 prefixEnd_1616577 := by exact prefixLift 1616577
  have htrace : WordTrace (prefixWord ++ tailWord_1616577) baseStart_1616577 baseEnd_1616577 := by
    simpa [prefixWord, tailWord_1616577, baseEnd_1616577] using wordTrace_append hprefix tailTrace_1616577
  have hstable : (prefixWord ++ tailWord_1616577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616577).length < 2 ^ (prefixWord ++ tailWord_1616577).sum := by decide
  have hdescent : baseEnd_1616577 < baseStart_1616577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616599 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 6]
def baseStart_1616599 : Nat := 118140960795 + 1616599 * 2 ^ 59
def prefixEnd_1616599 : Nat := 4983230072969 + 3 ^ 40 * 1616599 * 2
def baseEnd_1616599 : Nat := 368929916701255903412401

theorem tailTrace_1616599 : CollatzResearch.WordTrace tailWord_1616599 prefixEnd_1616599 368929916701255903412401 := by
  unfold tailWord_1616599
  simp only [CollatzResearch.WordTrace]
  refine ⟨58962209470345390973412851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39308139646896927315608567 58962209470345390973412851)
  ·
    refine ⟨88443314205518086460119277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58962209470345390973412851 88443314205518086460119277)
    ·
      refine ⟨33166242827069282422544729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88443314205518086460119277 33166242827069282422544729)
      ·
        refine ⟨24874682120301961816908547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33166242827069282422544729 24874682120301961816908547)
        ·
          refine ⟨37312023180452942725362821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24874682120301961816908547 37312023180452942725362821)
          ·
            refine ⟨6996004346334926761005529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37312023180452942725362821 6996004346334926761005529)
            ·
              refine ⟨5247003259751195070754147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6996004346334926761005529 5247003259751195070754147)
              ·
                refine ⟨7870504889626792606131221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5247003259751195070754147 7870504889626792606131221)
                ·
                  refine ⟨368929916701255903412401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7870504889626792606131221 368929916701255903412401)
                  ·
                    rfl

theorem cell21_1616599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_1616599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616599 prefixEnd_1616599 := by exact prefixLift 1616599
  have htrace : WordTrace (prefixWord ++ tailWord_1616599) baseStart_1616599 baseEnd_1616599 := by
    simpa [prefixWord, tailWord_1616599, baseEnd_1616599] using wordTrace_append hprefix tailTrace_1616599
  have hstable : (prefixWord ++ tailWord_1616599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616599).length < 2 ^ (prefixWord ++ tailWord_1616599).sum := by decide
  have hdescent : baseEnd_1616599 < baseStart_1616599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616630 : List Nat := [5, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1616630 : Nat := 118140960795 + 1616630 * 2 ^ 59
def prefixEnd_1616630 : Nat := 4983230072969 + 3 ^ 40 * 1616630 * 2
def baseEnd_1616630 : Nat := 122978997107868912798557

theorem tailTrace_1616630 : CollatzResearch.WordTrace tailWord_1616630 prefixEnd_1616630 122978997107868912798557 := by
  unfold tailWord_1616630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685208758327067704236959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39308893422155388845194229 3685208758327067704236959)
  ·
    refine ⟨5527813137490601556355439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3685208758327067704236959 5527813137490601556355439)
    ·
      refine ⟨8291719706235902334533159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5527813137490601556355439 8291719706235902334533159)
      ·
        refine ⟨12437579559353853501799739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8291719706235902334533159 12437579559353853501799739)
        ·
          refine ⟨18656369339030780252699609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12437579559353853501799739 18656369339030780252699609)
          ·
            refine ⟨13992277004273085189524707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18656369339030780252699609 13992277004273085189524707)
            ·
              refine ⟨20988415506409627784287061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13992277004273085189524707 20988415506409627784287061)
              ·
                refine ⟨122978997107868912798557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20988415506409627784287061 122978997107868912798557)
                ·
                  rfl

theorem cell21_1616630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1616630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616630 prefixEnd_1616630 := by exact prefixLift 1616630
  have htrace : WordTrace (prefixWord ++ tailWord_1616630) baseStart_1616630 baseEnd_1616630 := by
    simpa [prefixWord, tailWord_1616630, baseEnd_1616630] using wordTrace_append hprefix tailTrace_1616630
  have hstable : (prefixWord ++ tailWord_1616630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616630).length < 2 ^ (prefixWord ++ tailWord_1616630).sum := by decide
  have hdescent : baseEnd_1616630 < baseStart_1616630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616720 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_1616720 : Nat := 118140960795 + 1616720 * 2 ^ 59
def prefixEnd_1616720 : Nat := 4983230072969 + 3 ^ 40 * 1616720 * 2
def baseEnd_1616720 : Nat := 368957530549786581895487

theorem tailTrace_1616720 : CollatzResearch.WordTrace tailWord_1616720 prefixEnd_1616720 368957530549786581895487 := by
  unfold tailWord_1616720
  simp only [CollatzResearch.WordTrace]
  refine ⟨29483311351453514319283807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39311081801938019092378409 29483311351453514319283807)
  ·
    refine ⟨44224967027180271478925711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29483311351453514319283807 44224967027180271478925711)
    ·
      refine ⟨66337450540770407218388567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44224967027180271478925711 66337450540770407218388567)
      ·
        refine ⟨99506175811155610827582851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66337450540770407218388567 99506175811155610827582851)
        ·
          refine ⟨149259263716733416241374277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99506175811155610827582851 149259263716733416241374277)
          ·
            refine ⟨27986111946887515545257677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149259263716733416241374277 27986111946887515545257677)
            ·
              refine ⟨10494791980082818329471629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27986111946887515545257677 10494791980082818329471629)
              ·
                refine ⟨3935546992531056873551861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10494791980082818329471629 3935546992531056873551861)
                ·
                  refine ⟨368957530549786581895487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3935546992531056873551861 368957530549786581895487)
                  ·
                    rfl

theorem cell21_1616720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_1616720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616720 prefixEnd_1616720 := by exact prefixLift 1616720
  have htrace : WordTrace (prefixWord ++ tailWord_1616720) baseStart_1616720 baseEnd_1616720 := by
    simpa [prefixWord, tailWord_1616720, baseEnd_1616720] using wordTrace_append hprefix tailTrace_1616720
  have hstable : (prefixWord ++ tailWord_1616720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616720).length < 2 ^ (prefixWord ++ tailWord_1616720).sum := by decide
  have hdescent : baseEnd_1616720 < baseStart_1616720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616754 : List Nat := [3, 2, 1, 2, 1, 1, 5, 3, 3]
def baseStart_1616754 : Nat := 118140960795 + 1616754 * 2 ^ 59
def prefixEnd_1616754 : Nat := 4983230072969 + 3 ^ 40 * 1616754 * 2
def baseEnd_1616754 : Nat := 368965289813010078328751

theorem tailTrace_1616754 : CollatzResearch.WordTrace tailWord_1616754 prefixEnd_1616754 368965289813010078328751 := by
  unfold tailWord_1616754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14741965696195963111326329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39311908523189234963536877 14741965696195963111326329)
  ·
    refine ⟨11056474272146972333494747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14741965696195963111326329 11056474272146972333494747)
    ·
      refine ⟨16584711408220458500242121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11056474272146972333494747 16584711408220458500242121)
      ·
        refine ⟨12438533556165343875181591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16584711408220458500242121 12438533556165343875181591)
        ·
          refine ⟨18657800334248015812772387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12438533556165343875181591 18657800334248015812772387)
          ·
            refine ⟨27986700501372023719158581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18657800334248015812772387 27986700501372023719158581)
            ·
              refine ⟨2623753172003627223671117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27986700501372023719158581 2623753172003627223671117)
              ·
                refine ⟨983907439501360208876669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2623753172003627223671117 983907439501360208876669)
                ·
                  refine ⟨368965289813010078328751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983907439501360208876669 368965289813010078328751)
                  ·
                    rfl

theorem cell21_1616754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_1616754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616754 prefixEnd_1616754 := by exact prefixLift 1616754
  have htrace : WordTrace (prefixWord ++ tailWord_1616754) baseStart_1616754 baseEnd_1616754 := by
    simpa [prefixWord, tailWord_1616754, baseEnd_1616754] using wordTrace_append hprefix tailTrace_1616754
  have hstable : (prefixWord ++ tailWord_1616754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616754).length < 2 ^ (prefixWord ++ tailWord_1616754).sum := by decide
  have hdescent : baseEnd_1616754 < baseStart_1616754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616765 : List Nat := [1, 4, 1, 1, 2, 1, 11]
def baseStart_1616765 : Nat := 118140960795 + 1616765 * 2 ^ 59
def prefixEnd_1616765 : Nat := 4983230072969 + 3 ^ 40 * 1616765 * 2
def baseEnd_1616765 : Nat := 40996422240319611516155

theorem tailTrace_1616765 : CollatzResearch.WordTrace tailWord_1616765 prefixEnd_1616765 40996422240319611516155 := by
  unfold tailWord_1616765
  simp only [CollatzResearch.WordTrace]
  refine ⟨58968263987744001323955749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39312175991829334215970499 58968263987744001323955749)
  ·
    refine ⟨11056549497702000248241703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58968263987744001323955749 11056549497702000248241703)
    ·
      refine ⟨16584824246553000372362555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11056549497702000248241703 16584824246553000372362555)
      ·
        refine ⟨24877236369829500558543833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16584824246553000372362555 24877236369829500558543833)
        ·
          refine ⟨18657927277372125418907875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24877236369829500558543833 18657927277372125418907875)
          ·
            refine ⟨27986890916058188128361813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18657927277372125418907875 27986890916058188128361813)
            ·
              refine ⟨40996422240319611516155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27986890916058188128361813 40996422240319611516155)
              ·
                rfl

theorem cell21_1616765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 11].length) (baseStart_1616765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616765 prefixEnd_1616765 := by exact prefixLift 1616765
  have htrace : WordTrace (prefixWord ++ tailWord_1616765) baseStart_1616765 baseEnd_1616765 := by
    simpa [prefixWord, tailWord_1616765, baseEnd_1616765] using wordTrace_append hprefix tailTrace_1616765
  have hstable : (prefixWord ++ tailWord_1616765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616765).length < 2 ^ (prefixWord ++ tailWord_1616765).sum := by decide
  have hdescent : baseEnd_1616765 < baseStart_1616765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616830 : List Nat := [4, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_1616830 : Nat := 118140960795 + 1616830 * 2 ^ 59
def prefixEnd_1616830 : Nat := 4983230072969 + 3 ^ 40 * 1616830 * 2
def baseEnd_1616830 : Nat := 368982634048450835061929

theorem tailTrace_1616830 : CollatzResearch.WordTrace tailWord_1616830 prefixEnd_1616830 368982634048450835061929 := by
  unfold tailWord_1616830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7371329341563564678133993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39313756488339011616714629 7371329341563564678133993)
  ·
    refine ⟨5528497006172673508600495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7371329341563564678133993 5528497006172673508600495)
    ·
      refine ⟨8292745509259010262900743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5528497006172673508600495 8292745509259010262900743)
      ·
        refine ⟨12439118263888515394351115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8292745509259010262900743 12439118263888515394351115)
        ·
          refine ⟨18658677395832773091526673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12439118263888515394351115 18658677395832773091526673)
          ·
            refine ⟨13994008046874579818645005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18658677395832773091526673 13994008046874579818645005)
            ·
              refine ⟨5247753017577967431991877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13994008046874579818645005 5247753017577967431991877)
              ·
                refine ⟨983953690795868893498477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5247753017577967431991877 983953690795868893498477)
                ·
                  refine ⟨368982634048450835061929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983953690795868893498477 368982634048450835061929)
                  ·
                    rfl

theorem cell21_1616830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_1616830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616830 prefixEnd_1616830 := by exact prefixLift 1616830
  have htrace : WordTrace (prefixWord ++ tailWord_1616830) baseStart_1616830 baseEnd_1616830 := by
    simpa [prefixWord, tailWord_1616830, baseEnd_1616830] using wordTrace_append hprefix tailTrace_1616830
  have hstable : (prefixWord ++ tailWord_1616830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616830).length < 2 ^ (prefixWord ++ tailWord_1616830).sum := by decide
  have hdescent : baseEnd_1616830 < baseStart_1616830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616878 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_1616878 : Nat := 118140960795 + 1616878 * 2 ^ 59
def prefixEnd_1616878 : Nat := 4983230072969 + 3 ^ 40 * 1616878 * 2
def baseEnd_1616878 : Nat := 368993588302413418261831

theorem tailTrace_1616878 : CollatzResearch.WordTrace tailWord_1616878 prefixEnd_1616878 368993588302413418261831 := by
  unfold tailWord_1616878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7371548179541827702852411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39314923624223081081879525 7371548179541827702852411)
  ·
    refine ⟨11057322269312741554278617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7371548179541827702852411 11057322269312741554278617)
    ·
      refine ⟨8292991701984556165708963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11057322269312741554278617 8292991701984556165708963)
      ·
        refine ⟨12439487552976834248563445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8292991701984556165708963 12439487552976834248563445)
        ·
          refine ⟨1166201958091578210802823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12439487552976834248563445 1166201958091578210802823)
          ·
            refine ⟨1749302937137367316204235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166201958091578210802823 1749302937137367316204235)
            ·
              refine ⟨2623954405706050974306353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749302937137367316204235 2623954405706050974306353)
              ·
                refine ⟨1967965804279538230729765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623954405706050974306353 1967965804279538230729765)
                ·
                  refine ⟨368993588302413418261831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1967965804279538230729765 368993588302413418261831)
                  ·
                    rfl

theorem cell21_1616878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_1616878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616878 prefixEnd_1616878 := by exact prefixLift 1616878
  have htrace : WordTrace (prefixWord ++ tailWord_1616878) baseStart_1616878 baseEnd_1616878 := by
    simpa [prefixWord, tailWord_1616878, baseEnd_1616878] using wordTrace_append hprefix tailTrace_1616878
  have hstable : (prefixWord ++ tailWord_1616878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616878).length < 2 ^ (prefixWord ++ tailWord_1616878).sum := by decide
  have hdescent : baseEnd_1616878 < baseStart_1616878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616889 : List Nat := [1, 2, 1, 3, 1, 3, 1, 6, 3]
def baseStart_1616889 : Nat := 118140960795 + 1616889 * 2 ^ 59
def prefixEnd_1616889 : Nat := 4983230072969 + 3 ^ 40 * 1616889 * 2
def baseEnd_1616889 : Nat := 368996098652279843578475

theorem tailTrace_1616889 : CollatzResearch.WordTrace tailWord_1616889 prefixEnd_1616889 368996098652279843578475 := by
  unfold tailWord_1616889
  simp only [CollatzResearch.WordTrace]
  refine ⟨58972786639294770501469721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39315191092863180334313147 58972786639294770501469721)
  ·
    refine ⟨44229589979471077876102291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58972786639294770501469721 44229589979471077876102291)
    ·
      refine ⟨66344384969206616814153437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44229589979471077876102291 66344384969206616814153437)
      ·
        refine ⟨24879144363452481305307539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66344384969206616814153437 24879144363452481305307539)
        ·
          refine ⟨37318716545178721957961309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24879144363452481305307539 37318716545178721957961309)
          ·
            refine ⟨13994518704442020734235491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37318716545178721957961309 13994518704442020734235491)
            ·
              refine ⟨20991778056663031101353237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13994518704442020734235491 20991778056663031101353237)
              ·
                refine ⟨983989596406079582875933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20991778056663031101353237 983989596406079582875933)
                ·
                  refine ⟨368996098652279843578475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983989596406079582875933 368996098652279843578475)
                  ·
                    rfl

theorem cell21_1616889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 3].length) (baseStart_1616889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616889 prefixEnd_1616889 := by exact prefixLift 1616889
  have htrace : WordTrace (prefixWord ++ tailWord_1616889) baseStart_1616889 baseEnd_1616889 := by
    simpa [prefixWord, tailWord_1616889, baseEnd_1616889] using wordTrace_append hprefix tailTrace_1616889
  have hstable : (prefixWord ++ tailWord_1616889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616889).length < 2 ^ (prefixWord ++ tailWord_1616889).sum := by decide
  have hdescent : baseEnd_1616889 < baseStart_1616889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616999 : List Nat := [1, 1, 5, 1, 1, 5, 2, 2, 3]
def baseStart_1616999 : Nat := 118140960795 + 1616999 * 2 ^ 59
def prefixEnd_1616999 : Nat := 4983230072969 + 3 ^ 40 * 1616999 * 2
def baseEnd_1616999 : Nat := 369021202150944096744917

theorem tailTrace_1616999 : CollatzResearch.WordTrace tailWord_1616999 prefixEnd_1616999 369021202150944096744917 := by
  unfold tailWord_1616999
  simp only [CollatzResearch.WordTrace]
  refine ⟨58976798668896259287974051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39317865779264172858649367 58976798668896259287974051)
  ·
    refine ⟨88465198003344388931961077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58976798668896259287974051 88465198003344388931961077)
    ·
      refine ⟨8293612312813536462371351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88465198003344388931961077 8293612312813536462371351)
      ·
        refine ⟨12440418469220304693557027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8293612312813536462371351 12440418469220304693557027)
        ·
          refine ⟨18660627703830457040335541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12440418469220304693557027 18660627703830457040335541)
          ·
            refine ⟨1749433847234105347531457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18660627703830457040335541 1749433847234105347531457)
            ·
              refine ⟨1312075385425579010648593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1749433847234105347531457 1312075385425579010648593)
              ·
                refine ⟨984056539069184257986445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312075385425579010648593 984056539069184257986445)
                ·
                  refine ⟨369021202150944096744917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984056539069184257986445 369021202150944096744917)
                  ·
                    rfl

theorem cell21_1616999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 3].length) (baseStart_1616999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1616999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1616999 prefixEnd_1616999 := by exact prefixLift 1616999
  have htrace : WordTrace (prefixWord ++ tailWord_1616999) baseStart_1616999 baseEnd_1616999 := by
    simpa [prefixWord, tailWord_1616999, baseEnd_1616999] using wordTrace_append hprefix tailTrace_1616999
  have hstable : (prefixWord ++ tailWord_1616999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616999).length < 2 ^ (prefixWord ++ tailWord_1616999).sum := by decide
  have hdescent : baseEnd_1616999 < baseStart_1616999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617058 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1617058 : Nat := 118140960795 + 1617058 * 2 ^ 59
def prefixEnd_1617058 : Nat := 4983230072969 + 3 ^ 40 * 1617058 * 2
def baseEnd_1617058 : Nat := 369034666754773105261463

theorem tailTrace_1617058 : CollatzResearch.WordTrace tailWord_1617058 prefixEnd_1617058 369034666754773105261463 := by
  unfold tailWord_1617058
  simp only [CollatzResearch.WordTrace]
  refine ⟨14744737643920628091092957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39319300383788341576247885 14744737643920628091092957)
  ·
    refine ⟨5529276616470235534159859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14744737643920628091092957 5529276616470235534159859)
    ·
      refine ⟨8293914924705353301239789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5529276616470235534159859 8293914924705353301239789)
      ·
        refine ⟨3110218096764507487964921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8293914924705353301239789 3110218096764507487964921)
        ·
          refine ⟨2332663572573380615973691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3110218096764507487964921 2332663572573380615973691)
          ·
            refine ⟨3498995358860070923960537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332663572573380615973691 3498995358860070923960537)
            ·
              refine ⟨2624246519145053192970403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3498995358860070923960537 2624246519145053192970403)
              ·
                refine ⟨3936369778717579789455605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624246519145053192970403 3936369778717579789455605)
                ·
                  refine ⟨369034666754773105261463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3936369778717579789455605 369034666754773105261463)
                  ·
                    rfl

theorem cell21_1617058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1617058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617058 prefixEnd_1617058 := by exact prefixLift 1617058
  have htrace : WordTrace (prefixWord ++ tailWord_1617058) baseStart_1617058 baseEnd_1617058 := by
    simpa [prefixWord, tailWord_1617058, baseEnd_1617058] using wordTrace_append hprefix tailTrace_1617058
  have hstable : (prefixWord ++ tailWord_1617058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617058).length < 2 ^ (prefixWord ++ tailWord_1617058).sum := by decide
  have hdescent : baseEnd_1617058 < baseStart_1617058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617078 : List Nat := [5, 1, 3, 2, 2, 1, 2, 5]
def baseStart_1617078 : Nat := 118140960795 + 1617078 * 2 ^ 59
def prefixEnd_1617078 : Nat := 4983230072969 + 3 ^ 40 * 1617078 * 2
def baseEnd_1617078 : Nat := 123013077009085838309363

theorem tailTrace_1617078 : CollatzResearch.WordTrace tailWord_1617078 prefixEnd_1617078 123013077009085838309363 := by
  unfold tailWord_1617078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686230002225628486256243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39319786690406703853399925 3686230002225628486256243)
  ·
    refine ⟨5529345003338442729384365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3686230002225628486256243 5529345003338442729384365)
    ·
      refine ⟨2073504376251916023519137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5529345003338442729384365 2073504376251916023519137)
      ·
        refine ⟨1555128282188937017639353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2073504376251916023519137 1555128282188937017639353)
        ·
          refine ⟨1166346211641702763229515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1555128282188937017639353 1166346211641702763229515)
          ·
            refine ⟨1749519317462554144844273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166346211641702763229515 1749519317462554144844273)
            ·
              refine ⟨1312139488096915608633205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1749519317462554144844273 1312139488096915608633205)
              ·
                refine ⟨123013077009085838309363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1312139488096915608633205 123013077009085838309363)
                ·
                  rfl

theorem cell21_1617078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_1617078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617078 prefixEnd_1617078 := by exact prefixLift 1617078
  have htrace : WordTrace (prefixWord ++ tailWord_1617078) baseStart_1617078 baseEnd_1617078 := by
    simpa [prefixWord, tailWord_1617078, baseEnd_1617078] using wordTrace_append hprefix tailTrace_1617078
  have hstable : (prefixWord ++ tailWord_1617078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617078).length < 2 ^ (prefixWord ++ tailWord_1617078).sum := by decide
  have hdescent : baseEnd_1617078 < baseStart_1617078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617083 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 7]
def baseStart_1617083 : Nat := 118140960795 + 1617083 * 2 ^ 59
def prefixEnd_1617083 : Nat := 4983230072969 + 3 ^ 40 * 1617083 * 2
def baseEnd_1617083 : Nat := 369040372095378617344745

theorem tailTrace_1617083 : CollatzResearch.WordTrace tailWord_1617083 prefixEnd_1617083 369040372095378617344745 := by
  unfold tailWord_1617083
  simp only [CollatzResearch.WordTrace]
  refine ⟨58979862400591941634031903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39319908267061294422687935 58979862400591941634031903)
  ·
    refine ⟨88469793600887912451047855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58979862400591941634031903 88469793600887912451047855)
    ·
      refine ⟨132704690401331868676571783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88469793600887912451047855 132704690401331868676571783)
      ·
        refine ⟨199057035601997803014857675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132704690401331868676571783 199057035601997803014857675)
        ·
          refine ⟨298585553402996704522286513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199057035601997803014857675 298585553402996704522286513)
          ·
            refine ⟨223939165052247528391714885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298585553402996704522286513 223939165052247528391714885)
            ·
              refine ⟨41988593447296411573446541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223939165052247528391714885 41988593447296411573446541)
              ·
                refine ⟨15745722542736154340042453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41988593447296411573446541 15745722542736154340042453)
                ·
                  refine ⟨369040372095378617344745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15745722542736154340042453 369040372095378617344745)
                  ·
                    rfl

theorem cell21_1617083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_1617083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617083 prefixEnd_1617083 := by exact prefixLift 1617083
  have htrace : WordTrace (prefixWord ++ tailWord_1617083) baseStart_1617083 baseEnd_1617083 := by
    simpa [prefixWord, tailWord_1617083, baseEnd_1617083] using wordTrace_append hprefix tailTrace_1617083
  have hstable : (prefixWord ++ tailWord_1617083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617083).length < 2 ^ (prefixWord ++ tailWord_1617083).sum := by decide
  have hdescent : baseEnd_1617083 < baseStart_1617083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617086 : List Nat := [4, 2, 1, 1, 3, 2, 1, 7]
def baseStart_1617086 : Nat := 118140960795 + 1617086 * 2 ^ 59
def prefixEnd_1617086 : Nat := 4983230072969 + 3 ^ 40 * 1617086 * 2
def baseEnd_1617086 : Nat := 123013685578750426264913

theorem tailTrace_1617086 : CollatzResearch.WordTrace tailWord_1617086 prefixEnd_1617086 123013685578750426264913 := by
  unfold tailWord_1617086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7372496477447634143298889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39319981213054048764260741 7372496477447634143298889)
  ·
    refine ⟨5529372358085725607474167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7372496477447634143298889 5529372358085725607474167)
    ·
      refine ⟨8294058537128588411211251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5529372358085725607474167 8294058537128588411211251)
      ·
        refine ⟨12441087805692882616816877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8294058537128588411211251 12441087805692882616816877)
        ·
          refine ⟨4665407927134830981306329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12441087805692882616816877 4665407927134830981306329)
          ·
            refine ⟨3499055945351123235979747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4665407927134830981306329 3499055945351123235979747)
            ·
              refine ⟨5248583918026684853969621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3499055945351123235979747 5248583918026684853969621)
              ·
                refine ⟨123013685578750426264913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5248583918026684853969621 123013685578750426264913)
                ·
                  rfl

theorem cell21_1617086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_1617086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617086 prefixEnd_1617086 := by exact prefixLift 1617086
  have htrace : WordTrace (prefixWord ++ tailWord_1617086) baseStart_1617086 baseEnd_1617086 := by
    simpa [prefixWord, tailWord_1617086, baseEnd_1617086] using wordTrace_append hprefix tailTrace_1617086
  have hstable : (prefixWord ++ tailWord_1617086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617086).length < 2 ^ (prefixWord ++ tailWord_1617086).sum := by decide
  have hdescent : baseEnd_1617086 < baseStart_1617086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617092 : List Nat := [2, 3, 3, 1, 4, 1, 1, 3, 3]
def baseStart_1617092 : Nat := 118140960795 + 1617092 * 2 ^ 59
def prefixEnd_1617092 : Nat := 4983230072969 + 3 ^ 40 * 1617092 * 2
def baseEnd_1617092 : Nat := 369042426017996601694727

theorem tailTrace_1617092 : CollatzResearch.WordTrace tailWord_1617092 prefixEnd_1617092 369042426017996601694727 := by
  unfold tailWord_1617092
  simp only [CollatzResearch.WordTrace]
  refine ⟨29490095328779668085554765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39320127105039557447406353 29490095328779668085554765)
  ·
    refine ⟨11058785748292375532083037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29490095328779668085554765 11058785748292375532083037)
    ·
      refine ⟨4147044655609640824531139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11058785748292375532083037 4147044655609640824531139)
      ·
        refine ⟨6220566983414461236796709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147044655609640824531139 6220566983414461236796709)
        ·
          refine ⟨1166356309390211481899383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6220566983414461236796709 1166356309390211481899383)
          ·
            refine ⟨1749534464085317222849075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166356309390211481899383 1749534464085317222849075)
            ·
              refine ⟨2624301696127975834273613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749534464085317222849075 2624301696127975834273613)
              ·
                refine ⟨984113136047990937852605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2624301696127975834273613 984113136047990937852605)
                ·
                  refine ⟨369042426017996601694727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984113136047990937852605 369042426017996601694727)
                  ·
                    rfl

theorem cell21_1617092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_1617092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617092 prefixEnd_1617092 := by exact prefixLift 1617092
  have htrace : WordTrace (prefixWord ++ tailWord_1617092) baseStart_1617092 baseEnd_1617092 := by
    simpa [prefixWord, tailWord_1617092, baseEnd_1617092] using wordTrace_append hprefix tailTrace_1617092
  have hstable : (prefixWord ++ tailWord_1617092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617092).length < 2 ^ (prefixWord ++ tailWord_1617092).sum := by decide
  have hdescent : baseEnd_1617092 < baseStart_1617092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617131 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 4]
def baseStart_1617131 : Nat := 118140960795 + 1617131 * 2 ^ 59
def prefixEnd_1617131 : Nat := 4983230072969 + 3 ^ 40 * 1617131 * 2
def baseEnd_1617131 : Nat := 369051326349341200544647

theorem tailTrace_1617131 : CollatzResearch.WordTrace tailWord_1617131 prefixEnd_1617131 369051326349341200544647 := by
  unfold tailWord_1617131
  simp only [CollatzResearch.WordTrace]
  refine ⟨58981613104418045831779247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39321075402945363887852831 58981613104418045831779247)
  ·
    refine ⟨88472419656627068747668871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58981613104418045831779247 88472419656627068747668871)
    ·
      refine ⟨132708629484940603121503307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88472419656627068747668871 132708629484940603121503307)
      ·
        refine ⟨199062944227410904682254961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132708629484940603121503307 199062944227410904682254961)
        ·
          refine ⟨149297208170558178511691221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199062944227410904682254961 149297208170558178511691221)
          ·
            refine ⟨3499153316497457308867763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 149297208170558178511691221 3499153316497457308867763)
            ·
              refine ⟨5248729974746185963301645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3499153316497457308867763 5248729974746185963301645)
              ·
                refine ⟨1968273740529819736238117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5248729974746185963301645 1968273740529819736238117)
                ·
                  refine ⟨369051326349341200544647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1968273740529819736238117 369051326349341200544647)
                  ·
                    rfl

theorem cell21_1617131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 4].length) (baseStart_1617131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617131 prefixEnd_1617131 := by exact prefixLift 1617131
  have htrace : WordTrace (prefixWord ++ tailWord_1617131) baseStart_1617131 baseEnd_1617131 := by
    simpa [prefixWord, tailWord_1617131, baseEnd_1617131] using wordTrace_append hprefix tailTrace_1617131
  have hstable : (prefixWord ++ tailWord_1617131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617131).length < 2 ^ (prefixWord ++ tailWord_1617131).sum := by decide
  have hdescent : baseEnd_1617131 < baseStart_1617131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617252 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1617252 : Nat := 118140960795 + 1617252 * 2 ^ 59
def prefixEnd_1617252 : Nat := 4983230072969 + 3 ^ 40 * 1617252 * 2
def baseEnd_1617252 : Nat := 369078940197871879027733

theorem tailTrace_1617252 : CollatzResearch.WordTrace tailWord_1617252 prefixEnd_1617252 369078940197871879027733 := by
  unfold tailWord_1617252
  simp only [CollatzResearch.WordTrace]
  refine ⟨29493013168489841748467005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39324017557986455664622673 29493013168489841748467005)
  ·
    refine ⟨11059879938183690655675127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29493013168489841748467005 11059879938183690655675127)
    ·
      refine ⟨16589819907275535983512691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11059879938183690655675127 16589819907275535983512691)
      ·
        refine ⟨24884729860913303975269037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16589819907275535983512691 24884729860913303975269037)
        ·
          refine ⟨9331773697842488990725889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24884729860913303975269037 9331773697842488990725889)
          ·
            refine ⟨6998830273381866743044417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9331773697842488990725889 6998830273381866743044417)
            ·
              refine ⟨5249122705036400057283313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6998830273381866743044417 5249122705036400057283313)
              ·
                refine ⟨3936842028777300042962485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5249122705036400057283313 3936842028777300042962485)
                ·
                  refine ⟨369078940197871879027733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3936842028777300042962485 369078940197871879027733)
                  ·
                    rfl

theorem cell21_1617252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1617252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617252 prefixEnd_1617252 := by exact prefixLift 1617252
  have htrace : WordTrace (prefixWord ++ tailWord_1617252) baseStart_1617252 baseEnd_1617252 := by
    simpa [prefixWord, tailWord_1617252, baseEnd_1617252] using wordTrace_append hprefix tailTrace_1617252
  have hstable : (prefixWord ++ tailWord_1617252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617252).length < 2 ^ (prefixWord ++ tailWord_1617252).sum := by decide
  have hdescent : baseEnd_1617252 < baseStart_1617252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617255 : List Nat := [1, 1, 5, 1, 4, 2, 2, 5]
def baseStart_1617255 : Nat := 118140960795 + 1617255 * 2 ^ 59
def prefixEnd_1617255 : Nat := 4983230072969 + 3 ^ 40 * 1617255 * 2
def baseEnd_1617255 : Nat := 123026541612914846825909

theorem tailTrace_1617255 : CollatzResearch.WordTrace tailWord_1617255 prefixEnd_1617255 123026541612914846825909 := by
  unfold tailWord_1617255
  simp only [CollatzResearch.WordTrace]
  refine ⟨58986135755968815009293219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39324090503979210006195479 58986135755968815009293219)
  ·
    refine ⟨88479203633953222513939829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58986135755968815009293219 88479203633953222513939829)
    ·
      refine ⟨8294925340683114610681859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88479203633953222513939829 8294925340683114610681859)
      ·
        refine ⟨12442388011024671916022789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8294925340683114610681859 12442388011024671916022789)
        ·
          refine ⟨2332947752067125984254273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12442388011024671916022789 2332947752067125984254273)
          ·
            refine ⟨1749710814050344488190705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2332947752067125984254273 1749710814050344488190705)
            ·
              refine ⟨1312283110537758366143029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1749710814050344488190705 1312283110537758366143029)
              ·
                refine ⟨123026541612914846825909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1312283110537758366143029 123026541612914846825909)
                ·
                  rfl

theorem cell21_1617255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 5].length) (baseStart_1617255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617255 prefixEnd_1617255 := by exact prefixLift 1617255
  have htrace : WordTrace (prefixWord ++ tailWord_1617255) baseStart_1617255 baseEnd_1617255 := by
    simpa [prefixWord, tailWord_1617255, baseEnd_1617255] using wordTrace_append hprefix tailTrace_1617255
  have hstable : (prefixWord ++ tailWord_1617255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617255).length < 2 ^ (prefixWord ++ tailWord_1617255).sum := by decide
  have hdescent : baseEnd_1617255 < baseStart_1617255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617266 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_1617266 : Nat := 118140960795 + 1617266 * 2 ^ 59
def prefixEnd_1617266 : Nat := 4983230072969 + 3 ^ 40 * 1617266 * 2
def baseEnd_1617266 : Nat := 369082135188610965794371

theorem tailTrace_1617266 : CollatzResearch.WordTrace tailWord_1617266 prefixEnd_1617266 369082135188610965794371 := by
  unfold tailWord_1617266
  simp only [CollatzResearch.WordTrace]
  refine ⟨14746634239732240971985913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39324357972619309258629101 14746634239732240971985913)
  ·
    refine ⟨11059975679799180728989435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14746634239732240971985913 11059975679799180728989435)
    ·
      refine ⟨16589963519698771093484153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11059975679799180728989435 16589963519698771093484153)
      ·
        refine ⟨12442472639774078320113115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16589963519698771093484153 12442472639774078320113115)
        ·
          refine ⟨18663708959661117480169673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12442472639774078320113115 18663708959661117480169673)
          ·
            refine ⟨13997781719745838110127255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18663708959661117480169673 13997781719745838110127255)
            ·
              refine ⟨20996672579618757165190883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13997781719745838110127255 20996672579618757165190883)
              ·
                refine ⟨31495008869428135747786325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20996672579618757165190883 31495008869428135747786325)
                ·
                  refine ⟨369082135188610965794371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31495008869428135747786325 369082135188610965794371)
                  ·
                    rfl

theorem cell21_1617266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_1617266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617266 prefixEnd_1617266 := by exact prefixLift 1617266
  have htrace : WordTrace (prefixWord ++ tailWord_1617266) baseStart_1617266 baseEnd_1617266 := by
    simpa [prefixWord, tailWord_1617266, baseEnd_1617266] using wordTrace_append hprefix tailTrace_1617266
  have hstable : (prefixWord ++ tailWord_1617266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617266).length < 2 ^ (prefixWord ++ tailWord_1617266).sum := by decide
  have hdescent : baseEnd_1617266 < baseStart_1617266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617300 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1617300 : Nat := 118140960795 + 1617300 * 2 ^ 59
def prefixEnd_1617300 : Nat := 4983230072969 + 3 ^ 40 * 1617300 * 2
def baseEnd_1617300 : Nat := 369089894451834462227635

theorem tailTrace_1617300 : CollatzResearch.WordTrace tailWord_1617300 prefixEnd_1617300 369089894451834462227635 := by
  unfold tailWord_1617300
  simp only [CollatzResearch.WordTrace]
  refine ⟨29493888520402893847340677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39325184693870525129787569 29493888520402893847340677)
  ·
    refine ⟨5530104097575542596376377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29493888520402893847340677 5530104097575542596376377)
    ·
      refine ⟨4147578073181656947282283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5530104097575542596376377 4147578073181656947282283)
      ·
        refine ⟨6221367109772485420923425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147578073181656947282283 6221367109772485420923425)
        ·
          refine ⟨4666025332329364065692569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6221367109772485420923425 4666025332329364065692569)
          ·
            refine ⟨3499518999247023049269427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4666025332329364065692569 3499518999247023049269427)
            ·
              refine ⟨5249278498870534573904141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3499518999247023049269427 5249278498870534573904141)
              ·
                refine ⟨1968479437076450465214053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5249278498870534573904141 1968479437076450465214053)
                ·
                  refine ⟨369089894451834462227635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1968479437076450465214053 369089894451834462227635)
                  ·
                    rfl

theorem cell21_1617300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1617300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617300 prefixEnd_1617300 := by exact prefixLift 1617300
  have htrace : WordTrace (prefixWord ++ tailWord_1617300) baseStart_1617300 baseEnd_1617300 := by
    simpa [prefixWord, tailWord_1617300, baseEnd_1617300] using wordTrace_append hprefix tailTrace_1617300
  have hstable : (prefixWord ++ tailWord_1617300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617300).length < 2 ^ (prefixWord ++ tailWord_1617300).sum := by decide
  have hdescent : baseEnd_1617300 < baseStart_1617300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617469 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 4]
def baseStart_1617469 : Nat := 118140960795 + 1617469 * 2 ^ 59
def prefixEnd_1617469 : Nat := 4983230072969 + 3 ^ 40 * 1617469 * 2
def baseEnd_1617469 : Nat := 369128462554327723910623

theorem tailTrace_1617469 : CollatzResearch.WordTrace tailWord_1617469 prefixEnd_1617469 369128462554327723910623 := by
  unfold tailWord_1617469
  simp only [CollatzResearch.WordTrace]
  refine ⟨58993940977193529557583461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39329293984795686371722307 58993940977193529557583461)
  ·
    refine ⟨11061363933223786792046899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58993940977193529557583461 11061363933223786792046899)
    ·
      refine ⟨16592045899835680188070349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11061363933223786792046899 16592045899835680188070349)
      ·
        refine ⟨6222017212438380070526381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16592045899835680188070349 6222017212438380070526381)
        ·
          refine ⟨2333256454664392526447393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6222017212438380070526381 2333256454664392526447393)
          ·
            refine ⟨1749942340998294394835545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2333256454664392526447393 1749942340998294394835545)
            ·
              refine ⟨1312456755748720796126659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1749942340998294394835545 1312456755748720796126659)
              ·
                refine ⟨1968685133623081194189989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312456755748720796126659 1968685133623081194189989)
                ·
                  refine ⟨369128462554327723910623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1968685133623081194189989 369128462554327723910623)
                  ·
                    rfl

theorem cell21_1617469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_1617469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617469 prefixEnd_1617469 := by exact prefixLift 1617469
  have htrace : WordTrace (prefixWord ++ tailWord_1617469) baseStart_1617469 baseEnd_1617469 := by
    simpa [prefixWord, tailWord_1617469, baseEnd_1617469] using wordTrace_append hprefix tailTrace_1617469
  have hstable : (prefixWord ++ tailWord_1617469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617469).length < 2 ^ (prefixWord ++ tailWord_1617469).sum := by decide
  have hdescent : baseEnd_1617469 < baseStart_1617469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617508 : List Nat := [2, 3, 1, 1, 2, 12]
def baseStart_1617508 : Nat := 118140960795 + 1617508 * 2 ^ 59
def prefixEnd_1617508 : Nat := 4983230072969 + 3 ^ 40 * 1617508 * 2
def baseEnd_1617508 : Nat := 13671754180950826768909

theorem tailTrace_1617508 : CollatzResearch.WordTrace tailWord_1617508 prefixEnd_1617508 13671754180950826768909 := by
  unfold tailWord_1617508
  simp only [CollatzResearch.WordTrace]
  refine ⟨29497681712026119609126589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39330242282701492812168785 29497681712026119609126589)
  ·
    refine ⟨11061630642009794853422471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29497681712026119609126589 11061630642009794853422471)
    ·
      refine ⟨16592445963014692280133707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11061630642009794853422471 16592445963014692280133707)
      ·
        refine ⟨24888668944522038420200561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16592445963014692280133707 24888668944522038420200561)
        ·
          refine ⟨18666501708391528815150421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24888668944522038420200561 18666501708391528815150421)
          ·
            refine ⟨13671754180950826768909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18666501708391528815150421 13671754180950826768909)
            ·
              rfl

theorem cell21_1617508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 12].length) (baseStart_1617508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617508 prefixEnd_1617508 := by exact prefixLift 1617508
  have htrace : WordTrace (prefixWord ++ tailWord_1617508) baseStart_1617508 baseEnd_1617508 := by
    simpa [prefixWord, tailWord_1617508, baseEnd_1617508] using wordTrace_append hprefix tailTrace_1617508
  have hstable : (prefixWord ++ tailWord_1617508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617508).length < 2 ^ (prefixWord ++ tailWord_1617508).sum := by decide
  have hdescent : baseEnd_1617508 < baseStart_1617508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617514 : List Nat := [3, 1, 3, 2, 1, 2, 4, 2, 3]
def baseStart_1617514 : Nat := 118140960795 + 1617514 * 2 ^ 59
def prefixEnd_1617514 : Nat := 4983230072969 + 3 ^ 40 * 1617514 * 2
def baseEnd_1617514 : Nat := 369138732167417645660531

theorem tailTrace_1617514 : CollatzResearch.WordTrace tailWord_1617514 prefixEnd_1617514 369138732167417645660531 := by
  unfold tailWord_1617514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14748895565507625560742899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39330388174687001495314397 14748895565507625560742899)
  ·
    refine ⟨22123343348261438341114349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14748895565507625560742899 22123343348261438341114349)
    ·
      refine ⟨8296253755598039377917881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22123343348261438341114349 8296253755598039377917881)
      ·
        refine ⟨6222190316698529533438411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8296253755598039377917881 6222190316698529533438411)
        ·
          refine ⟨9333285475047794300157617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6222190316698529533438411 9333285475047794300157617)
          ·
            refine ⟨6999964106285845725118213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9333285475047794300157617 6999964106285845725118213)
            ·
              refine ⟨1312493269928596073459665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6999964106285845725118213 1312493269928596073459665)
              ·
                refine ⟨984369952446447055094749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312493269928596073459665 984369952446447055094749)
                ·
                  refine ⟨369138732167417645660531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984369952446447055094749 369138732167417645660531)
                  ·
                    rfl

theorem cell21_1617514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_1617514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617514 prefixEnd_1617514 := by exact prefixLift 1617514
  have htrace : WordTrace (prefixWord ++ tailWord_1617514) baseStart_1617514 baseEnd_1617514 := by
    simpa [prefixWord, tailWord_1617514, baseEnd_1617514] using wordTrace_append hprefix tailTrace_1617514
  have hstable : (prefixWord ++ tailWord_1617514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617514).length < 2 ^ (prefixWord ++ tailWord_1617514).sum := by decide
  have hdescent : baseEnd_1617514 < baseStart_1617514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617587 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 4]
def baseStart_1617587 : Nat := 118140960795 + 1617587 * 2 ^ 59
def prefixEnd_1617587 : Nat := 4983230072969 + 3 ^ 40 * 1617587 * 2
def baseEnd_1617587 : Nat := 369155391761985740943715

theorem tailTrace_1617587 : CollatzResearch.WordTrace tailWord_1617587 prefixEnd_1617587 369155391761985740943715 := by
  unfold tailWord_1617587
  simp only [CollatzResearch.WordTrace]
  refine ⟨58998244790766035710379015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39332163193844023806919343 58998244790766035710379015)
  ·
    refine ⟨88497367186149053565568523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58998244790766035710379015 88497367186149053565568523)
    ·
      refine ⟨132746050779223580348352785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88497367186149053565568523 132746050779223580348352785)
      ·
        refine ⟨99559538084417685261264589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132746050779223580348352785 99559538084417685261264589)
        ·
          refine ⟨37334826781656631972974221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99559538084417685261264589 37334826781656631972974221)
          ·
            refine ⟨14000560043121236989865333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37334826781656631972974221 14000560043121236989865333)
            ·
              refine ⟨1312552504042615967799875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14000560043121236989865333 1312552504042615967799875)
              ·
                refine ⟨1968828756063923951699813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312552504042615967799875 1968828756063923951699813)
                ·
                  refine ⟨369155391761985740943715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1968828756063923951699813 369155391761985740943715)
                  ·
                    rfl

theorem cell21_1617587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 4].length) (baseStart_1617587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617587 prefixEnd_1617587 := by exact prefixLift 1617587
  have htrace : WordTrace (prefixWord ++ tailWord_1617587) baseStart_1617587 baseEnd_1617587 := by
    simpa [prefixWord, tailWord_1617587, baseEnd_1617587] using wordTrace_append hprefix tailTrace_1617587
  have hstable : (prefixWord ++ tailWord_1617587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617587).length < 2 ^ (prefixWord ++ tailWord_1617587).sum := by decide
  have hdescent : baseEnd_1617587 < baseStart_1617587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617632 : List Nat := [2, 1, 1, 3, 1, 2, 2, 6, 3]
def baseStart_1617632 : Nat := 118140960795 + 1617632 * 2 ^ 59
def prefixEnd_1617632 : Nat := 4983230072969 + 3 ^ 40 * 1617632 * 2
def baseEnd_1617632 : Nat := 369165661375075662693623

theorem tailTrace_1617632 : CollatzResearch.WordTrace tailWord_1617632 prefixEnd_1617632 369165661375075662693623 := by
  unfold tailWord_1617632
  simp only [CollatzResearch.WordTrace]
  refine ⟨29499943037801504197883575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39333257383735338930511433 29499943037801504197883575)
  ·
    refine ⟨44249914556702256296825363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29499943037801504197883575 44249914556702256296825363)
    ·
      refine ⟨66374871835053384445238045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44249914556702256296825363 66374871835053384445238045)
      ·
        refine ⟨24890576938145019166964267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66374871835053384445238045 24890576938145019166964267)
        ·
          refine ⟨37335865407217528750446401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24890576938145019166964267 37335865407217528750446401)
          ·
            refine ⟨28001899055413146562834801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37335865407217528750446401 28001899055413146562834801)
            ·
              refine ⟨21001424291559859922126101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28001899055413146562834801 21001424291559859922126101)
              ·
                refine ⟨984441763666868433849661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21001424291559859922126101 984441763666868433849661)
                ·
                  refine ⟨369165661375075662693623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984441763666868433849661 369165661375075662693623)
                  ·
                    rfl

theorem cell21_1617632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 3].length) (baseStart_1617632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617632 prefixEnd_1617632 := by exact prefixLift 1617632
  have htrace : WordTrace (prefixWord ++ tailWord_1617632) baseStart_1617632 baseEnd_1617632 := by
    simpa [prefixWord, tailWord_1617632, baseEnd_1617632] using wordTrace_append hprefix tailTrace_1617632
  have hstable : (prefixWord ++ tailWord_1617632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617632).length < 2 ^ (prefixWord ++ tailWord_1617632).sum := by decide
  have hdescent : baseEnd_1617632 < baseStart_1617632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617660 : List Nat := [2, 2, 2, 1, 3, 1, 1, 9]
def baseStart_1617660 : Nat := 118140960795 + 1617660 * 2 ^ 59
def prefixEnd_1617660 : Nat := 4983230072969 + 3 ^ 40 * 1617660 * 2
def baseEnd_1617660 : Nat := 123057350452184612075633

theorem tailTrace_1617660 : CollatzResearch.WordTrace tailWord_1617660 prefixEnd_1617660 123057350452184612075633 := by
  unfold tailWord_1617660
  simp only [CollatzResearch.WordTrace]
  refine ⟨29500453659750784588893217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39333938213001046118524289 29500453659750784588893217)
  ·
    refine ⟨22125340244813088441669913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29500453659750784588893217 22125340244813088441669913)
    ·
      refine ⟨16594005183609816331252435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22125340244813088441669913 16594005183609816331252435)
      ·
        refine ⟨24891007775414724496878653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16594005183609816331252435 24891007775414724496878653)
        ·
          refine ⟨9334127915780521686329495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24891007775414724496878653 9334127915780521686329495)
          ·
            refine ⟨14001191873670782529494243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9334127915780521686329495 14001191873670782529494243)
            ·
              refine ⟨21001787810506173794241365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14001191873670782529494243 21001787810506173794241365)
              ·
                refine ⟨123057350452184612075633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21001787810506173794241365 123057350452184612075633)
                ·
                  rfl

theorem cell21_1617660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_1617660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617660 prefixEnd_1617660 := by exact prefixLift 1617660
  have htrace : WordTrace (prefixWord ++ tailWord_1617660) baseStart_1617660 baseEnd_1617660 := by
    simpa [prefixWord, tailWord_1617660, baseEnd_1617660] using wordTrace_append hprefix tailTrace_1617660
  have hstable : (prefixWord ++ tailWord_1617660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617660).length < 2 ^ (prefixWord ++ tailWord_1617660).sum := by decide
  have hdescent : baseEnd_1617660 < baseStart_1617660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617725 : List Nat := [1, 4, 1, 4, 1, 1, 1, 5, 3]
def baseStart_1617725 : Nat := 118140960795 + 1617725 * 2 ^ 59
def prefixEnd_1617725 : Nat := 4983230072969 + 3 ^ 40 * 1617725 * 2
def baseEnd_1617725 : Nat := 369186885242128167643433

theorem tailTrace_1617725 : CollatzResearch.WordTrace tailWord_1617725 prefixEnd_1617725 369186885242128167643433 := by
  unfold tailWord_1617725
  simp only [CollatzResearch.WordTrace]
  refine ⟨59003278064266085278902629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39335518709510723519268419 59003278064266085278902629)
  ·
    refine ⟨11063114637049890989794243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59003278064266085278902629 11063114637049890989794243)
    ·
      refine ⟨16594671955574836484691365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11063114637049890989794243 16594671955574836484691365)
      ·
        refine ⟨3111500991670281840879631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16594671955574836484691365 3111500991670281840879631)
        ·
          refine ⟨4667251487505422761319447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3111500991670281840879631 4667251487505422761319447)
          ·
            refine ⟨7000877231258134141979171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4667251487505422761319447 7000877231258134141979171)
            ·
              refine ⟨10501315846887201212968757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7000877231258134141979171 10501315846887201212968757)
              ·
                refine ⟨984498360645675113715821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10501315846887201212968757 984498360645675113715821)
                ·
                  refine ⟨369186885242128167643433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984498360645675113715821 369186885242128167643433)
                  ·
                    rfl

theorem cell21_1617725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_1617725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617725 prefixEnd_1617725 := by exact prefixLift 1617725
  have htrace : WordTrace (prefixWord ++ tailWord_1617725) baseStart_1617725 baseEnd_1617725 := by
    simpa [prefixWord, tailWord_1617725, baseEnd_1617725] using wordTrace_append hprefix tailTrace_1617725
  have hstable : (prefixWord ++ tailWord_1617725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617725).length < 2 ^ (prefixWord ++ tailWord_1617725).sum := by decide
  have hdescent : baseEnd_1617725 < baseStart_1617725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617736 : List Nat := [2, 1, 3, 1, 1, 5, 8]
def baseStart_1617736 : Nat := 118140960795 + 1617736 * 2 ^ 59
def prefixEnd_1617736 : Nat := 4983230072969 + 3 ^ 40 * 1617736 * 2
def baseEnd_1617736 : Nat := 41021043954666065884453

theorem tailTrace_1617736 : CollatzResearch.WordTrace tailWord_1617736 prefixEnd_1617736 41021043954666065884453 := by
  unfold tailWord_1617736
  simp only [CollatzResearch.WordTrace]
  refine ⟨29501839633613117078776531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39335786178150822771702041 29501839633613117078776531)
  ·
    refine ⟨44252759450419675618164797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29501839633613117078776531 44252759450419675618164797)
    ·
      refine ⟨16594784793907378356811799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44252759450419675618164797 16594784793907378356811799)
      ·
        refine ⟨24892177190861067535217699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16594784793907378356811799 24892177190861067535217699)
        ·
          refine ⟨37338265786291601302826549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24892177190861067535217699 37338265786291601302826549)
          ·
            refine ⟨3500462417464837622139989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37338265786291601302826549 3500462417464837622139989)
            ·
              refine ⟨41021043954666065884453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3500462417464837622139989 41021043954666065884453)
              ·
                rfl

theorem cell21_1617736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 8].length) (baseStart_1617736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617736 prefixEnd_1617736 := by exact prefixLift 1617736
  have htrace : WordTrace (prefixWord ++ tailWord_1617736) baseStart_1617736 baseEnd_1617736 := by
    simpa [prefixWord, tailWord_1617736, baseEnd_1617736] using wordTrace_append hprefix tailTrace_1617736
  have hstable : (prefixWord ++ tailWord_1617736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617736).length < 2 ^ (prefixWord ++ tailWord_1617736).sum := by decide
  have hdescent : baseEnd_1617736 < baseStart_1617736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617767 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 5]
def baseStart_1617767 : Nat := 118140960795 + 1617767 * 2 ^ 59
def prefixEnd_1617767 : Nat := 4983230072969 + 3 ^ 40 * 1617767 * 2
def baseEnd_1617767 : Nat := 369196470214345427943347

theorem tailTrace_1617767 : CollatzResearch.WordTrace tailWord_1617767 prefixEnd_1617767 369196470214345427943347 := by
  unfold tailWord_1617767
  simp only [CollatzResearch.WordTrace]
  refine ⟨59004809930113926451931555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39336539953409284301287703 59004809930113926451931555)
  ·
    refine ⟨88507214895170889677897333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59004809930113926451931555 88507214895170889677897333)
    ·
      refine ⟨8297551396422270907302875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88507214895170889677897333 8297551396422270907302875)
      ·
        refine ⟨12446327094633406360954313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8297551396422270907302875 12446327094633406360954313)
        ·
          refine ⟨9334745320975054770715735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12446327094633406360954313 9334745320975054770715735)
          ·
            refine ⟨14002117981462582156073603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9334745320975054770715735 14002117981462582156073603)
            ·
              refine ⟨21003176972193873234110405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14002117981462582156073603 21003176972193873234110405)
              ·
                refine ⟨3938095682286351231395701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21003176972193873234110405 3938095682286351231395701)
                ·
                  refine ⟨369196470214345427943347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3938095682286351231395701 369196470214345427943347)
                  ·
                    rfl

theorem cell21_1617767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_1617767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617767 prefixEnd_1617767 := by exact prefixLift 1617767
  have htrace : WordTrace (prefixWord ++ tailWord_1617767) baseStart_1617767 baseEnd_1617767 := by
    simpa [prefixWord, tailWord_1617767, baseEnd_1617767] using wordTrace_append hprefix tailTrace_1617767
  have hstable : (prefixWord ++ tailWord_1617767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617767).length < 2 ^ (prefixWord ++ tailWord_1617767).sum := by decide
  have hdescent : baseEnd_1617767 < baseStart_1617767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617770 : List Nat := [3, 1, 3, 4, 1, 1, 1, 7]
def baseStart_1617770 : Nat := 118140960795 + 1617770 * 2 ^ 59
def prefixEnd_1617770 : Nat := 4983230072969 + 3 ^ 40 * 1617770 * 2
def baseEnd_1617770 : Nat := 123065718285072696464447

theorem tailTrace_1617770 : CollatzResearch.WordTrace tailWord_1617770 prefixEnd_1617770 123065718285072696464447 := by
  unfold tailWord_1617770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14751229837275764491072691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39336612899402038642860509 14751229837275764491072691)
  ·
    refine ⟨22126844755913646736609037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14751229837275764491072691 22126844755913646736609037)
    ·
      refine ⟨8297566783467617526228389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22126844755913646736609037 8297566783467617526228389)
      ·
        refine ⟨1555793771900178286167823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8297566783467617526228389 1555793771900178286167823)
        ·
          refine ⟨2333690657850267429251735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555793771900178286167823 2333690657850267429251735)
          ·
            refine ⟨3500535986775401143877603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333690657850267429251735 3500535986775401143877603)
            ·
              refine ⟨5250803980163101715816405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500535986775401143877603 5250803980163101715816405)
              ·
                refine ⟨123065718285072696464447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5250803980163101715816405 123065718285072696464447)
                ·
                  rfl

theorem cell21_1617770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_1617770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617770 prefixEnd_1617770 := by exact prefixLift 1617770
  have htrace : WordTrace (prefixWord ++ tailWord_1617770) baseStart_1617770 baseEnd_1617770 := by
    simpa [prefixWord, tailWord_1617770, baseEnd_1617770] using wordTrace_append hprefix tailTrace_1617770
  have hstable : (prefixWord ++ tailWord_1617770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617770).length < 2 ^ (prefixWord ++ tailWord_1617770).sum := by decide
  have hdescent : baseEnd_1617770 < baseStart_1617770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617801 : List Nat := [1, 2, 1, 1, 5, 1, 5, 2, 3]
def baseStart_1617801 : Nat := 118140960795 + 1617801 * 2 ^ 59
def prefixEnd_1617801 : Nat := 4983230072969 + 3 ^ 40 * 1617801 * 2
def baseEnd_1617801 : Nat := 369204229477568924376611

theorem tailTrace_1617801 : CollatzResearch.WordTrace tailWord_1617801 prefixEnd_1617801 369204229477568924376611 := by
  unfold tailWord_1617801
  simp only [CollatzResearch.WordTrace]
  refine ⟨59006050011990750258669257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39337366674660500172446171 59006050011990750258669257)
  ·
    refine ⟨44254537508993062694001943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59006050011990750258669257 44254537508993062694001943)
    ·
      refine ⟨66381806263489594041002915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44254537508993062694001943 66381806263489594041002915)
      ·
        refine ⟨99572709395234391061504373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66381806263489594041002915 99572709395234391061504373)
        ·
          refine ⟨9334941505803224162016035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99572709395234391061504373 9334941505803224162016035)
          ·
            refine ⟨14002412258704836243024053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9334941505803224162016035 14002412258704836243024053)
            ·
              refine ⟨1312726149253578397783505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14002412258704836243024053 1312726149253578397783505)
              ·
                refine ⟨984544611940183798337629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312726149253578397783505 984544611940183798337629)
                ·
                  refine ⟨369204229477568924376611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984544611940183798337629 369204229477568924376611)
                  ·
                    rfl

theorem cell21_1617801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 3].length) (baseStart_1617801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617801 prefixEnd_1617801 := by exact prefixLift 1617801
  have htrace : WordTrace (prefixWord ++ tailWord_1617801) baseStart_1617801 baseEnd_1617801 := by
    simpa [prefixWord, tailWord_1617801, baseEnd_1617801] using wordTrace_append hprefix tailTrace_1617801
  have hstable : (prefixWord ++ tailWord_1617801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617801).length < 2 ^ (prefixWord ++ tailWord_1617801).sum := by decide
  have hdescent : baseEnd_1617801 < baseStart_1617801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617815 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 4]
def baseStart_1617815 : Nat := 118140960795 + 1617815 * 2 ^ 59
def prefixEnd_1617815 : Nat := 4983230072969 + 3 ^ 40 * 1617815 * 2
def baseEnd_1617815 : Nat := 369207424468308011143249

theorem tailTrace_1617815 : CollatzResearch.WordTrace tailWord_1617815 prefixEnd_1617815 369207424468308011143249 := by
  unfold tailWord_1617815
  simp only [CollatzResearch.WordTrace]
  refine ⟨59006560633940030649678899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39337707089293353766452599 59006560633940030649678899)
  ·
    refine ⟨88509840950910045974518349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59006560633940030649678899 88509840950910045974518349)
    ·
      refine ⟨33191190356591267240444381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88509840950910045974518349 33191190356591267240444381)
      ·
        refine ⟨12446696383721725215166643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33191190356591267240444381 12446696383721725215166643)
        ·
          refine ⟨18670044575582587822749965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12446696383721725215166643 18670044575582587822749965)
          ·
            refine ⟨7001266715843470433531237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18670044575582587822749965 7001266715843470433531237)
            ·
              refine ⟨1312737509220650706287107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7001266715843470433531237 1312737509220650706287107)
              ·
                refine ⟨1969106263830976059430661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312737509220650706287107 1969106263830976059430661)
                ·
                  refine ⟨369207424468308011143249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1969106263830976059430661 369207424468308011143249)
                  ·
                    rfl

theorem cell21_1617815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 4].length) (baseStart_1617815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617815 prefixEnd_1617815 := by exact prefixLift 1617815
  have htrace : WordTrace (prefixWord ++ tailWord_1617815) baseStart_1617815 baseEnd_1617815 := by
    simpa [prefixWord, tailWord_1617815, baseEnd_1617815] using wordTrace_append hprefix tailTrace_1617815
  have hstable : (prefixWord ++ tailWord_1617815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617815).length < 2 ^ (prefixWord ++ tailWord_1617815).sum := by decide
  have hdescent : baseEnd_1617815 < baseStart_1617815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617852 : List Nat := [2, 2, 2, 5, 2, 1, 2, 2, 3]
def baseStart_1617852 : Nat := 118140960795 + 1617852 * 2 ^ 59
def prefixEnd_1617852 : Nat := 4983230072969 + 3 ^ 40 * 1617852 * 2
def baseEnd_1617852 : Nat := 369215868372404169026507

theorem tailTrace_1617852 : CollatzResearch.WordTrace tailWord_1617852 prefixEnd_1617852 369215868372404169026507 := by
  unfold tailWord_1617852
  simp only [CollatzResearch.WordTrace]
  refine ⟨29503955067402992984387905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39338606756537323979183873 29503955067402992984387905)
  ·
    refine ⟨22127966300552244738290929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29503955067402992984387905 22127966300552244738290929)
    ·
      refine ⟨16595974725414183553718197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22127966300552244738290929 16595974725414183553718197)
      ·
        refine ⟨1555872630507579708161081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16595974725414183553718197 1555872630507579708161081)
        ·
          refine ⟨1166904472880684781120811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1555872630507579708161081 1166904472880684781120811)
          ·
            refine ⟨1750356709321027171681217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166904472880684781120811 1750356709321027171681217)
            ·
              refine ⟨1312767531990770378760913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750356709321027171681217 1312767531990770378760913)
              ·
                refine ⟨984575648993077784070685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312767531990770378760913 984575648993077784070685)
                ·
                  refine ⟨369215868372404169026507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984575648993077784070685 369215868372404169026507)
                  ·
                    rfl

theorem cell21_1617852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_1617852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1617852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1617852 prefixEnd_1617852 := by exact prefixLift 1617852
  have htrace : WordTrace (prefixWord ++ tailWord_1617852) baseStart_1617852 baseEnd_1617852 := by
    simpa [prefixWord, tailWord_1617852, baseEnd_1617852] using wordTrace_append hprefix tailTrace_1617852
  have hstable : (prefixWord ++ tailWord_1617852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617852).length < 2 ^ (prefixWord ++ tailWord_1617852).sum := by decide
  have hdescent : baseEnd_1617852 < baseStart_1617852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618085 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 6]
def baseStart_1618085 : Nat := 118140960795 + 1618085 * 2 ^ 59
def prefixEnd_1618085 : Nat := 4983230072969 + 3 ^ 40 * 1618085 * 2
def baseEnd_1618085 : Nat := 369269042146847541642697

theorem tailTrace_1618085 : CollatzResearch.WordTrace tailWord_1618085 prefixEnd_1618085 369269042146847541642697 := by
  unfold tailWord_1618085
  simp only [CollatzResearch.WordTrace]
  refine ⟨59016408342961866762007709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39344272228641244508005139 59016408342961866762007709)
  ·
    refine ⟨22131153128610700035752891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59016408342961866762007709 22131153128610700035752891)
    ·
      refine ⟨33196729692916050053629337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22131153128610700035752891 33196729692916050053629337)
      ·
        refine ⟨24897547269687037540222003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33196729692916050053629337 24897547269687037540222003)
        ·
          refine ⟨37346320904530556310333005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24897547269687037540222003 37346320904530556310333005)
          ·
            refine ⟨14004870339198958616374877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37346320904530556310333005 14004870339198958616374877)
            ·
              refine ⟨5251826377199609481140579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14004870339198958616374877 5251826377199609481140579)
              ·
                refine ⟨7877739565799414221710869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251826377199609481140579 7877739565799414221710869)
                ·
                  refine ⟨369269042146847541642697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7877739565799414221710869 369269042146847541642697)
                  ·
                    rfl

theorem cell21_1618085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_1618085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618085 prefixEnd_1618085 := by exact prefixLift 1618085
  have htrace : WordTrace (prefixWord ++ tailWord_1618085) baseStart_1618085 baseEnd_1618085 := by
    simpa [prefixWord, tailWord_1618085, baseEnd_1618085] using wordTrace_append hprefix tailTrace_1618085
  have hstable : (prefixWord ++ tailWord_1618085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618085).length < 2 ^ (prefixWord ++ tailWord_1618085).sum := by decide
  have hdescent : baseEnd_1618085 < baseStart_1618085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618099 : List Nat := [1, 1, 1, 2, 3, 2, 1, 10]
def baseStart_1618099 : Nat := 118140960795 + 1618099 * 2 ^ 59
def prefixEnd_1618099 : Nat := 4983230072969 + 3 ^ 40 * 1618099 * 2
def baseEnd_1618099 : Nat := 123090745712528876136445

theorem tailTrace_1618099 : CollatzResearch.WordTrace tailWord_1618099 prefixEnd_1618099 123090745712528876136445 := by
  unfold tailWord_1618099
  simp only [CollatzResearch.WordTrace]
  refine ⟨59016918964911147153017351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39344612643274098102011567 59016918964911147153017351)
  ·
    refine ⟨88525378447366720729526027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59016918964911147153017351 88525378447366720729526027)
    ·
      refine ⟨132788067671050081094289041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88525378447366720729526027 132788067671050081094289041)
      ·
        refine ⟨99591050753287560820716781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132788067671050081094289041 99591050753287560820716781)
        ·
          refine ⟨37346644032482835307768793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99591050753287560820716781 37346644032482835307768793)
          ·
            refine ⟨28009983024362126480826595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37346644032482835307768793 28009983024362126480826595)
            ·
              refine ⟨42014974536543189721239893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28009983024362126480826595 42014974536543189721239893)
              ·
                refine ⟨123090745712528876136445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42014974536543189721239893 123090745712528876136445)
                ·
                  rfl

theorem cell21_1618099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 10].length) (baseStart_1618099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618099 prefixEnd_1618099 := by exact prefixLift 1618099
  have htrace : WordTrace (prefixWord ++ tailWord_1618099) baseStart_1618099 baseEnd_1618099 := by
    simpa [prefixWord, tailWord_1618099, baseEnd_1618099] using wordTrace_append hprefix tailTrace_1618099
  have hstable : (prefixWord ++ tailWord_1618099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618099).length < 2 ^ (prefixWord ++ tailWord_1618099).sum := by decide
  have hdescent : baseEnd_1618099 < baseStart_1618099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618133 : List Nat := [1, 3, 2, 4, 2, 2, 7]
def baseStart_1618133 : Nat := 118140960795 + 1618133 * 2 ^ 59
def prefixEnd_1618133 : Nat := 4983230072969 + 3 ^ 40 * 1618133 * 2
def baseEnd_1618133 : Nat := 41031110711201124982511

theorem tailTrace_1618133 : CollatzResearch.WordTrace tailWord_1618133 prefixEnd_1618133 41031110711201124982511 := by
  unfold tailWord_1618133
  simp only [CollatzResearch.WordTrace]
  refine ⟨59018159046787970959755053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39345439364525313973170035 59018159046787970959755053)
  ·
    refine ⟨22131809642545489109908145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59018159046787970959755053 22131809642545489109908145)
    ·
      refine ⟨16598857231909116832431109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22131809642545489109908145 16598857231909116832431109)
      ·
        refine ⟨3112285730982959406080833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16598857231909116832431109 3112285730982959406080833)
        ·
          refine ⟨2334214298237219554560625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3112285730982959406080833 2334214298237219554560625)
          ·
            refine ⟨1750660723677914665920469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2334214298237219554560625 1750660723677914665920469)
            ·
              refine ⟨41031110711201124982511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1750660723677914665920469 41031110711201124982511)
              ·
                rfl

theorem cell21_1618133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 7].length) (baseStart_1618133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618133 prefixEnd_1618133 := by exact prefixLift 1618133
  have htrace : WordTrace (prefixWord ++ tailWord_1618133) baseStart_1618133 baseEnd_1618133 := by
    simpa [prefixWord, tailWord_1618133, baseEnd_1618133] using wordTrace_append hprefix tailTrace_1618133
  have hstable : (prefixWord ++ tailWord_1618133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618133).length < 2 ^ (prefixWord ++ tailWord_1618133).sum := by decide
  have hdescent : baseEnd_1618133 < baseStart_1618133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618175 : List Nat := [1, 1, 2, 2, 1, 4, 1, 9]
def baseStart_1618175 : Nat := 118140960795 + 1618175 * 2 ^ 59
def prefixEnd_1618175 : Nat := 4983230072969 + 3 ^ 40 * 1618175 * 2
def baseEnd_1618175 : Nat := 123096527124342461714171

theorem tailTrace_1618175 : CollatzResearch.WordTrace tailWord_1618175 prefixEnd_1618175 123096527124342461714171 := by
  unfold tailWord_1618175
  simp only [CollatzResearch.WordTrace]
  refine ⟨59019690912635812132783979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39346460608423874755189319 59019690912635812132783979)
  ·
    refine ⟨88529536368953718199175969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59019690912635812132783979 88529536368953718199175969)
    ·
      refine ⟨66397152276715288649381977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88529536368953718199175969 66397152276715288649381977)
      ·
        refine ⟨49797864207536466487036483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66397152276715288649381977 49797864207536466487036483)
        ·
          refine ⟨74696796311304699730554725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49797864207536466487036483 74696796311304699730554725)
          ·
            refine ⟨14005649308369631199479011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74696796311304699730554725 14005649308369631199479011)
            ·
              refine ⟨21008473962554446799218517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14005649308369631199479011 21008473962554446799218517)
              ·
                refine ⟨123096527124342461714171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21008473962554446799218517 123096527124342461714171)
                ·
                  rfl

theorem cell21_1618175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 9].length) (baseStart_1618175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618175 prefixEnd_1618175 := by exact prefixLift 1618175
  have htrace : WordTrace (prefixWord ++ tailWord_1618175) baseStart_1618175 baseEnd_1618175 := by
    simpa [prefixWord, tailWord_1618175, baseEnd_1618175] using wordTrace_append hprefix tailTrace_1618175
  have hstable : (prefixWord ++ tailWord_1618175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618175).length < 2 ^ (prefixWord ++ tailWord_1618175).sum := by decide
  have hdescent : baseEnd_1618175 < baseStart_1618175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618313 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 6]
def baseStart_1618313 : Nat := 118140960795 + 1618313 * 2 ^ 59
def prefixEnd_1618313 : Nat := 4983230072969 + 3 ^ 40 * 1618313 * 2
def baseEnd_1618313 : Nat := 369321074853169811842231

theorem tailTrace_1618313 : CollatzResearch.WordTrace tailWord_1618313 prefixEnd_1618313 369321074853169811842231 := by
  unfold tailWord_1618313
  simp only [CollatzResearch.WordTrace]
  refine ⟨59024724186135861701307593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39349816124090574467538395 59024724186135861701307593)
  ·
    refine ⟨44268543139601896275980695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59024724186135861701307593 44268543139601896275980695)
    ·
      refine ⟨66402814709402844413971043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44268543139601896275980695 66402814709402844413971043)
      ·
        refine ⟨99604222064104266620956565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66402814709402844413971043 99604222064104266620956565)
        ·
          refine ⟨4668947909254887497857339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99604222064104266620956565 4668947909254887497857339)
          ·
            refine ⟨7003421863882331246786009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668947909254887497857339 7003421863882331246786009)
            ·
              refine ⟨5252566397911748435089507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7003421863882331246786009 5252566397911748435089507)
              ·
                refine ⟨7878849596867622652634261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252566397911748435089507 7878849596867622652634261)
                ·
                  refine ⟨369321074853169811842231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7878849596867622652634261 369321074853169811842231)
                  ·
                    rfl

theorem cell21_1618313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_1618313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618313 prefixEnd_1618313 := by exact prefixLift 1618313
  have htrace : WordTrace (prefixWord ++ tailWord_1618313) baseStart_1618313 baseEnd_1618313 := by
    simpa [prefixWord, tailWord_1618313, baseEnd_1618313] using wordTrace_append hprefix tailTrace_1618313
  have hstable : (prefixWord ++ tailWord_1618313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618313).length < 2 ^ (prefixWord ++ tailWord_1618313).sum := by decide
  have hdescent : baseEnd_1618313 < baseStart_1618313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618327 : List Nat := [1, 1, 3, 3, 1, 1, 3, 8]
def baseStart_1618327 : Nat := 118140960795 + 1618327 * 2 ^ 59
def prefixEnd_1618327 : Nat := 4983230072969 + 3 ^ 40 * 1618327 * 2
def baseEnd_1618327 : Nat := 123108089947969632869623

theorem tailTrace_1618327 : CollatzResearch.WordTrace tailWord_1618327 prefixEnd_1618327 123108089947969632869623 := by
  unfold tailWord_1618327
  simp only [CollatzResearch.WordTrace]
  refine ⟨59025234808085142092317235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39350156538723428061544823 59025234808085142092317235)
  ·
    refine ⟨88537852212127713138475853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59025234808085142092317235 88537852212127713138475853)
    ·
      refine ⟨33201694579547892426928445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88537852212127713138475853 33201694579547892426928445)
      ·
        refine ⟨12450635467330459660098167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33201694579547892426928445 12450635467330459660098167)
        ·
          refine ⟨18675953200995689490147251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12450635467330459660098167 18675953200995689490147251)
          ·
            refine ⟨28013929801493534235220877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18675953200995689490147251 28013929801493534235220877)
            ·
              refine ⟨10505223675560075338207829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28013929801493534235220877 10505223675560075338207829)
              ·
                refine ⟨123108089947969632869623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10505223675560075338207829 123108089947969632869623)
                ·
                  rfl

theorem cell21_1618327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 8].length) (baseStart_1618327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618327 prefixEnd_1618327 := by exact prefixLift 1618327
  have htrace : WordTrace (prefixWord ++ tailWord_1618327) baseStart_1618327 baseEnd_1618327 := by
    simpa [prefixWord, tailWord_1618327, baseEnd_1618327] using wordTrace_append hprefix tailTrace_1618327
  have hstable : (prefixWord ++ tailWord_1618327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618327).length < 2 ^ (prefixWord ++ tailWord_1618327).sum := by decide
  have hdescent : baseEnd_1618327 < baseStart_1618327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618330 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_1618330 : Nat := 118140960795 + 1618330 * 2 ^ 59
def prefixEnd_1618330 : Nat := 4983230072969 + 3 ^ 40 * 1618330 * 2
def baseEnd_1618330 : Nat := 369324954484781560058863

theorem tailTrace_1618330 : CollatzResearch.WordTrace tailWord_1618330 prefixEnd_1618330 369324954484781560058863 := by
  unfold tailWord_1618330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14756336056768568401169111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39350229484716182403117629 14756336056768568401169111)
  ·
    refine ⟨22134504085152852601753667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14756336056768568401169111 22134504085152852601753667)
    ·
      refine ⟨33201756127729278902630501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22134504085152852601753667 33201756127729278902630501)
      ·
        refine ⟨6225329273949239794243219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33201756127729278902630501 6225329273949239794243219)
        ·
          refine ⟨9337993910923859691364829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6225329273949239794243219 9337993910923859691364829)
          ·
            refine ⟨3501747716596447384261811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9337993910923859691364829 3501747716596447384261811)
            ·
              refine ⟨5252621574894671076392717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501747716596447384261811 5252621574894671076392717)
              ·
                refine ⟨1969733090585501653647269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5252621574894671076392717 1969733090585501653647269)
                ·
                  refine ⟨369324954484781560058863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1969733090585501653647269 369324954484781560058863)
                  ·
                    rfl

theorem cell21_1618330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_1618330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618330 prefixEnd_1618330 := by exact prefixLift 1618330
  have htrace : WordTrace (prefixWord ++ tailWord_1618330) baseStart_1618330 baseEnd_1618330 := by
    simpa [prefixWord, tailWord_1618330, baseEnd_1618330] using wordTrace_append hprefix tailTrace_1618330
  have hstable : (prefixWord ++ tailWord_1618330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618330).length < 2 ^ (prefixWord ++ tailWord_1618330).sum := by decide
  have hdescent : baseEnd_1618330 < baseStart_1618330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618510 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1618510 : Nat := 118140960795 + 1618510 * 2 ^ 59
def prefixEnd_1618510 : Nat := 4983230072969 + 3 ^ 40 * 1618510 * 2
def baseEnd_1618510 : Nat := 369366032937141247058495

theorem tailTrace_1618510 : CollatzResearch.WordTrace tailWord_1618510 prefixEnd_1618510 369366032937141247058495 := by
  unfold tailWord_1618510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378988670802770543278623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39354606244281442897485989 7378988670802770543278623)
  ·
    refine ⟨11068483006204155814917935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7378988670802770543278623 11068483006204155814917935)
    ·
      refine ⟨16602724509306233722376903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11068483006204155814917935 16602724509306233722376903)
      ·
        refine ⟨24904086763959350583565355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16602724509306233722376903 24904086763959350583565355)
        ·
          refine ⟨37356130145939025875348033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24904086763959350583565355 37356130145939025875348033)
          ·
            refine ⟨28017097609454269406511025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37356130145939025875348033 28017097609454269406511025)
            ·
              refine ⟨21012823207090702054883269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28017097609454269406511025 21012823207090702054883269)
              ·
                refine ⟨3939904351329506635290613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21012823207090702054883269 3939904351329506635290613)
                ·
                  refine ⟨369366032937141247058495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3939904351329506635290613 369366032937141247058495)
                  ·
                    rfl

theorem cell21_1618510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1618510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618510 prefixEnd_1618510 := by exact prefixLift 1618510
  have htrace : WordTrace (prefixWord ++ tailWord_1618510) baseStart_1618510 baseEnd_1618510 := by
    simpa [prefixWord, tailWord_1618510, baseEnd_1618510] using wordTrace_append hprefix tailTrace_1618510
  have hstable : (prefixWord ++ tailWord_1618510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618510).length < 2 ^ (prefixWord ++ tailWord_1618510).sum := by decide
  have hdescent : baseEnd_1618510 < baseStart_1618510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618544 : List Nat := [2, 1, 1, 1, 7, 1, 1, 4, 3]
def baseStart_1618544 : Nat := 118140960795 + 1618544 * 2 ^ 59
def prefixEnd_1618544 : Nat := 4983230072969 + 3 ^ 40 * 1618544 * 2
def baseEnd_1618544 : Nat := 369373792200364743491759

theorem tailTrace_1618544 : CollatzResearch.WordTrace tailWord_1618544 prefixEnd_1618544 369373792200364743491759 := by
  unfold tailWord_1618544
  simp only [CollatzResearch.WordTrace]
  refine ⟨29516574724149494076483343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39355432965532658768644457 29516574724149494076483343)
  ·
    refine ⟨44274862086224241114725015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29516574724149494076483343 44274862086224241114725015)
    ·
      refine ⟨66412293129336361672087523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44274862086224241114725015 66412293129336361672087523)
      ·
        refine ⟨99618439694004542508131285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66412293129336361672087523 99618439694004542508131285)
        ·
          refine ⟨2334807180328231465034327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 99618439694004542508131285 2334807180328231465034327)
          ·
            refine ⟨3502210770492347197551491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334807180328231465034327 3502210770492347197551491)
            ·
              refine ⟨5253316155738520796327237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502210770492347197551491 5253316155738520796327237)
              ·
                refine ⟨984996779200972649311357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5253316155738520796327237 984996779200972649311357)
                ·
                  refine ⟨369373792200364743491759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984996779200972649311357 369373792200364743491759)
                  ·
                    rfl

theorem cell21_1618544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 3].length) (baseStart_1618544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618544 prefixEnd_1618544 := by exact prefixLift 1618544
  have htrace : WordTrace (prefixWord ++ tailWord_1618544) baseStart_1618544 baseEnd_1618544 := by
    simpa [prefixWord, tailWord_1618544, baseEnd_1618544] using wordTrace_append hprefix tailTrace_1618544
  have hstable : (prefixWord ++ tailWord_1618544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618544).length < 2 ^ (prefixWord ++ tailWord_1618544).sum := by decide
  have hdescent : baseEnd_1618544 < baseStart_1618544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618738 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_1618738 : Nat := 118140960795 + 1618738 * 2 ^ 59
def prefixEnd_1618738 : Nat := 4983230072969 + 3 ^ 40 * 1618738 * 2
def baseEnd_1618738 : Nat := 369418065643463517258029

theorem tailTrace_1618738 : CollatzResearch.WordTrace tailWord_1618738 prefixEnd_1618738 369418065643463517258029 := by
  unfold tailWord_1618738
  simp only [CollatzResearch.WordTrace]
  refine ⟨14760056302399039821382217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39360150139730772857019245 14760056302399039821382217)
  ·
    refine ⟨11070042226799279866036663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14760056302399039821382217 11070042226799279866036663)
    ·
      refine ⟨16605063340198919799054995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11070042226799279866036663 16605063340198919799054995)
      ·
        refine ⟨24907595010298379698582493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16605063340198919799054995 24907595010298379698582493)
        ·
          refine ⟨9340348128861892386968435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24907595010298379698582493 9340348128861892386968435)
          ·
            refine ⟨14010522193292838580452653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9340348128861892386968435 14010522193292838580452653)
            ·
              refine ⟨5253945822484814467669745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14010522193292838580452653 5253945822484814467669745)
              ·
                refine ⟨3940459366863610850752309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5253945822484814467669745 3940459366863610850752309)
                ·
                  refine ⟨369418065643463517258029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3940459366863610850752309 369418065643463517258029)
                  ·
                    rfl

theorem cell21_1618738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_1618738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618738 prefixEnd_1618738 := by exact prefixLift 1618738
  have htrace : WordTrace (prefixWord ++ tailWord_1618738) baseStart_1618738 baseEnd_1618738 := by
    simpa [prefixWord, tailWord_1618738, baseEnd_1618738] using wordTrace_append hprefix tailTrace_1618738
  have hstable : (prefixWord ++ tailWord_1618738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618738).length < 2 ^ (prefixWord ++ tailWord_1618738).sum := by decide
  have hdescent : baseEnd_1618738 < baseStart_1618738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618755 : List Nat := [1, 1, 1, 3, 1, 4, 4, 3, 3]
def baseStart_1618755 : Nat := 118140960795 + 1618755 * 2 ^ 59
def prefixEnd_1618755 : Nat := 4983230072969 + 3 ^ 40 * 1618755 * 2
def baseEnd_1618755 : Nat := 369421945275075265474661

theorem tailTrace_1618755 : CollatzResearch.WordTrace tailWord_1618755 prefixEnd_1618755 369421945275075265474661 := by
  unfold tailWord_1618755
  simp only [CollatzResearch.WordTrace]
  refine ⟨59040845250534571188897719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39360563500356380792598479 59040845250534571188897719)
  ·
    refine ⟨88561267875801856783346579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59040845250534571188897719 88561267875801856783346579)
    ·
      refine ⟨132841901813702785175019869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88561267875801856783346579 132841901813702785175019869)
      ·
        refine ⟨49815713180138544440632451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132841901813702785175019869 49815713180138544440632451)
        ·
          refine ⟨74723569770207816660948677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49815713180138544440632451 74723569770207816660948677)
          ·
            refine ⟨14010669331913965623927877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74723569770207816660948677 14010669331913965623927877)
            ·
              refine ⟨2627000499733868554486477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14010669331913965623927877 2627000499733868554486477)
              ·
                refine ⟨985125187400200707932429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2627000499733868554486477 985125187400200707932429)
                ·
                  refine ⟨369421945275075265474661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 985125187400200707932429 369421945275075265474661)
                  ·
                    rfl

theorem cell21_1618755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 3].length) (baseStart_1618755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618755 prefixEnd_1618755 := by exact prefixLift 1618755
  have htrace : WordTrace (prefixWord ++ tailWord_1618755) baseStart_1618755 baseEnd_1618755 := by
    simpa [prefixWord, tailWord_1618755, baseEnd_1618755] using wordTrace_append hprefix tailTrace_1618755
  have hstable : (prefixWord ++ tailWord_1618755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618755).length < 2 ^ (prefixWord ++ tailWord_1618755).sum := by decide
  have hdescent : baseEnd_1618755 < baseStart_1618755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618769 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 6]
def baseStart_1618769 : Nat := 118140960795 + 1618769 * 2 ^ 59
def prefixEnd_1618769 : Nat := 4983230072969 + 3 ^ 40 * 1618769 * 2
def baseEnd_1618769 : Nat := 369425140265814352241299

theorem tailTrace_1618769 : CollatzResearch.WordTrace tailWord_1618769 prefixEnd_1618769 369425140265814352241299 := by
  unfold tailWord_1618769
  simp only [CollatzResearch.WordTrace]
  refine ⟨59041355872483851579907361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39360903914989234386604907 59041355872483851579907361)
  ·
    refine ⟨44281016904362888684930521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59041355872483851579907361 44281016904362888684930521)
    ·
      refine ⟨33210762678272166513697891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44281016904362888684930521 33210762678272166513697891)
      ·
        refine ⟨49816144017408249770546837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33210762678272166513697891 49816144017408249770546837)
        ·
          refine ⟨2335131750816011707994383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49816144017408249770546837 2335131750816011707994383)
          ·
            refine ⟨3502697626224017561991575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335131750816011707994383 3502697626224017561991575)
            ·
              refine ⟨5254046439336026342987363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502697626224017561991575 5254046439336026342987363)
              ·
                refine ⟨7881069659004039514481045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5254046439336026342987363 7881069659004039514481045)
                ·
                  refine ⟨369425140265814352241299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7881069659004039514481045 369425140265814352241299)
                  ·
                    rfl

theorem cell21_1618769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_1618769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618769 prefixEnd_1618769 := by exact prefixLift 1618769
  have htrace : WordTrace (prefixWord ++ tailWord_1618769) baseStart_1618769 baseEnd_1618769 := by
    simpa [prefixWord, tailWord_1618769, baseEnd_1618769] using wordTrace_append hprefix tailTrace_1618769
  have hstable : (prefixWord ++ tailWord_1618769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618769).length < 2 ^ (prefixWord ++ tailWord_1618769).sum := by decide
  have hdescent : baseEnd_1618769 < baseStart_1618769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618828 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_1618828 : Nat := 118140960795 + 1618828 * 2 ^ 59
def prefixEnd_1618828 : Nat := 4983230072969 + 3 ^ 40 * 1618828 * 2
def baseEnd_1618828 : Nat := 369438604869643360757845

theorem tailTrace_1618828 : CollatzResearch.WordTrace tailWord_1618828 prefixEnd_1618828 369438604869643360757845 := by
  unfold tailWord_1618828
  simp only [CollatzResearch.WordTrace]
  refine ⟨29521753889635052328152569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39362338519513403104203425 29521753889635052328152569)
  ·
    refine ⟨22141315417226289246114427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29521753889635052328152569 22141315417226289246114427)
    ·
      refine ⟨33211973125839433869171641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22141315417226289246114427 33211973125839433869171641)
      ·
        refine ⟨24908979844379575401878731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33211973125839433869171641 24908979844379575401878731)
        ·
          refine ⟨37363469766569363102818097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24908979844379575401878731 37363469766569363102818097)
          ·
            refine ⟨28022602324927022327113573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37363469766569363102818097 28022602324927022327113573)
            ·
              refine ⟨5254237935923816686333795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28022602324927022327113573 5254237935923816686333795)
              ·
                refine ⟨7881356903885725029500693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5254237935923816686333795 7881356903885725029500693)
                ·
                  refine ⟨369438604869643360757845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7881356903885725029500693 369438604869643360757845)
                  ·
                    rfl

theorem cell21_1618828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_1618828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618828 prefixEnd_1618828 := by exact prefixLift 1618828
  have htrace : WordTrace (prefixWord ++ tailWord_1618828) baseStart_1618828 baseEnd_1618828 := by
    simpa [prefixWord, tailWord_1618828, baseEnd_1618828] using wordTrace_append hprefix tailTrace_1618828
  have hstable : (prefixWord ++ tailWord_1618828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618828).length < 2 ^ (prefixWord ++ tailWord_1618828).sum := by decide
  have hdescent : baseEnd_1618828 < baseStart_1618828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618845 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 4]
def baseStart_1618845 : Nat := 118140960795 + 1618845 * 2 ^ 59
def prefixEnd_1618845 : Nat := 4983230072969 + 3 ^ 40 * 1618845 * 2
def baseEnd_1618845 : Nat := 369442484501255108974477

theorem tailTrace_1618845 : CollatzResearch.WordTrace tailWord_1618845 prefixEnd_1618845 369442484501255108974477 := by
  unfold tailWord_1618845
  simp only [CollatzResearch.WordTrace]
  refine ⟨59044127820208516559673989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39362751880139011039782659 59044127820208516559673989)
  ·
    refine ⟨11070773966289096854938873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59044127820208516559673989 11070773966289096854938873)
    ·
      refine ⟨8303080474716822641204155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11070773966289096854938873 8303080474716822641204155)
      ·
        refine ⟨12454620712075233961806233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8303080474716822641204155 12454620712075233961806233)
        ·
          refine ⟨9340965534056425471354675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12454620712075233961806233 9340965534056425471354675)
          ·
            refine ⟨14011448301084638207032013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9340965534056425471354675 14011448301084638207032013)
            ·
              refine ⟨5254293112906739327637005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14011448301084638207032013 5254293112906739327637005)
              ·
                refine ⟨1970359917340027247863877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5254293112906739327637005 1970359917340027247863877)
                ·
                  refine ⟨369442484501255108974477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1970359917340027247863877 369442484501255108974477)
                  ·
                    rfl

theorem cell21_1618845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_1618845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1618845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1618845 prefixEnd_1618845 := by exact prefixLift 1618845
  have htrace : WordTrace (prefixWord ++ tailWord_1618845) baseStart_1618845 baseEnd_1618845 := by
    simpa [prefixWord, tailWord_1618845, baseEnd_1618845] using wordTrace_append hprefix tailTrace_1618845
  have hstable : (prefixWord ++ tailWord_1618845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618845).length < 2 ^ (prefixWord ++ tailWord_1618845).sum := by decide
  have hdescent : baseEnd_1618845 < baseStart_1618845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619000 : List Nat := [2, 1, 2, 1, 5, 2, 3, 2, 3]
def baseStart_1619000 : Nat := 118140960795 + 1619000 * 2 ^ 59
def prefixEnd_1619000 : Nat := 4983230072969 + 3 ^ 40 * 1619000 * 2
def baseEnd_1619000 : Nat := 369477857613009283890827

theorem tailTrace_1619000 : CollatzResearch.WordTrace tailWord_1619000 prefixEnd_1619000 369477857613009283890827 := by
  unfold tailWord_1619000
  simp only [CollatzResearch.WordTrace]
  refine ⟨29524890567323489015783227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39366520756431318687710969 29524890567323489015783227)
  ·
    refine ⟨44287335850985233523674841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29524890567323489015783227 44287335850985233523674841)
    ·
      refine ⟨33215501888238925142756131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44287335850985233523674841 33215501888238925142756131)
      ·
        refine ⟨49823252832358387714134197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33215501888238925142756131 49823252832358387714134197)
        ·
          refine ⟨4670929953033598848200081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49823252832358387714134197 4670929953033598848200081)
          ·
            refine ⟨3503197464775199136150061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4670929953033598848200081 3503197464775199136150061)
            ·
              refine ⟨1313699049290699676056273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3503197464775199136150061 1313699049290699676056273)
              ·
                refine ⟨985274286968024757042205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313699049290699676056273 985274286968024757042205)
                ·
                  refine ⟨369477857613009283890827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 985274286968024757042205 369477857613009283890827)
                  ·
                    rfl

theorem cell21_1619000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 3].length) (baseStart_1619000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619000 prefixEnd_1619000 := by exact prefixLift 1619000
  have htrace : WordTrace (prefixWord ++ tailWord_1619000) baseStart_1619000 baseEnd_1619000 := by
    simpa [prefixWord, tailWord_1619000, baseEnd_1619000] using wordTrace_append hprefix tailTrace_1619000
  have hstable : (prefixWord ++ tailWord_1619000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619000).length < 2 ^ (prefixWord ++ tailWord_1619000).sum := by decide
  have hdescent : baseEnd_1619000 < baseStart_1619000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619025 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 5]
def baseStart_1619025 : Nat := 118140960795 + 1619025 * 2 ^ 59
def prefixEnd_1619025 : Nat := 4983230072969 + 3 ^ 40 * 1619025 * 2
def baseEnd_1619025 : Nat := 369483562953614795974109

theorem tailTrace_1619025 : CollatzResearch.WordTrace tailWord_1619025 prefixEnd_1619025 369483562953614795974109 := by
  unfold tailWord_1619025
  simp only [CollatzResearch.WordTrace]
  refine ⟨59050692959556407301226529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39367128639704271534151019 59050692959556407301226529)
  ·
    refine ⟨44288019719667305475919897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59050692959556407301226529 44288019719667305475919897)
    ·
      refine ⟨33216014789750479106939923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44288019719667305475919897 33216014789750479106939923)
      ·
        refine ⟨49824022184625718660409885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33216014789750479106939923 49824022184625718660409885)
        ·
          refine ⟨18684008319234644497653707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49824022184625718660409885 18684008319234644497653707)
          ·
            refine ⟨28026012478851966746480561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18684008319234644497653707 28026012478851966746480561)
            ·
              refine ⟨21019509359138975059860421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28026012478851966746480561 21019509359138975059860421)
              ·
                refine ⟨3941158004838557823723829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21019509359138975059860421 3941158004838557823723829)
                ·
                  refine ⟨369483562953614795974109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3941158004838557823723829 369483562953614795974109)
                  ·
                    rfl

theorem cell21_1619025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_1619025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619025 prefixEnd_1619025 := by exact prefixLift 1619025
  have htrace : WordTrace (prefixWord ++ tailWord_1619025) baseStart_1619025 baseEnd_1619025 := by
    simpa [prefixWord, tailWord_1619025, baseEnd_1619025] using wordTrace_append hprefix tailTrace_1619025
  have hstable : (prefixWord ++ tailWord_1619025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619025).length < 2 ^ (prefixWord ++ tailWord_1619025).sum := by decide
  have hdescent : baseEnd_1619025 < baseStart_1619025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619073 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 4]
def baseStart_1619073 : Nat := 118140960795 + 1619073 * 2 ^ 59
def prefixEnd_1619073 : Nat := 4983230072969 + 3 ^ 40 * 1619073 * 2
def baseEnd_1619073 : Nat := 369494517207577379174011

theorem tailTrace_1619073 : CollatzResearch.WordTrace tailWord_1619073 prefixEnd_1619073 369494517207577379174011 := by
  unfold tailWord_1619073
  simp only [CollatzResearch.WordTrace]
  refine ⟨59052443663382511498973873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39368295775588340999315915 59052443663382511498973873)
  ·
    refine ⟨44289332747536883624230405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59052443663382511498973873 44289332747536883624230405)
    ·
      refine ⟨8304249890163165679543201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44289332747536883624230405 8304249890163165679543201)
      ·
        refine ⟨6228187417622374259657401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8304249890163165679543201 6228187417622374259657401)
        ·
          refine ⟨4671140563216780694743051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6228187417622374259657401 4671140563216780694743051)
          ·
            refine ⟨7006710844825171042114577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4671140563216780694743051 7006710844825171042114577)
            ·
              refine ⟨5255033133618878281585933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7006710844825171042114577 5255033133618878281585933)
              ·
                refine ⟨1970637425107079355594725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5255033133618878281585933 1970637425107079355594725)
                ·
                  refine ⟨369494517207577379174011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1970637425107079355594725 369494517207577379174011)
                  ·
                    rfl

theorem cell21_1619073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_1619073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619073 prefixEnd_1619073 := by exact prefixLift 1619073
  have htrace : WordTrace (prefixWord ++ tailWord_1619073) baseStart_1619073 baseEnd_1619073 := by
    simpa [prefixWord, tailWord_1619073, baseEnd_1619073] using wordTrace_append hprefix tailTrace_1619073
  have hstable : (prefixWord ++ tailWord_1619073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619073).length < 2 ^ (prefixWord ++ tailWord_1619073).sum := by decide
  have hdescent : baseEnd_1619073 < baseStart_1619073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619101 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 7]
def baseStart_1619101 : Nat := 118140960795 + 1619101 * 2 ^ 59
def prefixEnd_1619101 : Nat := 4983230072969 + 3 ^ 40 * 1619101 * 2
def baseEnd_1619101 : Nat := 369500907189055552707287

theorem tailTrace_1619101 : CollatzResearch.WordTrace tailWord_1619101 prefixEnd_1619101 369500907189055552707287 := by
  unfold tailWord_1619101
  simp only [CollatzResearch.WordTrace]
  refine ⟨59053464907281072280993157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39368976604854048187328771 59053464907281072280993157)
  ·
    refine ⟨11072524670115201052686217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59053464907281072280993157 11072524670115201052686217)
    ·
      refine ⟨8304393502586400789514663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11072524670115201052686217 8304393502586400789514663)
      ·
        refine ⟨12456590253879601184271995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8304393502586400789514663 12456590253879601184271995)
        ·
          refine ⟨18684885380819401776407993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12456590253879601184271995 18684885380819401776407993)
          ·
            refine ⟨14013664035614551332305995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18684885380819401776407993 14013664035614551332305995)
            ·
              refine ⟨21020496053421826998458993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14013664035614551332305995 21020496053421826998458993)
              ·
                refine ⟨15765372040066370248844245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21020496053421826998458993 15765372040066370248844245)
                ·
                  refine ⟨369500907189055552707287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15765372040066370248844245 369500907189055552707287)
                  ·
                    rfl

theorem cell21_1619101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_1619101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619101 prefixEnd_1619101 := by exact prefixLift 1619101
  have htrace : WordTrace (prefixWord ++ tailWord_1619101) baseStart_1619101 baseEnd_1619101 := by
    simpa [prefixWord, tailWord_1619101, baseEnd_1619101] using wordTrace_append hprefix tailTrace_1619101
  have hstable : (prefixWord ++ tailWord_1619101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619101).length < 2 ^ (prefixWord ++ tailWord_1619101).sum := by decide
  have hdescent : baseEnd_1619101 < baseStart_1619101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619183 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 4]
def baseStart_1619183 : Nat := 118140960795 + 1619183 * 2 ^ 59
def prefixEnd_1619183 : Nat := 4983230072969 + 3 ^ 40 * 1619183 * 2
def baseEnd_1619183 : Nat := 369519620706241632340453

theorem tailTrace_1619183 : CollatzResearch.WordTrace tailWord_1619183 prefixEnd_1619183 369519620706241632340453 := by
  unfold tailWord_1619183
  simp only [CollatzResearch.WordTrace]
  refine ⟨59056455692984000285478203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39370970461989333523652135 59056455692984000285478203)
  ·
    refine ⟨88584683539476000428217305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59056455692984000285478203 88584683539476000428217305)
    ·
      refine ⟨66438512654607000321162979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88584683539476000428217305 66438512654607000321162979)
      ·
        refine ⟨99657768981910500481744469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66438512654607000321162979 99657768981910500481744469)
        ·
          refine ⟨1167864480256763677520443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 99657768981910500481744469 1167864480256763677520443)
          ·
            refine ⟨1751796720385145516280665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167864480256763677520443 1751796720385145516280665)
            ·
              refine ⟨1313847540288859137210499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751796720385145516280665 1313847540288859137210499)
              ·
                refine ⟨1970771310433288705815749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313847540288859137210499 1970771310433288705815749)
                ·
                  refine ⟨369519620706241632340453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1970771310433288705815749 369519620706241632340453)
                  ·
                    rfl

theorem cell21_1619183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 4].length) (baseStart_1619183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619183 prefixEnd_1619183 := by exact prefixLift 1619183
  have htrace : WordTrace (prefixWord ++ tailWord_1619183) baseStart_1619183 baseEnd_1619183 := by
    simpa [prefixWord, tailWord_1619183, baseEnd_1619183] using wordTrace_append hprefix tailTrace_1619183
  have hstable : (prefixWord ++ tailWord_1619183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619183).length < 2 ^ (prefixWord ++ tailWord_1619183).sum := by decide
  have hdescent : baseEnd_1619183 < baseStart_1619183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619253 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 7]
def baseStart_1619253 : Nat := 118140960795 + 1619253 * 2 ^ 59
def prefixEnd_1619253 : Nat := 4983230072969 + 3 ^ 40 * 1619253 * 2
def baseEnd_1619253 : Nat := 369535595659937066173643

theorem tailTrace_1619253 : CollatzResearch.WordTrace tailWord_1619253 prefixEnd_1619253 369535595659937066173643 := by
  unfold tailWord_1619253
  simp only [CollatzResearch.WordTrace]
  refine ⟨59059008802730402240526413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39372672535153601493684275 59059008802730402240526413)
  ·
    refine ⟨22147128301023900840197405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59059008802730402240526413 22147128301023900840197405)
    ·
      refine ⟨8305173112883962815074027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22147128301023900840197405 8305173112883962815074027)
      ·
        refine ⟨12457759669325944222611041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8305173112883962815074027 12457759669325944222611041)
        ·
          refine ⟨9343319751994458166958281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12457759669325944222611041 9343319751994458166958281)
          ·
            refine ⟨7007489813995843625218711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9343319751994458166958281 7007489813995843625218711)
            ·
              refine ⟨10511234720993765437828067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7007489813995843625218711 10511234720993765437828067)
              ·
                refine ⟨15766852081490648156742101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10511234720993765437828067 15766852081490648156742101)
                ·
                  refine ⟨369535595659937066173643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15766852081490648156742101 369535595659937066173643)
                  ·
                    rfl

theorem cell21_1619253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_1619253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619253 prefixEnd_1619253 := by exact prefixLift 1619253
  have htrace : WordTrace (prefixWord ++ tailWord_1619253) baseStart_1619253 baseEnd_1619253 := by
    simpa [prefixWord, tailWord_1619253, baseEnd_1619253] using wordTrace_append hprefix tailTrace_1619253
  have hstable : (prefixWord ++ tailWord_1619253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619253).length < 2 ^ (prefixWord ++ tailWord_1619253).sum := by decide
  have hdescent : baseEnd_1619253 < baseStart_1619253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619267 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 6]
def baseStart_1619267 : Nat := 118140960795 + 1619267 * 2 ^ 59
def prefixEnd_1619267 : Nat := 4983230072969 + 3 ^ 40 * 1619267 * 2
def baseEnd_1619267 : Nat := 369538790650676152940281

theorem tailTrace_1619267 : CollatzResearch.WordTrace tailWord_1619267 prefixEnd_1619267 369538790650676152940281 := by
  unfold tailWord_1619267
  simp only [CollatzResearch.WordTrace]
  refine ⟨59059519424679682631536055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39373012949786455087690703 59059519424679682631536055)
  ·
    refine ⟨88589279137019523947304083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59059519424679682631536055 88589279137019523947304083)
    ·
      refine ⟨132883918705529285920956125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88589279137019523947304083 132883918705529285920956125)
      ·
        refine ⟨49831469514573482220358547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132883918705529285920956125 49831469514573482220358547)
        ·
          refine ⟨74747204271860223330537821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49831469514573482220358547 74747204271860223330537821)
          ·
            refine ⟨28030201601947583748951683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74747204271860223330537821 28030201601947583748951683)
            ·
              refine ⟨42045302402921375623427525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28030201601947583748951683 42045302402921375623427525)
              ·
                refine ⟨7883494200547757929392661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42045302402921375623427525 7883494200547757929392661)
                ·
                  refine ⟨369538790650676152940281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7883494200547757929392661 369538790650676152940281)
                  ·
                    rfl

theorem cell21_1619267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_1619267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619267 prefixEnd_1619267 := by exact prefixLift 1619267
  have htrace : WordTrace (prefixWord ++ tailWord_1619267) baseStart_1619267 baseEnd_1619267 := by
    simpa [prefixWord, tailWord_1619267, baseEnd_1619267] using wordTrace_append hprefix tailTrace_1619267
  have hstable : (prefixWord ++ tailWord_1619267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619267).length < 2 ^ (prefixWord ++ tailWord_1619267).sum := by decide
  have hdescent : baseEnd_1619267 < baseStart_1619267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619284 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1619284 : Nat := 118140960795 + 1619284 * 2 ^ 59
def prefixEnd_1619284 : Nat := 4983230072969 + 3 ^ 40 * 1619284 * 2
def baseEnd_1619284 : Nat := 369542670282287901156913

theorem tailTrace_1619284 : CollatzResearch.WordTrace tailWord_1619284 prefixEnd_1619284 369542670282287901156913 := by
  unfold tailWord_1619284
  simp only [CollatzResearch.WordTrace]
  refine ⟨29530069732809047267452453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39373426310412063023269937 29530069732809047267452453)
  ·
    refine ⟨5536888074901696362647335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29530069732809047267452453 5536888074901696362647335)
    ·
      refine ⟨8305332112352544543971003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5536888074901696362647335 8305332112352544543971003)
      ·
        refine ⟨12457998168528816815956505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8305332112352544543971003 12457998168528816815956505)
        ·
          refine ⟨9343498626396612611967379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12457998168528816815956505 9343498626396612611967379)
          ·
            refine ⟨14015247939594918917951069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9343498626396612611967379 14015247939594918917951069)
            ·
              refine ⟨5255717977348094594231651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14015247939594918917951069 5255717977348094594231651)
              ·
                refine ⟨7883576966022141891347477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255717977348094594231651 7883576966022141891347477)
                ·
                  refine ⟨369542670282287901156913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7883576966022141891347477 369542670282287901156913)
                  ·
                    rfl

theorem cell21_1619284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1619284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619284 prefixEnd_1619284 := by exact prefixLift 1619284
  have htrace : WordTrace (prefixWord ++ tailWord_1619284) baseStart_1619284 baseEnd_1619284 := by
    simpa [prefixWord, tailWord_1619284, baseEnd_1619284] using wordTrace_append hprefix tailTrace_1619284
  have hstable : (prefixWord ++ tailWord_1619284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619284).length < 2 ^ (prefixWord ++ tailWord_1619284).sum := by decide
  have hdescent : baseEnd_1619284 < baseStart_1619284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619301 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 4]
def baseStart_1619301 : Nat := 118140960795 + 1619301 * 2 ^ 59
def prefixEnd_1619301 : Nat := 4983230072969 + 3 ^ 40 * 1619301 * 2
def baseEnd_1619301 : Nat := 369546549913899649373545

theorem tailTrace_1619301 : CollatzResearch.WordTrace tailWord_1619301 prefixEnd_1619301 369546549913899649373545 := by
  unfold tailWord_1619301
  simp only [CollatzResearch.WordTrace]
  refine ⟨59060759506556506438273757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39373839671037670958849171 59060759506556506438273757)
  ·
    refine ⟨22147784814958689914352659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59060759506556506438273757 22147784814958689914352659)
    ·
      refine ⟨33221677222438034871528989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22147784814958689914352659 33221677222438034871528989)
      ·
        refine ⟨12458128958414263076823371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33221677222438034871528989 12458128958414263076823371)
        ·
          refine ⟨18687193437621394615235057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12458128958414263076823371 18687193437621394615235057)
          ·
            refine ⟨14015395078216045961426293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18687193437621394615235057 14015395078216045961426293)
            ·
              refine ⟨1313943288582754308883715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14015395078216045961426293 1313943288582754308883715)
              ·
                refine ⟨1970914932874131463325573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313943288582754308883715 1970914932874131463325573)
                ·
                  refine ⟨369546549913899649373545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1970914932874131463325573 369546549913899649373545)
                  ·
                    rfl

theorem cell21_1619301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_1619301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619301 prefixEnd_1619301 := by exact prefixLift 1619301
  have htrace : WordTrace (prefixWord ++ tailWord_1619301) baseStart_1619301 baseEnd_1619301 := by
    simpa [prefixWord, tailWord_1619301, baseEnd_1619301] using wordTrace_append hprefix tailTrace_1619301
  have hstable : (prefixWord ++ tailWord_1619301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619301).length < 2 ^ (prefixWord ++ tailWord_1619301).sum := by decide
  have hdescent : baseEnd_1619301 < baseStart_1619301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619360 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_1619360 : Nat := 118140960795 + 1619360 * 2 ^ 59
def prefixEnd_1619360 : Nat := 4983230072969 + 3 ^ 40 * 1619360 * 2
def baseEnd_1619360 : Nat := 369560014517728657890091

theorem tailTrace_1619360 : CollatzResearch.WordTrace tailWord_1619360 prefixEnd_1619360 369560014517728657890091 := by
  unfold tailWord_1619360
  simp only [CollatzResearch.WordTrace]
  refine ⟨29531455706671379757335767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39375274275561839676447689 29531455706671379757335767)
  ·
    refine ⟨44297183560007069636003651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29531455706671379757335767 44297183560007069636003651)
    ·
      refine ⟨66445775340010604454005477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44297183560007069636003651 66445775340010604454005477)
      ·
        refine ⟨12458582876251988335126027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66445775340010604454005477 12458582876251988335126027)
        ·
          refine ⟨18687874314377982502689041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12458582876251988335126027 18687874314377982502689041)
          ·
            refine ⟨14015905735783486877016781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18687874314377982502689041 14015905735783486877016781)
            ·
              refine ⟨5255964650918807578881293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14015905735783486877016781 5255964650918807578881293)
              ·
                refine ⟨1970986744094552842080485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5255964650918807578881293 1970986744094552842080485)
                ·
                  refine ⟨369560014517728657890091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1970986744094552842080485 369560014517728657890091)
                  ·
                    rfl

theorem cell21_1619360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_1619360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619360 prefixEnd_1619360 := by exact prefixLift 1619360
  have htrace : WordTrace (prefixWord ++ tailWord_1619360) baseStart_1619360 baseEnd_1619360 := by
    simpa [prefixWord, tailWord_1619360, baseEnd_1619360] using wordTrace_append hprefix tailTrace_1619360
  have hstable : (prefixWord ++ tailWord_1619360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619360).length < 2 ^ (prefixWord ++ tailWord_1619360).sum := by decide
  have hdescent : baseEnd_1619360 < baseStart_1619360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619453 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 4]
def baseStart_1619453 : Nat := 118140960795 + 1619453 * 2 ^ 59
def prefixEnd_1619453 : Nat := 4983230072969 + 3 ^ 40 * 1619453 * 2
def baseEnd_1619453 : Nat := 369581238384781162839901

theorem tailTrace_1619453 : CollatzResearch.WordTrace tailWord_1619453 prefixEnd_1619453 369581238384781162839901 := by
  unfold tailWord_1619453
  simp only [CollatzResearch.WordTrace]
  refine ⟨59066303402005836397807013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39377535601337224265204675 59066303402005836397807013)
  ·
    refine ⟨11074931887876094324588815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59066303402005836397807013 11074931887876094324588815)
    ·
      refine ⟨16612397831814141486883223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11074931887876094324588815 16612397831814141486883223)
      ·
        refine ⟨24918596747721212230324835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16612397831814141486883223 24918596747721212230324835)
        ·
          refine ⟨37377895121581818345487253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24918596747721212230324835 37377895121581818345487253)
          ·
            refine ⟨1752088833824147734944715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37377895121581818345487253 1752088833824147734944715)
            ·
              refine ⟨2628133250736221602417073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752088833824147734944715 2628133250736221602417073)
              ·
                refine ⟨1971099938052166201812805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628133250736221602417073 1971099938052166201812805)
                ·
                  refine ⟨369581238384781162839901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971099938052166201812805 369581238384781162839901)
                  ·
                    rfl

theorem cell21_1619453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_1619453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619453 prefixEnd_1619453 := by exact prefixLift 1619453
  have htrace : WordTrace (prefixWord ++ tailWord_1619453) baseStart_1619453 baseEnd_1619453 := by
    simpa [prefixWord, tailWord_1619453, baseEnd_1619453] using wordTrace_append hprefix tailTrace_1619453
  have hstable : (prefixWord ++ tailWord_1619453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619453).length < 2 ^ (prefixWord ++ tailWord_1619453).sum := by decide
  have hdescent : baseEnd_1619453 < baseStart_1619453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619470 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_1619470 : Nat := 118140960795 + 1619470 * 2 ^ 59
def prefixEnd_1619470 : Nat := 4983230072969 + 3 ^ 40 * 1619470 * 2
def baseEnd_1619470 : Nat := 369585118016392911056533

theorem tailTrace_1619470 : CollatzResearch.WordTrace tailWord_1619470 prefixEnd_1619470 369585118016392911056533 := by
  unfold tailWord_1619470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7383365430368031037646983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39377948961962832200783909 7383365430368031037646983)
  ·
    refine ⟨11075048145552046556470475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7383365430368031037646983 11075048145552046556470475)
    ·
      refine ⟨16612572218328069834705713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11075048145552046556470475 16612572218328069834705713)
      ·
        refine ⟨12459429163746052376029285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16612572218328069834705713 12459429163746052376029285)
        ·
          refine ⟨2336142968202384820505491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12459429163746052376029285 2336142968202384820505491)
          ·
            refine ⟨3504214452303577230758237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336142968202384820505491 3504214452303577230758237)
            ·
              refine ⟨1314080419613841461534339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3504214452303577230758237 1314080419613841461534339)
              ·
                refine ⟨1971120629420762192301509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314080419613841461534339 1971120629420762192301509)
                ·
                  refine ⟨369585118016392911056533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971120629420762192301509 369585118016392911056533)
                  ·
                    rfl

theorem cell21_1619470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_1619470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619470 prefixEnd_1619470 := by exact prefixLift 1619470
  have htrace : WordTrace (prefixWord ++ tailWord_1619470) baseStart_1619470 baseEnd_1619470 := by
    simpa [prefixWord, tailWord_1619470, baseEnd_1619470] using wordTrace_append hprefix tailTrace_1619470
  have hstable : (prefixWord ++ tailWord_1619470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619470).length < 2 ^ (prefixWord ++ tailWord_1619470).sum := by decide
  have hdescent : baseEnd_1619470 < baseStart_1619470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619740 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_1619740 : Nat := 118140960795 + 1619740 * 2 ^ 59
def prefixEnd_1619740 : Nat := 4983230072969 + 3 ^ 40 * 1619740 * 2
def baseEnd_1619740 : Nat := 369646735694932441555981

theorem tailTrace_1619740 : CollatzResearch.WordTrace tailWord_1619740 prefixEnd_1619740 369646735694932441555981 := by
  unfold tailWord_1619740
  simp only [CollatzResearch.WordTrace]
  refine ⟨29538385575983042206752337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39384514101310722942336449 29538385575983042206752337)
  ·
    refine ⟨22153789181987281655064253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29538385575983042206752337 22153789181987281655064253)
    ·
      refine ⟨8307670943245230620649095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22153789181987281655064253 8307670943245230620649095)
      ·
        refine ⟨12461506414867845930973643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307670943245230620649095 12461506414867845930973643)
        ·
          refine ⟨18692259622301768896460465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12461506414867845930973643 18692259622301768896460465)
          ·
            refine ⟨14019194716726326672345349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18692259622301768896460465 14019194716726326672345349)
            ·
              refine ⟨2628599009386186251064753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14019194716726326672345349 2628599009386186251064753)
              ·
                refine ⟨1971449257039639688298565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628599009386186251064753 1971449257039639688298565)
                ·
                  refine ⟨369646735694932441555981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971449257039639688298565 369646735694932441555981)
                  ·
                    rfl

theorem cell21_1619740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_1619740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619740 prefixEnd_1619740 := by exact prefixLift 1619740
  have htrace : WordTrace (prefixWord ++ tailWord_1619740) baseStart_1619740 baseEnd_1619740 := by
    simpa [prefixWord, tailWord_1619740, baseEnd_1619740] using wordTrace_append hprefix tailTrace_1619740
  have hstable : (prefixWord ++ tailWord_1619740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619740).length < 2 ^ (prefixWord ++ tailWord_1619740).sum := by decide
  have hdescent : baseEnd_1619740 < baseStart_1619740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619768 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_1619768 : Nat := 118140960795 + 1619768 * 2 ^ 59
def prefixEnd_1619768 : Nat := 4983230072969 + 3 ^ 40 * 1619768 * 2
def baseEnd_1619768 : Nat := 369653125676410615089257

theorem tailTrace_1619768 : CollatzResearch.WordTrace tailWord_1619768 prefixEnd_1619768 369653125676410615089257 := by
  unfold tailWord_1619768
  simp only [CollatzResearch.WordTrace]
  refine ⟨29538896197932322597761979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39385194930576430130349305 29538896197932322597761979)
  ·
    refine ⟨44308344296898483896642969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29538896197932322597761979 44308344296898483896642969)
    ·
      refine ⟨33231258222673862922482227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44308344296898483896642969 33231258222673862922482227)
      ·
        refine ⟨49846887334010794383723341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33231258222673862922482227 49846887334010794383723341)
        ·
          refine ⟨18692582750254047893896253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49846887334010794383723341 18692582750254047893896253)
          ·
            refine ⟨7009718531345267960211095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18692582750254047893896253 7009718531345267960211095)
            ·
              refine ⟨10514577797017901940316643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7009718531345267960211095 10514577797017901940316643)
              ·
                refine ⟨15771866695526852910474965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10514577797017901940316643 15771866695526852910474965)
                ·
                  refine ⟨369653125676410615089257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15771866695526852910474965 369653125676410615089257)
                  ·
                    rfl

theorem cell21_1619768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_1619768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619768 prefixEnd_1619768 := by exact prefixLift 1619768
  have htrace : WordTrace (prefixWord ++ tailWord_1619768) baseStart_1619768 baseEnd_1619768 := by
    simpa [prefixWord, tailWord_1619768, baseEnd_1619768] using wordTrace_append hprefix tailTrace_1619768
  have hstable : (prefixWord ++ tailWord_1619768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619768).length < 2 ^ (prefixWord ++ tailWord_1619768).sum := by decide
  have hdescent : baseEnd_1619768 < baseStart_1619768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619813 : List Nat := [1, 3, 1, 3, 1, 1, 1, 10]
def baseStart_1619813 : Nat := 118140960795 + 1619813 * 2 ^ 59
def prefixEnd_1619813 : Nat := 4983230072969 + 3 ^ 40 * 1619813 * 2
def baseEnd_1619813 : Nat := 123221131763166845613055

theorem tailTrace_1619813 : CollatzResearch.WordTrace tailWord_1619813 prefixEnd_1619813 123221131763166845613055 := by
  unfold tailWord_1619813
  simp only [CollatzResearch.WordTrace]
  refine ⟨59079433680701617880912093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39386289120467745253941395 59079433680701617880912093)
  ·
    refine ⟨22154787630263106705342035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59079433680701617880912093 22154787630263106705342035)
    ·
      refine ⟨33232181445394660058013053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22154787630263106705342035 33232181445394660058013053)
      ·
        refine ⟨12462068042022997521754895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33232181445394660058013053 12462068042022997521754895)
        ·
          refine ⟨18693102063034496282632343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12462068042022997521754895 18693102063034496282632343)
          ·
            refine ⟨28039653094551744423948515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18693102063034496282632343 28039653094551744423948515)
            ·
              refine ⟨42059479641827616635922773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28039653094551744423948515 42059479641827616635922773)
              ·
                refine ⟨123221131763166845613055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42059479641827616635922773 123221131763166845613055)
                ·
                  rfl

theorem cell21_1619813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 10].length) (baseStart_1619813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619813 prefixEnd_1619813 := by exact prefixLift 1619813
  have htrace : WordTrace (prefixWord ++ tailWord_1619813) baseStart_1619813 baseEnd_1619813 := by
    simpa [prefixWord, tailWord_1619813, baseEnd_1619813] using wordTrace_append hprefix tailTrace_1619813
  have hstable : (prefixWord ++ tailWord_1619813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619813).length < 2 ^ (prefixWord ++ tailWord_1619813).sum := by decide
  have hdescent : baseEnd_1619813 < baseStart_1619813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619844 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1619844 : Nat := 118140960795 + 1619844 * 2 ^ 59
def prefixEnd_1619844 : Nat := 4983230072969 + 3 ^ 40 * 1619844 * 2
def baseEnd_1619844 : Nat := 369670469911851371822435

theorem tailTrace_1619844 : CollatzResearch.WordTrace tailWord_1619844 prefixEnd_1619844 369670469911851371822435 := by
  unfold tailWord_1619844
  simp only [CollatzResearch.WordTrace]
  refine ⟨29540282171794655087645293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39387042895726206783527057 29540282171794655087645293)
  ·
    refine ⟨11077605814422995657866985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29540282171794655087645293 11077605814422995657866985)
    ·
      refine ⟨8308204360817246743400239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11077605814422995657866985 8308204360817246743400239)
      ·
        refine ⟨12462306541225870115100359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8308204360817246743400239 12462306541225870115100359)
        ·
          refine ⟨18693459811838805172650539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12462306541225870115100359 18693459811838805172650539)
          ·
            refine ⟨28040189717758207758975809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18693459811838805172650539 28040189717758207758975809)
            ·
              refine ⟨21030142288318655819231857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28040189717758207758975809 21030142288318655819231857)
              ·
                refine ⟨15772606716238991864423893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21030142288318655819231857 15772606716238991864423893)
                ·
                  refine ⟨369670469911851371822435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15772606716238991864423893 369670469911851371822435)
                  ·
                    rfl

theorem cell21_1619844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1619844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619844 prefixEnd_1619844 := by exact prefixLift 1619844
  have htrace : WordTrace (prefixWord ++ tailWord_1619844) baseStart_1619844 baseEnd_1619844 := by
    simpa [prefixWord, tailWord_1619844, baseEnd_1619844] using wordTrace_append hprefix tailTrace_1619844
  have hstable : (prefixWord ++ tailWord_1619844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619844).length < 2 ^ (prefixWord ++ tailWord_1619844).sum := by decide
  have hdescent : baseEnd_1619844 < baseStart_1619844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619847 : List Nat := [1, 1, 4, 2, 5, 1, 7]
def baseStart_1619847 : Nat := 118140960795 + 1619847 * 2 ^ 59
def prefixEnd_1619847 : Nat := 4983230072969 + 3 ^ 40 * 1619847 * 2
def baseEnd_1619847 : Nat := 41074572728080448141381

theorem tailTrace_1619847 : CollatzResearch.WordTrace tailWord_1619847 prefixEnd_1619847 41074572728080448141381 := by
  unfold tailWord_1619847
  simp only [CollatzResearch.WordTrace]
  refine ⟨59080673762578441687649795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39387115841718961125099863 59080673762578441687649795)
  ·
    refine ⟨88621010643867662531474693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59080673762578441687649795 88621010643867662531474693)
    ·
      refine ⟨16616439495725186724651505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88621010643867662531474693 16616439495725186724651505)
      ·
        refine ⟨12462329621793890043488629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16616439495725186724651505 12462329621793890043488629)
        ·
          refine ⟨1168343402043177191577059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12462329621793890043488629 1168343402043177191577059)
          ·
            refine ⟨1752515103064765787365589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168343402043177191577059 1752515103064765787365589)
            ·
              refine ⟨41074572728080448141381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1752515103064765787365589 41074572728080448141381)
              ·
                rfl

theorem cell21_1619847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 7].length) (baseStart_1619847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1619847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1619847 prefixEnd_1619847 := by exact prefixLift 1619847
  have htrace : WordTrace (prefixWord ++ tailWord_1619847) baseStart_1619847 baseEnd_1619847 := by
    simpa [prefixWord, tailWord_1619847, baseEnd_1619847] using wordTrace_append hprefix tailTrace_1619847
  have hstable : (prefixWord ++ tailWord_1619847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619847).length < 2 ^ (prefixWord ++ tailWord_1619847).sum := by decide
  have hdescent : baseEnd_1619847 < baseStart_1619847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620041 : List Nat := [1, 2, 1, 1, 2, 2, 6, 6]
def baseStart_1620041 : Nat := 118140960795 + 1620041 * 2 ^ 59
def prefixEnd_1620041 : Nat := 4983230072969 + 3 ^ 40 * 1620041 * 2
def baseEnd_1620041 : Nat := 123238475998607602346233

theorem tailTrace_1620041 : CollatzResearch.WordTrace tailWord_1620041 prefixEnd_1620041 123238475998607602346233 := by
  unfold tailWord_1620041
  simp only [CollatzResearch.WordTrace]
  refine ⟨59087749523875612820211977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39391833015917075213474651 59087749523875612820211977)
  ·
    refine ⟨44315812142906709615158983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59087749523875612820211977 44315812142906709615158983)
    ·
      refine ⟨66473718214360064422738475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44315812142906709615158983 66473718214360064422738475)
      ·
        refine ⟨99710577321540096634107713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66473718214360064422738475 99710577321540096634107713)
        ·
          refine ⟨74782932991155072475580785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99710577321540096634107713 74782932991155072475580785)
          ·
            refine ⟨56087199743366304356685589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74782932991155072475580785 56087199743366304356685589)
            ·
              refine ⟨2629087487970295516719637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56087199743366304356685589 2629087487970295516719637)
              ·
                refine ⟨123238475998607602346233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2629087487970295516719637 123238475998607602346233)
                ·
                  rfl

theorem cell21_1620041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 6].length) (baseStart_1620041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620041 prefixEnd_1620041 := by exact prefixLift 1620041
  have htrace : WordTrace (prefixWord ++ tailWord_1620041) baseStart_1620041 baseEnd_1620041 := by
    simpa [prefixWord, tailWord_1620041, baseEnd_1620041] using wordTrace_append hprefix tailTrace_1620041
  have hstable : (prefixWord ++ tailWord_1620041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620041).length < 2 ^ (prefixWord ++ tailWord_1620041).sum := by decide
  have hdescent : baseEnd_1620041 < baseStart_1620041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620044 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 4]
def baseStart_1620044 : Nat := 118140960795 + 1620044 * 2 ^ 59
def prefixEnd_1620044 : Nat := 4983230072969 + 3 ^ 40 * 1620044 * 2
def baseEnd_1620044 : Nat := 369716112636695468488693

theorem tailTrace_1620044 : CollatzResearch.WordTrace tailWord_1620044 prefixEnd_1620044 369716112636695468488693 := by
  unfold tailWord_1620044
  simp only [CollatzResearch.WordTrace]
  refine ⟨29543929471432372166285593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39391905961909829555047457 29543929471432372166285593)
  ·
    refine ⟨22157947103574279124714195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29543929471432372166285593 22157947103574279124714195)
    ·
      refine ⟨33236920655361418687071293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22157947103574279124714195 33236920655361418687071293)
      ·
        refine ⟨12463845245760532007651735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33236920655361418687071293 12463845245760532007651735)
        ·
          refine ⟨18695767868640798011477603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12463845245760532007651735 18695767868640798011477603)
          ·
            refine ⟨28043651802961197017216405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18695767868640798011477603 28043651802961197017216405)
            ·
              refine ⟨1314546178263806110182019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28043651802961197017216405 1314546178263806110182019)
              ·
                refine ⟨1971819267395709165273029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314546178263806110182019 1971819267395709165273029)
                ·
                  refine ⟨369716112636695468488693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971819267395709165273029 369716112636695468488693)
                  ·
                    rfl

theorem cell21_1620044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_1620044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620044 prefixEnd_1620044 := by exact prefixLift 1620044
  have htrace : WordTrace (prefixWord ++ tailWord_1620044) baseStart_1620044 baseEnd_1620044 := by
    simpa [prefixWord, tailWord_1620044, baseEnd_1620044] using wordTrace_append hprefix tailTrace_1620044
  have hstable : (prefixWord ++ tailWord_1620044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620044).length < 2 ^ (prefixWord ++ tailWord_1620044).sum := by decide
  have hdescent : baseEnd_1620044 < baseStart_1620044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620103 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 4]
def baseStart_1620103 : Nat := 118140960795 + 1620103 * 2 ^ 59
def prefixEnd_1620103 : Nat := 4983230072969 + 3 ^ 40 * 1620103 * 2
def baseEnd_1620103 : Nat := 369729577240524477005239

theorem tailTrace_1620103 : CollatzResearch.WordTrace tailWord_1620103 prefixEnd_1620103 369729577240524477005239 := by
  unfold tailWord_1620103
  simp only [CollatzResearch.WordTrace]
  refine ⟨59090010849650997408968963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39393340566433998272645975 59090010849650997408968963)
  ·
    refine ⟨88635016274476496113453445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59090010849650997408968963 88635016274476496113453445)
    ·
      refine ⟨16619065551464343021272521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88635016274476496113453445 16619065551464343021272521)
      ·
        refine ⟨12464299163598257265954391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16619065551464343021272521 12464299163598257265954391)
        ·
          refine ⟨18696448745397385898931587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12464299163598257265954391 18696448745397385898931587)
          ·
            refine ⟨28044673118096078848397381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18696448745397385898931587 28044673118096078848397381)
            ·
              refine ⟨5258376209643014784074509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28044673118096078848397381 5258376209643014784074509)
              ·
                refine ⟨1971891078616130544027941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5258376209643014784074509 1971891078616130544027941)
                ·
                  refine ⟨369729577240524477005239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971891078616130544027941 369729577240524477005239)
                  ·
                    rfl

theorem cell21_1620103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 4].length) (baseStart_1620103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620103 prefixEnd_1620103 := by exact prefixLift 1620103
  have htrace : WordTrace (prefixWord ++ tailWord_1620103) baseStart_1620103 baseEnd_1620103 := by
    simpa [prefixWord, tailWord_1620103, baseEnd_1620103] using wordTrace_append hprefix tailTrace_1620103
  have hstable : (prefixWord ++ tailWord_1620103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620103).length < 2 ^ (prefixWord ++ tailWord_1620103).sum := by decide
  have hdescent : baseEnd_1620103 < baseStart_1620103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620199 : List Nat := [1, 1, 5, 3, 1, 2, 3, 2, 3]
def baseStart_1620199 : Nat := 118140960795 + 1620199 * 2 ^ 59
def prefixEnd_1620199 : Nat := 4983230072969 + 3 ^ 40 * 1620199 * 2
def baseEnd_1620199 : Nat := 369751485748449643405043

theorem tailTrace_1620199 : CollatzResearch.WordTrace tailWord_1620199 prefixEnd_1620199 369751485748449643405043 := by
  unfold tailWord_1620199
  simp only [CollatzResearch.WordTrace]
  refine ⟨59093512257303205804463651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39395674838202137202975767 59093512257303205804463651)
  ·
    refine ⟨88640268385954808706695477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59093512257303205804463651 88640268385954808706695477)
    ·
      refine ⟨8310025161183263316252701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88640268385954808706695477 8310025161183263316252701)
      ·
        refine ⟨3116259435443723743594763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8310025161183263316252701 3116259435443723743594763)
        ·
          refine ⟨4674389153165585615392145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116259435443723743594763 4674389153165585615392145)
          ·
            refine ⟨3505791864874189211544109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4674389153165585615392145 3505791864874189211544109)
            ·
              refine ⟨1314671949327820954329041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3505791864874189211544109 1314671949327820954329041)
              ·
                refine ⟨986003961995865715746781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314671949327820954329041 986003961995865715746781)
                ·
                  refine ⟨369751485748449643405043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986003961995865715746781 369751485748449643405043)
                  ·
                    rfl

theorem cell21_1620199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 3].length) (baseStart_1620199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620199 prefixEnd_1620199 := by exact prefixLift 1620199
  have htrace : WordTrace (prefixWord ++ tailWord_1620199) baseStart_1620199 baseEnd_1620199 := by
    simpa [prefixWord, tailWord_1620199, baseEnd_1620199] using wordTrace_append hprefix tailTrace_1620199
  have hstable : (prefixWord ++ tailWord_1620199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620199).length < 2 ^ (prefixWord ++ tailWord_1620199).sum := by decide
  have hdescent : baseEnd_1620199 < baseStart_1620199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620210 : List Nat := [3, 2, 1, 3, 2, 2, 2, 6]
def baseStart_1620210 : Nat := 118140960795 + 1620210 * 2 ^ 59
def prefixEnd_1620210 : Nat := 4983230072969 + 3 ^ 40 * 1620210 * 2
def baseEnd_1620210 : Nat := 123251332032772022907229

theorem tailTrace_1620210 : CollatzResearch.WordTrace tailWord_1620210 prefixEnd_1620210 123251332032772022907229 := by
  unfold tailWord_1620210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773478365065838670778521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39395942306842236455409389 14773478365065838670778521)
  ·
    refine ⟨11080108773799379003083891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14773478365065838670778521 11080108773799379003083891)
    ·
      refine ⟨16620163160699068504625837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11080108773799379003083891 16620163160699068504625837)
      ·
        refine ⟨6232561185262150689234689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16620163160699068504625837 6232561185262150689234689)
        ·
          refine ⟨4674420888946613016926017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6232561185262150689234689 4674420888946613016926017)
          ·
            refine ⟨3505815666709959762694513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4674420888946613016926017 3505815666709959762694513)
            ·
              refine ⟨2629361750032469822020885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3505815666709959762694513 2629361750032469822020885)
              ·
                refine ⟨123251332032772022907229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2629361750032469822020885 123251332032772022907229)
                ·
                  rfl

theorem cell21_1620210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_1620210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620210 prefixEnd_1620210 := by exact prefixLift 1620210
  have htrace : WordTrace (prefixWord ++ tailWord_1620210) baseStart_1620210 baseEnd_1620210 := by
    simpa [prefixWord, tailWord_1620210, baseEnd_1620210] using wordTrace_append hprefix tailTrace_1620210
  have hstable : (prefixWord ++ tailWord_1620210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620210).length < 2 ^ (prefixWord ++ tailWord_1620210).sum := by decide
  have hdescent : baseEnd_1620210 < baseStart_1620210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620255 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 4]
def baseStart_1620255 : Nat := 118140960795 + 1620255 * 2 ^ 59
def prefixEnd_1620255 : Nat := 4983230072969 + 3 ^ 40 * 1620255 * 2
def baseEnd_1620255 : Nat := 369764265711405990471595

theorem tailTrace_1620255 : CollatzResearch.WordTrace tailWord_1620255 prefixEnd_1620255 369764265711405990471595 := by
  unfold tailWord_1620255
  simp only [CollatzResearch.WordTrace]
  refine ⟨59095554745100327368502219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39397036496733551579001479 59095554745100327368502219)
  ·
    refine ⟨88643332117650491052753329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59095554745100327368502219 88643332117650491052753329)
    ·
      refine ⟨66482499088237868289564997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88643332117650491052753329 66482499088237868289564997)
      ·
        refine ⟨12465468579044600304293437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66482499088237868289564997 12465468579044600304293437)
        ·
          refine ⟨4674550717141725114110039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12465468579044600304293437 4674550717141725114110039)
          ·
            refine ⟨7011826075712587671165059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674550717141725114110039 7011826075712587671165059)
            ·
              refine ⟨10517739113568881506747589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7011826075712587671165059 10517739113568881506747589)
              ·
                refine ⟨1972076083794165282515173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10517739113568881506747589 1972076083794165282515173)
                ·
                  refine ⟨369764265711405990471595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1972076083794165282515173 369764265711405990471595)
                  ·
                    rfl

theorem cell21_1620255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 4].length) (baseStart_1620255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620255 prefixEnd_1620255 := by exact prefixLift 1620255
  have htrace : WordTrace (prefixWord ++ tailWord_1620255) baseStart_1620255 baseEnd_1620255 := by
    simpa [prefixWord, tailWord_1620255, baseEnd_1620255] using wordTrace_append hprefix tailTrace_1620255
  have hstable : (prefixWord ++ tailWord_1620255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620255).length < 2 ^ (prefixWord ++ tailWord_1620255).sum := by decide
  have hdescent : baseEnd_1620255 < baseStart_1620255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620258 : List Nat := [3, 3, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1620258 : Nat := 118140960795 + 1620258 * 2 ^ 59
def prefixEnd_1620258 : Nat := 4983230072969 + 3 ^ 40 * 1620258 * 2
def baseEnd_1620258 : Nat := 369764950352278651921589

theorem tailTrace_1620258 : CollatzResearch.WordTrace tailWord_1620258 prefixEnd_1620258 369764950352278651921589 := by
  unfold tailWord_1620258
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773916041022364720215357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39397109442726305920574285 14773916041022364720215357)
  ·
    refine ⟨5540218515383386770080759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14773916041022364720215357 5540218515383386770080759)
    ·
      refine ⟨8310327773075080155121139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5540218515383386770080759 8310327773075080155121139)
      ·
        refine ⟨12465491659612620232681709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8310327773075080155121139 12465491659612620232681709)
        ·
          refine ⟨4674559372354732587255641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12465491659612620232681709 4674559372354732587255641)
          ·
            refine ⟨3505919529266049440441731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4674559372354732587255641 3505919529266049440441731)
            ·
              refine ⟨5258879293899074160662597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505919529266049440441731 5258879293899074160662597)
              ·
                refine ⟨986039867606076405124237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5258879293899074160662597 986039867606076405124237)
                ·
                  refine ⟨369764950352278651921589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986039867606076405124237 369764950352278651921589)
                  ·
                    rfl

theorem cell21_1620258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1620258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620258 prefixEnd_1620258 := by exact prefixLift 1620258
  have htrace : WordTrace (prefixWord ++ tailWord_1620258) baseStart_1620258 baseEnd_1620258 := by
    simpa [prefixWord, tailWord_1620258, baseEnd_1620258] using wordTrace_append hprefix tailTrace_1620258
  have hstable : (prefixWord ++ tailWord_1620258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620258).length < 2 ^ (prefixWord ++ tailWord_1620258).sum := by decide
  have hdescent : baseEnd_1620258 < baseStart_1620258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620382 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1620382 : Nat := 118140960795 + 1620382 * 2 ^ 59
def prefixEnd_1620382 : Nat := 4983230072969 + 3 ^ 40 * 1620382 * 2
def baseEnd_1620382 : Nat := 369793248841681991854669

theorem tailTrace_1620382 : CollatzResearch.WordTrace tailWord_1620382 prefixEnd_1620382 369793248841681991854669 := by
  unfold tailWord_1620382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7387523351955028507296925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39400124543760152038916933 7387523351955028507296925)
  ·
    refine ⟨2770321256983135690236347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7387523351955028507296925 2770321256983135690236347)
    ·
      refine ⟨4155481885474703535354521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2770321256983135690236347 4155481885474703535354521)
      ·
        refine ⟨3116611414106027651515891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4155481885474703535354521 3116611414106027651515891)
        ·
          refine ⟨4674917121159041477273837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116611414106027651515891 4674917121159041477273837)
          ·
            refine ⟨1753093920434640553977689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4674917121159041477273837 1753093920434640553977689)
            ·
              refine ⟨1314820440325980415483267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753093920434640553977689 1314820440325980415483267)
              ·
                refine ⟨1972230660488970623224901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314820440325980415483267 1972230660488970623224901)
                ·
                  refine ⟨369793248841681991854669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1972230660488970623224901 369793248841681991854669)
                  ·
                    rfl

theorem cell21_1620382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1620382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620382 prefixEnd_1620382 := by exact prefixLift 1620382
  have htrace : WordTrace (prefixWord ++ tailWord_1620382) baseStart_1620382 baseEnd_1620382 := by
    simpa [prefixWord, tailWord_1620382, baseEnd_1620382] using wordTrace_append hprefix tailTrace_1620382
  have hstable : (prefixWord ++ tailWord_1620382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620382).length < 2 ^ (prefixWord ++ tailWord_1620382).sum := by decide
  have hdescent : baseEnd_1620382 < baseStart_1620382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620545 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 5]
def baseStart_1620545 : Nat := 118140960795 + 1620545 * 2 ^ 59
def prefixEnd_1620545 : Nat := 4983230072969 + 3 ^ 40 * 1620545 * 2
def baseEnd_1620545 : Nat := 369830447662429930637669

theorem tailTrace_1620545 : CollatzResearch.WordTrace tailWord_1620545 prefixEnd_1620545 369830447662429930637669 := by
  unfold tailWord_1620545
  simp only [CollatzResearch.WordTrace]
  refine ⟨59106131914049706896559089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39404087942699804597706059 59106131914049706896559089)
  ·
    refine ⟨44329598935537280172419317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59106131914049706896559089 44329598935537280172419317)
    ·
      refine ⟨4155899900206620016164311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44329598935537280172419317 4155899900206620016164311)
      ·
        refine ⟨6233849850309930024246467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4155899900206620016164311 6233849850309930024246467)
        ·
          refine ⟨9350774775464895036369701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6233849850309930024246467 9350774775464895036369701)
          ·
            refine ⟨1753270270399667819319319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9350774775464895036369701 1753270270399667819319319)
            ·
              refine ⟨2629905405599501728978979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753270270399667819319319 2629905405599501728978979)
              ·
                refine ⟨3944858108399252593468469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629905405599501728978979 3944858108399252593468469)
                ·
                  refine ⟨369830447662429930637669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3944858108399252593468469 369830447662429930637669)
                  ·
                    rfl

theorem cell21_1620545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_1620545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620545 prefixEnd_1620545 := by exact prefixLift 1620545
  have htrace : WordTrace (prefixWord ++ tailWord_1620545) baseStart_1620545 baseEnd_1620545 := by
    simpa [prefixWord, tailWord_1620545, baseEnd_1620545] using wordTrace_append hprefix tailTrace_1620545
  have hstable : (prefixWord ++ tailWord_1620545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620545).length < 2 ^ (prefixWord ++ tailWord_1620545).sum := by decide
  have hdescent : baseEnd_1620545 < baseStart_1620545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620548 : List Nat := [2, 3, 5, 1, 1, 1, 2, 6]
def baseStart_1620548 : Nat := 118140960795 + 1620548 * 2 ^ 59
def prefixEnd_1620548 : Nat := 4983230072969 + 3 ^ 40 * 1620548 * 2
def baseEnd_1620548 : Nat := 123277044101100864029221

theorem tailTrace_1620548 : CollatzResearch.WordTrace tailWord_1620548 prefixEnd_1620548 123277044101100864029221 := by
  unfold tailWord_1620548
  simp only [CollatzResearch.WordTrace]
  refine ⟨29553120666519419204459149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39404160888692558939278865 29553120666519419204459149)
  ·
    refine ⟨11082420249944782201672181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29553120666519419204459149 11082420249944782201672181)
    ·
      refine ⟨1038976898432323331406767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11082420249944782201672181 1038976898432323331406767)
      ·
        refine ⟨1558465347648484997110151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038976898432323331406767 1558465347648484997110151)
        ·
          refine ⟨2337698021472727495665227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558465347648484997110151 2337698021472727495665227)
          ·
            refine ⟨3506547032209091243497841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337698021472727495665227 3506547032209091243497841)
            ·
              refine ⟨2629910274156818432623381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3506547032209091243497841 2629910274156818432623381)
              ·
                refine ⟨123277044101100864029221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2629910274156818432623381 123277044101100864029221)
                ·
                  rfl

theorem cell21_1620548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 6].length) (baseStart_1620548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620548 prefixEnd_1620548 := by exact prefixLift 1620548
  have htrace : WordTrace (prefixWord ++ tailWord_1620548) baseStart_1620548 baseEnd_1620548 := by
    simpa [prefixWord, tailWord_1620548, baseEnd_1620548] using wordTrace_append hprefix tailTrace_1620548
  have hstable : (prefixWord ++ tailWord_1620548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620548).length < 2 ^ (prefixWord ++ tailWord_1620548).sum := by decide
  have hdescent : baseEnd_1620548 < baseStart_1620548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
